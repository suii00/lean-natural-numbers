# Mathlib一括変換システム
# プロジェクト内の全Lean証明ファイルを自動変換

param(
    [string]$ProjectPath = ".",
    [string]$OutputDir = "mathlib-converted",
    [switch]$DryRun,
    [switch]$Verbose,
    [string[]]$ExcludePatterns = @("*.lean.backup", "*/.lake/*", "*/mathlib-testing/*")
)

# 設定
$timestamp = Get-Date -Format "yyyy-MM-dd_HH-mm-ss"
$logFile = "mathlib-conversion\batch_conversion_$timestamp.json"
$reportFile = "mathlib-conversion\batch_report_$timestamp.md"

Write-Host "🔄 Mathlib一括変換システム" -ForegroundColor Green
Write-Host "プロジェクトパス: $ProjectPath" -ForegroundColor Gray
Write-Host "出力ディレクトリ: $OutputDir" -ForegroundColor Gray

# 変換対象ファイル検索
Write-Host "`n📁 変換対象ファイル検索中..." -ForegroundColor Yellow

$allLeanFiles = Get-ChildItem -Path $ProjectPath -Recurse -Filter "*.lean" | Where-Object {
    $file = $_
    $shouldExclude = $false
    
    foreach ($pattern in $ExcludePatterns) {
        if ($file.FullName -like "*$pattern*") {
            $shouldExclude = $true
            break
        }
    }
    
    -not $shouldExclude
}

Write-Host "発見されたファイル: $($allLeanFiles.Count)個" -ForegroundColor Green

# ファイル分類
$conversionTargets = @()
foreach ($file in $allLeanFiles) {
    # ファイル内容分析
    $content = Get-Content $file.FullName -Encoding UTF8
    $hasProofs = $content | Where-Object { $_ -match "theorem|lemma|def.*:.*:=" }
    $hasImports = $content | Where-Object { $_ -match "^import" }
    $needsConversion = $content | Where-Object { $_ -match "Nat\.|Int\.|exact ⟨|omega|ring" }
    
    $analysisResult = @{
        FilePath = $file.FullName
        RelativePath = $file.FullName.Replace((Get-Location).Path + "\", "")
        HasProofs = $hasProofs.Count -gt 0
        HasImports = $hasImports.Count -gt 0  
        NeedsConversion = $needsConversion.Count -gt 0
        LineCount = $content.Count
        Size = $file.Length
    }
    
    if ($analysisResult.HasProofs -or $analysisResult.NeedsConversion) {
        $conversionTargets += $analysisResult
    }
}

Write-Host "変換対象: $($conversionTargets.Count)ファイル" -ForegroundColor Cyan

if ($conversionTargets.Count -eq 0) {
    Write-Host "変換対象ファイルが見つかりませんでした。" -ForegroundColor Yellow
    exit 0
}

# 出力ディレクトリ作成
if (-not $DryRun) {
    New-Item -ItemType Directory -Path $OutputDir -Force | Out-Null
}

# 変換結果記録
$conversionResults = @()

# 各ファイルを変換
foreach ($target in $conversionTargets) {
    Write-Host "`n🔄 変換中: $($target.RelativePath)" -ForegroundColor Yellow
    
    $startTime = Get-Date
    
    try {
        # 出力パス決定
        $relativePath = $target.RelativePath
        $outputPath = Join-Path $OutputDir $relativePath
        $outputDir = Split-Path $outputPath -Parent
        
        if (-not $DryRun) {
            New-Item -ItemType Directory -Path $outputDir -Force | Out-Null
        }
        
        # MathLibConverterを呼び出し
        $converterParams = @{
            InputFile = $target.FilePath
            OutputFile = $outputPath
            Verbose = $Verbose
            DryRun = $DryRun
        }
        
        if ($DryRun) {
            Write-Host "  DryRun: 変換処理をシミュレート" -ForegroundColor Gray
            $success = $true
            $errors = @()
        } else {
            # 実際の変換実行
            $output = & "mathlib-conversion\MathLibConverter.ps1" @converterParams 2>&1
            $success = $LASTEXITCODE -eq 0
            $errors = if ($success) { @() } else { @($output -join "`n") }
        }
        
        $duration = (Get-Date) - $startTime
        
        # 結果記録
        $result = @{
            SourceFile = $target.RelativePath
            OutputFile = $relativePath
            Success = $success
            Duration = $duration.TotalSeconds
            OriginalLines = $target.LineCount
            Errors = $errors
            Timestamp = $startTime.ToString("yyyy-MM-dd HH:mm:ss")
            HasProofs = $target.HasProofs
            HasImports = $target.HasImports
            NeedsConversion = $target.NeedsConversion
        }
        
        $conversionResults += $result
        
        if ($success) {
            Write-Host "  ✅ 変換成功 ($($duration.TotalSeconds.ToString('F1'))s)" -ForegroundColor Green
        } else {
            Write-Host "  ❌ 変換失敗" -ForegroundColor Red
            if ($Verbose) {
                $errors | ForEach-Object { Write-Host "    $_" -ForegroundColor Red }
            }
        }
        
    } catch {
        Write-Host "  ❌ 変換エラー: $_" -ForegroundColor Red
        $conversionResults += @{
            SourceFile = $target.RelativePath
            Success = $false
            Duration = 0
            Errors = @($_.Exception.Message)
            Timestamp = $startTime.ToString("yyyy-MM-dd HH:mm:ss")
        }
    }
}

# 結果集計
$successCount = ($conversionResults | Where-Object { $_.Success }).Count
$totalCount = $conversionResults.Count
$totalDuration = ($conversionResults | Measure-Object -Property Duration -Sum).Sum

Write-Host "`n📊 変換結果サマリー" -ForegroundColor Cyan
Write-Host "成功: $successCount / $totalCount ファイル" -ForegroundColor Green
Write-Host "成功率: $(($successCount / $totalCount * 100).ToString('F1'))%" -ForegroundColor Green
Write-Host "総実行時間: $($totalDuration.ToString('F1'))秒" -ForegroundColor Gray

# JSON結果保存
if (-not $DryRun) {
    $resultData = @{
        ConversionSession = @{
            Timestamp = $timestamp
            ProjectPath = $ProjectPath
            OutputDir = $OutputDir
            TotalFiles = $totalCount
            SuccessCount = $successCount
            SuccessRate = $successCount / $totalCount
            TotalDuration = $totalDuration
        }
        Results = $conversionResults
    }
    
    $resultData | ConvertTo-Json -Depth 10 | Out-File -FilePath $logFile -Encoding UTF8
    Write-Host "📁 詳細ログ: $logFile" -ForegroundColor Gray
}

# Markdownレポート生成
$markdownReport = @"
# Mathlib一括変換レポート

## 📋 変換セッション情報

- **実行日時**: $timestamp
- **プロジェクトパス**: $ProjectPath
- **出力ディレクトリ**: $OutputDir
- **総ファイル数**: $totalCount
- **成功数**: $successCount
- **成功率**: $(($successCount / $totalCount * 100).ToString('F1'))%
- **総実行時間**: $($totalDuration.ToString('F1'))秒

---

## 📊 ファイル別変換結果

"@

foreach ($result in $conversionResults) {
    $status = if ($result.Success) { "✅ 成功" } else { "❌ 失敗" }
    $markdownReport += @"

### $($result.SourceFile) - $status

- **実行時間**: $($result.Duration.ToString('F2'))秒
- **元ファイル行数**: $($result.OriginalLines)
- **証明含む**: $(if ($result.HasProofs) { "あり" } else { "なし" })
- **Import文**: $(if ($result.HasImports) { "あり" } else { "なし" })
- **変換必要**: $(if ($result.NeedsConversion) { "あり" } else { "なし" })

"@
    
    if (-not $result.Success -and $result.Errors) {
        $markdownReport += "**エラー詳細**:`n"
        foreach ($error in $result.Errors) {
            $markdownReport += "``````"
            $markdownReport += "`n$error"
            $markdownReport += "`n``````"
        }
    }
}

$markdownReport += @"

---

## 🎯 推奨事項

"@

if ($successCount -eq $totalCount) {
    $markdownReport += "- ✅ 全ファイルの変換が成功しました！"
    $markdownReport += "`n- 変換されたファイルをテストして動作確認してください"
    $markdownReport += "`n- 必要に応じて元ファイルを置換してください"
} elseif ($successCount -gt 0) {
    $failedCount = $totalCount - $successCount
    $markdownReport += "- ⚠️ $failedCount ファイルの変換に失敗しました"
    $markdownReport += "`n- 失敗ファイルのエラーを確認して手動修正を検討してください"
    $markdownReport += "`n- 成功したファイルから変換パターンを学習して改善できます"
} else {
    $markdownReport += "- ❌ すべてのファイルの変換に失敗しました"
    $markdownReport += "`n- 変換ルールの見直しが必要です"
    $markdownReport += "`n- 個別ファイルでの動作確認から開始してください"
}

if (-not $DryRun) {
    $markdownReport | Out-File -FilePath $reportFile -Encoding UTF8
    Write-Host "📄 変換レポート: $reportFile" -ForegroundColor Gray
}

Write-Host "`n🎯 一括変換完了!" -ForegroundColor Green