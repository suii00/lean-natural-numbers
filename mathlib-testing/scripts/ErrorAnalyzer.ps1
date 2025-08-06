# Mathlib Import エラー自動解析・修復システム

param(
    [string]$ErrorLogFile,
    [string]$SolutionDatabase = "mathlib-testing\database\error_solutions.json",
    [switch]$AutoFix
)

# エラーパターンと解決策のデータベース
$errorPatterns = @{
    "object file.*does not exist" = @{
        Type = "MissingDependency"
        Description = "依存関係のオブジェクトファイルが見つからない"
        Solutions = @(
            "lake exe cache get で事前ビルド済みファイルを取得",
            "lake build で依存関係をビルド", 
            "特定モジュールのビルド: lake build ModuleName"
        )
        AutoFix = "lake exe cache get"
    }
    "unknown tactic" = @{
        Type = "TacticNotAvailable"
        Description = "戦術が利用できない"
        Solutions = @(
            "適切なimportを追加",
            "代替戦術を使用",
            "Mathlib.Tacticの完全ビルドが必要"
        )
        AutoFix = $null
    }
    "unknown identifier" = @{
        Type = "IdentifierNotFound"
        Description = "識別子が見つからない"
        Solutions = @(
            "必要なimportを追加",
            "名前空間を確認",
            "スペルチェック"
        )
        AutoFix = $null
    }
    "unexpected token" = @{
        Type = "SyntaxError"
        Description = "構文エラー"
        Solutions = @(
            "Lean 4の正しい構文を使用",
            "括弧やカンマの位置を確認",
            "型注釈を追加"
        )
        AutoFix = $null
    }
    "unsolved goals" = @{
        Type = "ProofIncomplete"
        Description = "証明が未完了"
        Solutions = @(
            "sorry を追加して一時的にスキップ",
            "適切な戦術を使用",
            "証明戦略を見直す"
        )
        AutoFix = $null
    }
}

function Analyze-Error {
    param([string]$ErrorText)
    
    $analysis = @{
        OriginalError = $ErrorText
        ErrorType = "Unknown"
        Description = ""
        Solutions = @()
        AutoFixAvailable = $false
        AutoFixCommand = $null
    }
    
    foreach ($pattern in $errorPatterns.Keys) {
        if ($ErrorText -match $pattern) {
            $solution = $errorPatterns[$pattern]
            $analysis.ErrorType = $solution.Type
            $analysis.Description = $solution.Description
            $analysis.Solutions = $solution.Solutions
            $analysis.AutoFixAvailable = $solution.AutoFix -ne $null
            $analysis.AutoFixCommand = $solution.AutoFix
            break
        }
    }
    
    return $analysis
}

function Generate-Solution-Report {
    param([array]$Errors)
    
    $timestamp = Get-Date -Format "yyyy-MM-dd_HH-mm-ss"
    $reportFile = "mathlib-testing\logs\error_analysis_$timestamp.md"
    
    $report = @"
# Mathlib Import エラー解析レポート

## 📋 解析サマリー

- **解析日時**: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')
- **総エラー数**: $($Errors.Count)
- **自動修復可能**: $(($Errors | Where-Object { $_.AutoFixAvailable }).Count)

---

"@

    $groupedErrors = $Errors | Group-Object ErrorType
    
    foreach ($group in $groupedErrors) {
        $report += @"

## 🔍 $($group.Name) エラー ($($group.Count)件)

"@
        
        foreach ($error in $group.Group) {
            $report += @"

### エラー詳細
- **説明**: $($error.Description)
- **自動修復**: $(if ($error.AutoFixAvailable) { '✅ 可能' } else { '❌ 不可' })

**元のエラー**:
``````
$($error.OriginalError)
``````

**推奨解決策**:
"@
            
            foreach ($solution in $error.Solutions) {
                $report += "`n- $solution"
            }
            
            if ($error.AutoFixAvailable) {
                $report += "`n`n**自動修復コマンド**:"
                $report += "`n``````bash"
                $report += "`n$($error.AutoFixCommand)"
                $report += "`n``````"
            }
            
            $report += "`n`n---"
        }
    }
    
    $report += @"

## 🚀 推奨アクション

### 即座に実行可能
"@

    $autoFixErrors = $Errors | Where-Object { $_.AutoFixAvailable }
    if ($autoFixErrors) {
        $report += "`n"
        foreach ($error in $autoFixErrors) {
            $report += "- ``$($error.AutoFixCommand)``"
        }
    } else {
        $report += "`n- 自動修復可能なエラーはありません"
    }
    
    $report += @"

### 手動対応が必要
"@

    $manualFixErrors = $Errors | Where-Object { -not $_.AutoFixAvailable }
    if ($manualFixErrors) {
        $uniqueTypes = $manualFixErrors | Select-Object -ExpandProperty ErrorType -Unique
        foreach ($type in $uniqueTypes) {
            $report += "`n- $type エラーの解決"
        }
    } else {
        $report += "`n- すべてのエラーが自動修復可能です！"
    }
    
    $report | Out-File -FilePath $reportFile -Encoding UTF8
    
    return $reportFile
}

# メイン処理
if ($ErrorLogFile) {
    Write-Host "🔍 エラー解析開始..." -ForegroundColor Yellow
    
    # エラーログ読み込み
    $logData = Get-Content $ErrorLogFile | ConvertFrom-Json
    $allErrors = @()
    
    foreach ($result in $logData.Results) {
        if (-not $result.Success) {
            foreach ($errorText in $result.Errors) {
                $analysis = Analyze-Error $errorText
                $allErrors += $analysis
            }
        }
    }
    
    Write-Host "📊 解析完了: $($allErrors.Count)個のエラーを分析" -ForegroundColor Green
    
    # レポート生成
    $reportFile = Generate-Solution-Report $allErrors
    Write-Host "📝 解析レポート生成: $reportFile" -ForegroundColor Green
    
    # 自動修復実行
    if ($AutoFix) {
        Write-Host "`n🔧 自動修復実行..." -ForegroundColor Blue
        
        $autoFixCommands = $allErrors | Where-Object { $_.AutoFixAvailable } | 
                          Select-Object -ExpandProperty AutoFixCommand -Unique
        
        foreach ($command in $autoFixCommands) {
            Write-Host "実行: $command" -ForegroundColor Yellow
            try {
                Invoke-Expression $command
                Write-Host "✅ 実行完了" -ForegroundColor Green
            } catch {
                Write-Host "❌ 実行失敗: $_" -ForegroundColor Red
            }
        }
    }
    
    # 解決策データベース更新
    $database = @{}
    if (Test-Path $SolutionDatabase) {
        $database = Get-Content $SolutionDatabase | ConvertFrom-Json -AsHashtable
    }
    
    if (-not $database.ContainsKey("ErrorAnalyses")) {
        $database["ErrorAnalyses"] = @()
    }
    
    $analysisRecord = @{
        Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        TotalErrors = $allErrors.Count
        ErrorTypes = ($allErrors | Group-Object ErrorType | ForEach-Object { @{Type = $_.Name; Count = $_.Count} })
        AutoFixCount = ($allErrors | Where-Object { $_.AutoFixAvailable }).Count
    }
    
    $database["ErrorAnalyses"] += $analysisRecord
    $database | ConvertTo-Json -Depth 10 | Out-File -FilePath $SolutionDatabase -Encoding UTF8
    
    Write-Host "💾 解決策データベース更新完了" -ForegroundColor Green
    
} else {
    Write-Host "❌ エラーログファイルが指定されていません" -ForegroundColor Red
    Write-Host "使用方法: .\ErrorAnalyzer.ps1 -ErrorLogFile 'path\to\logfile.json' [-AutoFix]"
}