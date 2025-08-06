# Mathlib Import統合テストシステム
# 段階的import → エラー解析 → 自動修復 → 結果記録

param(
    [switch]$AutoFix,
    [switch]$Verbose,
    [switch]$SkipDependencyBuild
)

Write-Host @"
🧪 Mathlib Import統合テストシステム
=====================================
段階的importテスト + エラー解析 + 自動修復

"@ -ForegroundColor Cyan

$timestamp = Get-Date -Format "yyyy-MM-dd_HH-mm-ss"

# ステップ1: 必要に応じて依存関係ビルド
if (-not $SkipDependencyBuild) {
    Write-Host "🔧 ステップ1: 依存関係の確認とビルド" -ForegroundColor Yellow
    
    Write-Host "キャッシュからの取得を試行中..." -ForegroundColor Gray
    try {
        $cacheOutput = & lake exe cache get 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✅ キャッシュ取得完了" -ForegroundColor Green
        } else {
            Write-Host "⚠️ キャッシュ取得失敗、手動ビルドが必要" -ForegroundColor Yellow
        }
    } catch {
        Write-Host "⚠️ キャッシュ取得エラー: $_" -ForegroundColor Yellow
    }
}

# ステップ2: 段階的importテスト実行
Write-Host "`n🧪 ステップ2: 段階的Importテスト実行" -ForegroundColor Yellow

$testParams = @()
if ($Verbose) { $testParams += "-Verbose" }

$testResult = & "mathlib-testing\scripts\MathLibImportTester.ps1" @testParams
$latestLogFile = Get-ChildItem "mathlib-testing\logs\import_test_*.json" | Sort-Object LastWriteTime -Descending | Select-Object -First 1

if ($latestLogFile) {
    Write-Host "✅ テスト完了、ログファイル: $($latestLogFile.Name)" -ForegroundColor Green
    
    # ログデータ読み込み
    $logData = Get-Content $latestLogFile.FullName | ConvertFrom-Json
    $failedTests = $logData.Results | Where-Object { -not $_.Success }
    
    if ($failedTests) {
        Write-Host "`n🔍 ステップ3: エラー解析開始" -ForegroundColor Yellow
        Write-Host "失敗テスト数: $($failedTests.Count)" -ForegroundColor Red
        
        # エラー解析実行
        $analyzerParams = @{
            ErrorLogFile = $latestLogFile.FullName
        }
        if ($AutoFix) { $analyzerParams.AutoFix = $true }
        
        & "mathlib-testing\scripts\ErrorAnalyzer.ps1" @analyzerParams
        
        # 自動修復後の再テスト
        if ($AutoFix) {
            Write-Host "`n🔄 ステップ4: 修復後の再テスト" -ForegroundColor Yellow
            
            Start-Sleep -Seconds 2  # ビルド完了待ち
            & "mathlib-testing\scripts\MathLibImportTester.ps1" @testParams
            
            $retestLogFile = Get-ChildItem "mathlib-testing\logs\import_test_*.json" | Sort-Object LastWriteTime -Descending | Select-Object -First 1
            $retestData = Get-Content $retestLogFile.FullName | ConvertFrom-Json
            
            Write-Host "`n📊 修復効果:" -ForegroundColor Cyan
            Write-Host "修復前成功率: $(($logData.TestSession.SuccessRate * 100).ToString('F1'))%" -ForegroundColor Gray
            Write-Host "修復後成功率: $(($retestData.TestSession.SuccessRate * 100).ToString('F1'))%" -ForegroundColor Green
        }
    } else {
        Write-Host "✅ すべてのテストが成功しました！" -ForegroundColor Green
    }
    
} else {
    Write-Host "❌ テストログファイルが見つかりません" -ForegroundColor Red
    exit 1
}

# ステップ5: 総合レポート生成
Write-Host "`n📋 ステップ5: 総合レポート生成" -ForegroundColor Yellow

$summaryFile = "mathlib-testing\logs\test_summary_$timestamp.md"
$summary = @"
# Mathlib Import統合テストサマリー

## 📋 実行情報
- **実行日時**: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')
- **自動修復**: $(if ($AutoFix) { '✅ 有効' } else { '❌ 無効' })
- **詳細出力**: $(if ($Verbose) { '✅ 有効' } else { '❌ 無効' })

## 📊 最終結果
"@

# 最新結果の取得
$latestResults = Get-ChildItem "mathlib-testing\logs\import_test_*.json" | Sort-Object LastWriteTime -Descending | Select-Object -First 1
if ($latestResults) {
    $finalData = Get-Content $latestResults.FullName | ConvertFrom-Json
    $summary += @"

- **総テスト数**: $($finalData.TestSession.TotalTests)
- **成功数**: $($finalData.TestSession.SuccessCount)  
- **成功率**: $(($finalData.TestSession.SuccessRate * 100).ToString('F1'))%
- **最高到達レベル**: $(($finalData.Results | Where-Object { $_.Success } | Select-Object -Last 1).Level)

## 🎯 推奨次ステップ

"@

    if ($finalData.TestSession.SuccessRate -eq 1.0) {
        $summary += "✅ **完全成功**: すべてのMathlibインポートが動作しています！"
        $summary += "`n- square_even.leanとsqrt2_indep.leanの改善が可能です"
        $summary += "`n- 高度な数学証明の実装に進むことができます"
    } elseif ($finalData.TestSession.SuccessRate -ge 0.6) {
        $summary += "⚠️ **部分成功**: 基本機能は動作していますが、改善余地があります"
        $summary += "`n- 失敗したレベルの詳細調査が必要です"
        $summary += "`n- lake build で追加依存関係のビルドを検討してください"
    } else {
        $summary += "❌ **要改善**: 基本的なMathlibインポートに問題があります"
        $summary += "`n- lake exe cache get の実行を強く推奨します"
        $summary += "`n- 環境設定の見直しが必要かもしれません"
    }
}

$summary += @"

## 📁 生成ファイル

- 段階的テストログ: $($latestLogFile.Name)
- エラー解析レポート: error_analysis_*.md  
- 成功パターンDB: database\success_patterns.json
- エラー解決DB: database\error_solutions.json

---

*このレポートは Mathlib Import統合テストシステム によって自動生成されました*
"@

$summary | Out-File -FilePath $summaryFile -Encoding UTF8

Write-Host "📝 総合レポート生成完了: $summaryFile" -ForegroundColor Green

# 最終メッセージ
Write-Host "`n🎯 テスト完了!" -ForegroundColor Green
Write-Host "詳細は生成されたレポートファイルを確認してください。" -ForegroundColor Gray

# 簡易サマリー表示
if ($latestLogFile) {
    $data = Get-Content $latestLogFile.FullName | ConvertFrom-Json
    Write-Host "`n📈 最終結果: $($data.TestSession.SuccessCount)/$($data.TestSession.TotalTests) 成功 ($(($data.TestSession.SuccessRate * 100).ToString('F1'))%)" -ForegroundColor Cyan
}