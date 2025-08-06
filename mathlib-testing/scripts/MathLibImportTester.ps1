# Mathlib Import段階的テストシステム
# 各importレベルでのコンパイルエラーを記録・解決

param(
    [string]$LogDirectory = "mathlib-testing\logs",
    [string]$DatabaseFile = "mathlib-testing\database\success_patterns.json",
    [switch]$Verbose
)

# 設定
$timestamp = Get-Date -Format "yyyy-MM-dd_HH-mm-ss"
$logFile = "$LogDirectory\import_test_$timestamp.json"
$reportFile = "$LogDirectory\import_report_$timestamp.md"

# テスト段階定義
$testLevels = @(
    @{
        Name = "Level0_Basic"
        Description = "基本的なLeanコンパイル確認"
        Imports = @()
        TestCode = @"
-- 基本レベル: import なし
theorem basic_test : 1 + 1 = 2 := by rfl
def hello_world : String := "Hello, Mathlib Testing!"
"@
    },
    @{
        Name = "Level1_Tactic_Basic"  
        Description = "基本戦術のみ"
        Imports = @("Mathlib.Tactic.Basic")
        TestCode = @"
-- レベル1: 基本戦術
import Mathlib.Tactic.Basic

theorem test_trivial : True := by trivial
theorem test_rfl : 2 + 2 = 4 := by rfl
"@
    },
    @{
        Name = "Level2_Tactic_Extended"
        Description = "拡張戦術"
        Imports = @("Mathlib.Tactic.Basic", "Mathlib.Tactic.Ring")
        TestCode = @"
-- レベル2: Ring戦術追加
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ring

theorem test_ring (a b : ℕ) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by ring
"@
    },
    @{
        Name = "Level3_Nat_Basic"
        Description = "自然数基本機能"
        Imports = @("Mathlib.Tactic.Basic", "Mathlib.Data.Nat.Basic")
        TestCode = @"
-- レベル3: 自然数基本
import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Basic

theorem test_nat : ∀ n : ℕ, n + 0 = n := by intro; rfl
example : Even 4 := by use 2; rfl
"@
    },
    @{
        Name = "Level4_Nat_Extended"
        Description = "自然数拡張機能"
        Imports = @("Mathlib.Tactic.Basic", "Mathlib.Data.Nat.Basic", "Mathlib.Data.Nat.Parity")
        TestCode = @"
-- レベル4: 自然数拡張
import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity

theorem test_parity (n : ℕ) : Even n ∨ Odd n := Nat.even_or_odd n
"@
    },
    @{
        Name = "Level5_Full_Tactic"
        Description = "フル戦術セット"
        Imports = @("Mathlib.Tactic")
        TestCode = @"
-- レベル5: フル戦術
import Mathlib.Tactic

theorem test_omega (n : ℕ) : n + 0 = n := by omega
theorem test_norm_num : 2^10 = 1024 := by norm_num
theorem test_use_tactic : ∃ x : ℕ, x > 5 := by use 10; norm_num
"@
    }
)

# ログ初期化
$testResults = @()

Write-Host "🚀 Mathlib Import段階的テスト開始" -ForegroundColor Green
Write-Host "タイムスタンプ: $timestamp" -ForegroundColor Gray
Write-Host "ログファイル: $logFile" -ForegroundColor Gray

# 各レベルのテスト実行
foreach ($level in $testLevels) {
    Write-Host "`n📋 テスト実行: $($level.Name)" -ForegroundColor Yellow
    Write-Host "説明: $($level.Description)" -ForegroundColor Gray
    
    # テストファイル作成
    $testFileName = "mathlib-testing\tests\$($level.Name).lean"
    $level.TestCode | Out-File -FilePath $testFileName -Encoding UTF8
    
    # コンパイル実行
    $startTime = Get-Date
    try {
        $output = & lake env lean $testFileName 2>&1
        $exitCode = $LASTEXITCODE
        $endTime = Get-Date
        $duration = ($endTime - $startTime).TotalSeconds
        
        $success = $exitCode -eq 0
        
        if ($success) {
            Write-Host "✅ 成功" -ForegroundColor Green
        } else {
            Write-Host "❌ エラー" -ForegroundColor Red
        }
        
        # 結果記録
        $result = @{
            Level = $level.Name
            Description = $level.Description
            Imports = $level.Imports
            Success = $success
            ExitCode = $exitCode
            Output = $output -join "`n"
            Duration = $duration
            Timestamp = $startTime.ToString("yyyy-MM-dd HH:mm:ss")
            ErrorCount = 0
            Errors = @()
        }
        
        # エラー解析
        if (-not $success) {
            $errorLines = $output | Where-Object { $_ -match "error:" }
            $result.ErrorCount = $errorLines.Count
            $result.Errors = $errorLines
            
            Write-Host "エラー数: $($result.ErrorCount)" -ForegroundColor Red
            if ($Verbose) {
                foreach ($error in $errorLines) {
                    Write-Host "  - $error" -ForegroundColor Red
                }
            }
        }
        
        $testResults += $result
        
    } catch {
        Write-Host "❌ 実行エラー: $_" -ForegroundColor Red
        $testResults += @{
            Level = $level.Name
            Description = $level.Description
            Success = $false
            ExitCode = -1
            Output = $_.Exception.Message
            Duration = 0
            Timestamp = $startTime.ToString("yyyy-MM-dd HH:mm:ss")
            ErrorCount = 1
            Errors = @($_.Exception.Message)
        }
    }
}

# 結果集計
$successCount = ($testResults | Where-Object { $_.Success }).Count
$totalCount = $testResults.Count

Write-Host "`n📊 テスト結果サマリー" -ForegroundColor Cyan
Write-Host "成功: $successCount / $totalCount" -ForegroundColor Green
Write-Host "成功率: $(($successCount / $totalCount * 100).ToString('F1'))%" -ForegroundColor Green

# JSON結果保存
$resultData = @{
    TestSession = @{
        Timestamp = $timestamp
        TotalTests = $totalCount
        SuccessCount = $successCount
        SuccessRate = $successCount / $totalCount
    }
    Results = $testResults
}

$resultData | ConvertTo-Json -Depth 10 | Out-File -FilePath $logFile -Encoding UTF8

# Markdownレポート生成
$markdownReport = @"
# Mathlib Import段階的テスト結果

## 📋 テストセッション情報

- **実行日時**: $timestamp
- **総テスト数**: $totalCount
- **成功数**: $successCount  
- **成功率**: $(($successCount / $totalCount * 100).ToString('F1'))%

---

## 📊 レベル別結果

"@

foreach ($result in $testResults) {
    $status = if ($result.Success) { "✅ 成功" } else { "❌ 失敗" }
    $markdownReport += @"

### $($result.Level) - $status

- **説明**: $($result.Description)
- **Import数**: $($result.Imports.Count)
- **実行時間**: $($result.Duration.ToString('F2'))秒
- **エラー数**: $($result.ErrorCount)

**Import一覧**:
"@
    
    foreach ($import in $result.Imports) {
        $markdownReport += "`n- ``$import``"
    }
    
    if (-not $result.Success) {
        $markdownReport += "`n`n**エラー詳細**:"
        foreach ($error in $result.Errors) {
            $markdownReport += "`n``````"
            $markdownReport += "`n$error"
            $markdownReport += "`n``````"
        }
    }
}

$markdownReport += @"

---

## 🔍 推奨事項

"@

if ($successCount -eq 0) {
    $markdownReport += "- すべてのテストが失敗しました。Mathlibの基本設定を確認してください。"
} elseif ($successCount -eq $totalCount) {
    $markdownReport += "- すべてのテストが成功しました！Mathlibが正常に動作しています。"
} else {
    $lastSuccessLevel = ($testResults | Where-Object { $_.Success })[-1].Level
    $markdownReport += "- 最後に成功したレベル: $lastSuccessLevel"
    $markdownReport += "`n- 段階的にimportを増やして問題を特定してください。"
}

$markdownReport | Out-File -FilePath $reportFile -Encoding UTF8

Write-Host "`n📁 生成ファイル:" -ForegroundColor Cyan
Write-Host "- JSONログ: $logFile" -ForegroundColor Gray
Write-Host "- Markdownレポート: $reportFile" -ForegroundColor Gray

# 成功パターンをデータベースに追加
$successfulResults = $testResults | Where-Object { $_.Success }
if ($successfulResults) {
    Write-Host "`n💾 成功パターンをデータベースに記録中..." -ForegroundColor Blue
    
    # 既存データベース読み込み
    $database = @{}
    if (Test-Path $DatabaseFile) {
        $database = Get-Content $DatabaseFile | ConvertFrom-Json -AsHashtable
    }
    
    if (-not $database.ContainsKey("SuccessfulImports")) {
        $database["SuccessfulImports"] = @()
    }
    
    foreach ($success in $successfulResults) {
        $pattern = @{
            Level = $success.Level
            Imports = $success.Imports
            TestTimestamp = $timestamp
            Duration = $success.Duration
        }
        $database["SuccessfulImports"] += $pattern
    }
    
    # データベース保存
    $database | ConvertTo-Json -Depth 10 | Out-File -FilePath $DatabaseFile -Encoding UTF8
    Write-Host "✅ データベース更新完了" -ForegroundColor Green
}

Write-Host "`n🎯 テスト完了!" -ForegroundColor Green