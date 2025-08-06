# 対話的Import探索システム
# ユーザーとの対話でimport文を段階的に発見・学習

param(
    [string]$Goal = "",
    [switch]$LearningMode,
    [string]$DatabasePath = "import-learning\import_database.json"
)

# よく使われるMathlib importの階層構造
$mathlibModules = @{
    "Tactic" = @{
        Description = "証明戦術"
        Modules = @(
            "Mathlib.Tactic.Basic",
            "Mathlib.Tactic.Ring", 
            "Mathlib.Tactic.Omega",
            "Mathlib.Tactic.Use",
            "Mathlib.Tactic.Simp",
            "Mathlib.Tactic.Rw"
        )
    }
    "Data" = @{
        Description = "データ型と構造"
        Modules = @(
            "Mathlib.Data.Nat.Basic",
            "Mathlib.Data.Int.Basic",
            "Mathlib.Data.Real.Basic",
            "Mathlib.Data.Nat.Parity",
            "Mathlib.Data.Rat.Basic"
        )
    }
    "Init" = @{
        Description = "基本初期化"
        Modules = @(
            "Mathlib.Init.Logic",
            "Mathlib.Init.Data.Nat",
            "Mathlib.Init.Function"
        )
    }
    "Algebra" = @{
        Description = "代数構造"
        Modules = @(
            "Mathlib.Algebra.Ring.Basic",
            "Mathlib.Algebra.Field.Basic",
            "Mathlib.Algebra.Group.Basic"
        )
    }
}

function Show-MainMenu {
    Write-Host @"
🔍 対話的Import探索システム

何をしたいですか？
1. 特定の定理・戦術を使いたい
2. 数学分野別のimportを探す
3. エラーメッセージからimportを特定
4. 成功したimportパターンを参照
5. 新しいimportを試行・学習
6. 学習データベース分析
7. 終了

"@ -ForegroundColor Cyan
}

function Search-TheoremInDatabase {
    param([string]$TheoremName, [hashtable]$Database)
    
    # 定理マッピングから検索
    $mappings = $Database.TheoremMapping | Where-Object { 
        $_.OldName -like "*$TheoremName*" -or $_.NewName -like "*$TheoremName*" 
    }
    
    if ($mappings) {
        Write-Host "📖 定理マッピングが見つかりました:" -ForegroundColor Green
        $mappings | ForEach-Object {
            Write-Host "  $($_.OldName) → $($_.NewName)" -ForegroundColor White
            Write-Host "  必要Import: $($_.ImportRequired)" -ForegroundColor Gray
            Write-Host "  使用回数: $($_.UsageCount)" -ForegroundColor Gray
            Write-Host ""
        }
        return $mappings
    }
    
    # 成功パターンから検索
    $successfulImports = $Database.SuccessfulPatterns | Where-Object {
        $_.TestCode -like "*$TheoremName*"
    }
    
    if ($successfulImports) {
        Write-Host "✅ 関連する成功パターン:" -ForegroundColor Green
        $successfulImports | ForEach-Object {
            Write-Host "  Import: $($_.ImportStatement)" -ForegroundColor White
            Write-Host "  テスト: $($_.TestCode -replace "`n", " ")" -ForegroundColor Gray
            Write-Host ""
        }
        return $successfulImports
    }
    
    Write-Host "❌ '$TheoremName' に関する情報が見つかりませんでした" -ForegroundColor Red
    return $null
}

function Suggest-ImportsForField {
    param([string]$Field)
    
    $suggestions = switch ($Field.ToLower()) {
        "自然数" { $mathlibModules["Data"].Modules | Where-Object { $_ -match "Nat" } }
        "整数" { $mathlibModules["Data"].Modules | Where-Object { $_ -match "Int" } }
        "実数" { $mathlibModules["Data"].Modules | Where-Object { $_ -match "Real" } }
        "有理数" { $mathlibModules["Data"].Modules | Where-Object { $_ -match "Rat" } }
        "代数" { $mathlibModules["Algebra"].Modules }
        "戦術" { $mathlibModules["Tactic"].Modules }
        "証明" { @("Mathlib.Tactic.Basic", "Mathlib.Init.Logic") }
        default { @("Mathlib.Tactic.Basic", "Mathlib.Data.Nat.Basic") }
    }
    
    Write-Host "💡 '$Field' 分野の推奨Import:" -ForegroundColor Yellow
    $suggestions | ForEach-Object {
        Write-Host "  $_" -ForegroundColor White
    }
    
    return $suggestions
}

function Analyze-ErrorMessage {
    param([string]$ErrorMessage)
    
    $suggestions = @()
    
    if ($ErrorMessage -match "object file.*of module ([^\s]+)") {
        $missingModule = $matches[1]
        Write-Host "🔍 不足モジュール検出: $missingModule" -ForegroundColor Yellow
        
        # モジュール名から推測されるimport
        $possibleImports = @(
            "import $missingModule",
            "import Mathlib.$missingModule"
        )
        
        $suggestions += $possibleImports
    }
    
    if ($ErrorMessage -match "unknown identifier '([^']+)'") {
        $unknownId = $matches[1]
        Write-Host "🔍 未知の識別子: $unknownId" -ForegroundColor Yellow
        
        # よくある識別子のマッピング
        $identifierMappings = @{
            "Even" = @("Mathlib.Data.Nat.Parity")
            "Odd" = @("Mathlib.Data.Nat.Parity")
            "add_zero" = @("Mathlib.Data.Nat.Basic", "Mathlib.Data.Int.Basic")
            "zero_add" = @("Mathlib.Data.Nat.Basic", "Mathlib.Data.Int.Basic")
            "ring" = @("Mathlib.Tactic.Ring")
            "omega" = @("Mathlib.Tactic.Omega")
        }
        
        if ($identifierMappings.ContainsKey($unknownId)) {
            $suggestions += $identifierMappings[$unknownId]
        }
    }
    
    if ($ErrorMessage -match "unknown tactic '([^']+)'") {
        $unknownTactic = $matches[1]
        Write-Host "🔍 未知の戦術: $unknownTactic" -ForegroundColor Yellow
        
        $tacticMappings = @{
            "ring" = @("Mathlib.Tactic.Ring")
            "omega" = @("Mathlib.Tactic.Omega")  
            "use" = @("Mathlib.Tactic.Use")
            "simp" = @("Mathlib.Tactic.Simp")
            "rw" = @("Mathlib.Tactic.Rw")
            "norm_num" = @("Mathlib.Tactic.NormNum")
        }
        
        if ($tacticMappings.ContainsKey($unknownTactic)) {
            $suggestions += $tacticMappings[$unknownTactic]
        }
    }
    
    if ($suggestions.Count -gt 0) {
        Write-Host "💡 推奨Import:" -ForegroundColor Green
        $suggestions | Select-Object -Unique | ForEach-Object {
            Write-Host "  $_" -ForegroundColor White
        }
    } else {
        Write-Host "❓ 自動提案できませんでした。手動でimportを調査してください。" -ForegroundColor Yellow
    }
    
    return $suggestions
}

function Interactive-ImportTester {
    param([hashtable]$Database)
    
    Write-Host "🧪 対話的Import テスター" -ForegroundColor Green
    Write-Host "試したいimport文を入力してください (空行で終了):"
    
    $imports = @()
    
    do {
        $input = Read-Host "Import"
        if ($input) {
            $imports += $input
            Write-Host "  追加: $input" -ForegroundColor Gray
        }
    } while ($input)
    
    if ($imports.Count -eq 0) {
        Write-Host "Importが入力されませんでした" -ForegroundColor Yellow
        return
    }
    
    Write-Host "`nテストコードを入力してください (空行で終了、省略可):"
    $testLines = @()
    
    do {
        $input = Read-Host "Code"
        if ($input) {
            $testLines += $input
        }
    } while ($input)
    
    $testCode = $testLines -join "`n"
    
    # 学習システムでテスト実行
    Write-Host "`n🔄 テスト実行中..." -ForegroundColor Yellow
    
    # ImportLearningSystemを呼び出し
    $learningSystem = "import-learning\ImportLearningSystem.ps1"
    
    foreach ($import in $imports) {
        $result = Test-ImportStatement $import $testCode
        Record-ImportAttempt $Database $result
        
        if ($result.Success) {
            Write-Host "✅ 成功: $import" -ForegroundColor Green
        } else {
            Write-Host "❌ 失敗: $import" -ForegroundColor Red
            Write-Host "エラー:" -ForegroundColor Red
            $result.Errors | ForEach-Object { Write-Host "  $_" -ForegroundColor Red }
            
            # 自動修正提案
            $suggestions = Analyze-ErrorMessage ($result.Errors -join "`n")
            if ($suggestions) {
                Write-Host "これらのimportを追加で試してみてください:" -ForegroundColor Cyan
                $suggestions | ForEach-Object { Write-Host "  $_" -ForegroundColor White }
            }
        }
    }
}

function Show-DatabaseStats {
    param([hashtable]$Database)
    
    Write-Host @"
📊 学習データベース統計

基本情報:
- 総試行数: $($Database.Metadata.TotalAttempts)
- 成功率: $(($Database.Metadata.SuccessRate * 100).ToString('F1'))%
- セッション数: $($Database.Metadata.TotalSessions)
- 最終更新: $($Database.Metadata.LastUpdated)

パターン数:
- 成功パターン: $($Database.SuccessfulPatterns.Count)
- エラーパターン: $($Database.ErrorPatterns.Count)  
- 定理マッピング: $($Database.TheoremMapping.Count)
- 自動修正提案: $($Database.AutoFixSuggestions.Count)

"@ -ForegroundColor Cyan

    if ($Database.SuccessfulPatterns.Count -gt 0) {
        Write-Host "最も成功回数が多いImport:" -ForegroundColor Green
        $Database.SuccessfulPatterns | 
            Sort-Object SuccessCount -Descending | 
            Select-Object -First 5 | 
            ForEach-Object {
                Write-Host "  $($_.ImportStatement) (成功: $($_.SuccessCount)回)" -ForegroundColor White
            }
    }
    
    if ($Database.ErrorPatterns.Count -gt 0) {
        Write-Host "`n最も頻発するエラー:" -ForegroundColor Red
        $Database.ErrorPatterns | 
            Group-Object ErrorType | 
            Sort-Object Count -Descending |
            Select-Object -First 3 | 
            ForEach-Object {
                Write-Host "  $($_.Name): $($_.Count)件" -ForegroundColor White
            }
    }
}

# メイン対話ループ
function Start-InteractiveSession {
    Write-Host "🚀 対話的Import探索システム開始" -ForegroundColor Green
    
    # データベース読み込み
    $database = if (Test-Path $DatabasePath) {
        Get-Content $DatabasePath | ConvertFrom-Json -AsHashtable
    } else {
        @{
            Metadata = @{TotalAttempts = 0; SuccessRate = 0.0; TotalSessions = 0; LastUpdated = ""}
            SuccessfulPatterns = @()
            ErrorPatterns = @()
            TheoremMapping = @()
            AutoFixSuggestions = @()
        }
    }
    
    do {
        Show-MainMenu
        $choice = Read-Host "選択してください (1-7)"
        
        switch ($choice) {
            "1" {
                $theorem = Read-Host "探している定理・戦術名を入力してください"
                Search-TheoremInDatabase $theorem $database
            }
            "2" {
                $field = Read-Host "数学分野を入力してください (例: 自然数, 整数, 実数, 代数, 戦術)"
                Suggest-ImportsForField $field
            }
            "3" {
                Write-Host "エラーメッセージを貼り付けてください:"
                $errorMsg = Read-Host "Error"
                Analyze-ErrorMessage $errorMsg
            }
            "4" {
                if ($database.SuccessfulPatterns.Count -gt 0) {
                    Write-Host "✅ 成功したImportパターン:" -ForegroundColor Green
                    $database.SuccessfulPatterns | ForEach-Object {
                        Write-Host "  $($_.ImportStatement)" -ForegroundColor White
                    }
                } else {
                    Write-Host "まだ成功パターンが記録されていません" -ForegroundColor Yellow
                }
            }
            "5" {
                Interactive-ImportTester $database
                # データベース保存
                $database | ConvertTo-Json -Depth 10 | Out-File -FilePath $DatabasePath -Encoding UTF8
            }
            "6" {
                Show-DatabaseStats $database
            }
            "7" {
                Write-Host "システムを終了します" -ForegroundColor Green
                break
            }
            default {
                Write-Host "無効な選択です" -ForegroundColor Red
            }
        }
        
        if ($choice -ne "7") {
            Write-Host "`nEnterキーで続行..." -ForegroundColor Gray
            Read-Host
        }
        
    } while ($choice -ne "7")
}

# スクリプト実行
if ($Goal) {
    Write-Host "目標: $Goal" -ForegroundColor Yellow
    # 目標に基づいた自動提案を実装
}

Start-InteractiveSession