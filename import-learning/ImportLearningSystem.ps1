# Mathlib Import学習システム
# import試行錯誤を完全記録し、学習データベースを構築

param(
    [string]$DatabasePath = "import-learning\import_database.json",
    [string]$SessionLog = "",
    [switch]$Verbose,
    [switch]$ExportReport
)

# データベース構造定義
$databaseSchema = @{
    Metadata = @{
        Version = "1.0"
        Created = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        LastUpdated = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        TotalSessions = 0
        TotalAttempts = 0
        SuccessRate = 0.0
    }
    
    ImportAttempts = @()      # 全import試行記録
    SuccessfulPatterns = @()  # 成功したimportパターン
    ErrorPatterns = @()       # エラーパターンと原因
    TheoremMapping = @()      # 定理名新旧対応表
    AutoFixSuggestions = @()  # 自動修正提案
    LearningInsights = @()    # 学習から得られた知見
}

function Initialize-ImportDatabase {
    param([string]$Path)
    
    if (Test-Path $Path) {
        $database = Get-Content $Path | ConvertFrom-Json -AsHashtable
        Write-Host "既存データベース読み込み: $Path" -ForegroundColor Green
        
        # バージョンアップグレード処理
        if (-not $database.Metadata) {
            $database.Metadata = $databaseSchema.Metadata
        }
        
        return $database
    } else {
        Write-Host "新規データベース作成: $Path" -ForegroundColor Yellow
        return $databaseSchema.Clone()
    }
}

function Test-ImportStatement {
    param([string]$ImportStatement, [string]$TestCode = "")
    
    # 一時テストファイル作成
    $timestamp = Get-Date -Format "HHmmss"
    $testFile = "import-learning\temp_test_$timestamp.lean"
    
    $defaultTestCode = @"
-- Test theorem to verify import
theorem test_import : True := trivial
#check True
"@
    
    $fullTestCode = if ($TestCode) { $TestCode } else { $defaultTestCode }
    $fileContent = "$ImportStatement`n`n$fullTestCode"
    
    $fileContent | Out-File -FilePath $testFile -Encoding UTF8
    
    try {
        Write-Host "テスト中: $ImportStatement" -ForegroundColor Yellow
        $output = & lake env lean $testFile 2>&1
        $success = $LASTEXITCODE -eq 0
        
        $result = @{
            ImportStatement = $ImportStatement
            Success = $success
            Output = $output -join "`n"
            TestCode = $fullTestCode
            Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
            Duration = 0  # 計測は後で追加
            Errors = @()
        }
        
        if (-not $success) {
            $result.Errors = $output | Where-Object { $_ -match "error:" }
        }
        
        return $result
        
    } finally {
        Remove-Item $testFile -ErrorAction SilentlyContinue
    }
}

function Record-ImportAttempt {
    param([hashtable]$Database, [hashtable]$AttemptResult)
    
    # 試行記録を追加
    $Database.ImportAttempts += $AttemptResult
    
    # 成功パターンの記録
    if ($AttemptResult.Success) {
        $successPattern = @{
            ImportStatement = $AttemptResult.ImportStatement
            TestCode = $AttemptResult.TestCode
            FirstSuccessDate = $AttemptResult.Timestamp
            SuccessCount = 1
            AverageResponseTime = $AttemptResult.Duration
        }
        
        # 既存の成功パターンがあるかチェック
        $existing = $Database.SuccessfulPatterns | Where-Object { $_.ImportStatement -eq $AttemptResult.ImportStatement }
        if ($existing) {
            $existing.SuccessCount++
            $existing.LastSuccessDate = $AttemptResult.Timestamp
        } else {
            $Database.SuccessfulPatterns += $successPattern
        }
        
        Write-Host "✅ 成功パターン記録: $($AttemptResult.ImportStatement)" -ForegroundColor Green
    } else {
        # エラーパターンの分析と記録
        $errorPattern = Analyze-ImportError $AttemptResult
        $Database.ErrorPatterns += $errorPattern
        
        Write-Host "❌ エラーパターン記録: $($errorPattern.ErrorType)" -ForegroundColor Red
    }
    
    # メタデータ更新
    $Database.Metadata.TotalAttempts++
    $Database.Metadata.LastUpdated = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    
    $successCount = ($Database.ImportAttempts | Where-Object { $_.Success }).Count
    $Database.Metadata.SuccessRate = $successCount / $Database.Metadata.TotalAttempts
}

function Analyze-ImportError {
    param([hashtable]$AttemptResult)
    
    $errors = $AttemptResult.Errors
    $errorTypes = @()
    $suggestedFixes = @()
    
    foreach ($error in $errors) {
        if ($error -match "object file.*\.olean.*does not exist") {
            $errorTypes += "MissingObjectFile"
            $suggestedFixes += "依存関係のビルドが必要: lake build"
            
            # 不足しているモジュールを特定
            if ($error -match "of module ([^\s]+)") {
                $missingModule = $matches[1]
                $suggestedFixes += "特定モジュールビルド: lake build $missingModule"
            }
        } elseif ($error -match "unknown identifier") {
            $errorTypes += "UnknownIdentifier"
            $suggestedFixes += "定理名または型名の確認が必要"
        } elseif ($error -match "expected token") {
            $errorTypes += "SyntaxError"
            $suggestedFixes += "構文エラー: import文の記法確認"
        } elseif ($error -match "module.*not found") {
            $errorTypes += "ModuleNotFound"
            $suggestedFixes += "モジュール名の確認またはMathlib更新"
        }
    }
    
    return @{
        ImportStatement = $AttemptResult.ImportStatement
        ErrorType = $errorTypes -join ", "
        ErrorMessages = $AttemptResult.Errors
        SuggestedFixes = $suggestedFixes
        Timestamp = $AttemptResult.Timestamp
        Frequency = 1
    }
}

function Generate-AutoFixSuggestion {
    param([hashtable]$Database, [string]$FailedImport, [string[]]$ErrorMessages)
    
    $suggestions = @()
    
    # 成功パターンから類似するものを検索
    $similarSuccessful = $Database.SuccessfulPatterns | Where-Object {
        $_.ImportStatement -match ($FailedImport -replace "Mathlib\.", ".*")
    }
    
    if ($similarSuccessful) {
        $suggestions += @{
            Type = "SimilarSuccessful"
            Description = "類似の成功パターンが見つかりました"
            Suggestions = $similarSuccessful | ForEach-Object { $_.ImportStatement }
            Confidence = 0.8
        }
    }
    
    # エラーパターンから修正案を生成
    foreach ($errorMsg in $ErrorMessages) {
        if ($errorMsg -match "object file.*of module ([^\s]+)") {
            $missingModule = $matches[1]
            $suggestions += @{
                Type = "BuildDependency"
                Description = "依存関係のビルドが必要です"
                Suggestions = @("lake build $missingModule", "lake exe cache get")
                Confidence = 0.9
            }
        }
        
        if ($errorMsg -match "module.*not found" -and $FailedImport -match "Mathlib\.(.+)") {
            $modulePath = $matches[1]
            $alternatives = @(
                "import Mathlib.Data.$modulePath",
                "import Mathlib.Tactic.$modulePath",
                "import Mathlib.Init.$modulePath"
            )
            
            $suggestions += @{
                Type = "AlternativeModulePath"
                Description = "代替モジュールパスを試してください"
                Suggestions = $alternatives
                Confidence = 0.6
            }
        }
    }
    
    return @{
        FailedImport = $FailedImport
        Suggestions = $suggestions
        GeneratedAt = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        Applied = $false
    }
}

function Update-TheoremMapping {
    param([hashtable]$Database, [string]$OldName, [string]$NewName, [string]$ImportRequired)
    
    $existing = $Database.TheoremMapping | Where-Object { $_.OldName -eq $OldName }
    
    if ($existing) {
        $existing.NewName = $NewName
        $existing.ImportRequired = $ImportRequired
        $existing.LastUpdated = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        $existing.UsageCount++
    } else {
        $Database.TheoremMapping += @{
            OldName = $OldName
            NewName = $NewName
            ImportRequired = $ImportRequired
            Category = "Auto-detected"
            Confidence = 0.8
            UsageCount = 1
            FirstDetected = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
            LastUpdated = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        }
    }
    
    Write-Host "📝 定理マッピング更新: $OldName → $NewName" -ForegroundColor Cyan
}

function Save-Database {
    param([hashtable]$Database, [string]$Path)
    
    $Database.Metadata.LastUpdated = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    
    # JSONに変換して保存
    $Database | ConvertTo-Json -Depth 10 | Out-File -FilePath $Path -Encoding UTF8
    
    Write-Host "💾 データベース保存完了: $Path" -ForegroundColor Green
}

function Export-LearningReport {
    param([hashtable]$Database, [string]$OutputPath = "import-learning\learning_report.md")
    
    $report = @"
# Mathlib Import学習レポート

## 📊 学習統計

- **総試行数**: $($Database.Metadata.TotalAttempts)
- **成功率**: $(($Database.Metadata.SuccessRate * 100).ToString('F1'))%
- **成功パターン数**: $($Database.SuccessfulPatterns.Count)
- **エラーパターン数**: $($Database.ErrorPatterns.Count)
- **定理マッピング数**: $($Database.TheoremMapping.Count)

## ✅ 成功したImportパターン

"@

    $Database.SuccessfulPatterns | Sort-Object SuccessCount -Descending | ForEach-Object {
        $report += @"

### $($_.ImportStatement)
- **成功回数**: $($_.SuccessCount)
- **初回成功**: $($_.FirstSuccessDate)

"@
    }
    
    $report += @"

## ❌ よくあるエラーパターン

"@

    $Database.ErrorPatterns | Group-Object ErrorType | ForEach-Object {
        $errorType = $_.Name
        $count = $_.Count
        $report += @"

### $errorType ($count件)
"@
        $_.Group | Select-Object -First 3 | ForEach-Object {
            $report += @"
- **Import**: ``$($_.ImportStatement)``
- **修正提案**: $($_.SuggestedFixes -join ", ")
"@
        }
    }
    
    $report += @"

## 🔄 定理名対応表

| 旧名 | 新名 | 必要Import | 使用回数 |
|------|------|------------|----------|
"@

    $Database.TheoremMapping | Sort-Object UsageCount -Descending | ForEach-Object {
        $report += "`n| ``$($_.OldName)`` | ``$($_.NewName)`` | ``$($_.ImportRequired)`` | $($_.UsageCount) |"
    }
    
    $report += @"

## 💡 学習から得られた知見

"@

    $Database.LearningInsights | ForEach-Object {
        $report += @"

### $($_.Title)
$($_.Description)

**推奨事項**: $($_.Recommendation)

"@
    }
    
    $report += @"

---

*このレポートは Import学習システム によって自動生成されました*
*最終更新: $($Database.Metadata.LastUpdated)*
"@
    
    $report | Out-File -FilePath $OutputPath -Encoding UTF8
    Write-Host "📄 学習レポート生成: $OutputPath" -ForegroundColor Green
}

# セッション実行関数
function Start-ImportLearningSession {
    param([string[]]$ImportStatements, [hashtable]$TestCases = @{})
    
    Write-Host "🎓 Import学習セッション開始" -ForegroundColor Green
    Write-Host "データベース: $DatabasePath" -ForegroundColor Gray
    
    # データベース初期化
    $database = Initialize-ImportDatabase $DatabasePath
    
    $sessionResults = @()
    $sessionStartTime = Get-Date
    
    foreach ($importStatement in $ImportStatements) {
        $testCode = if ($TestCases.ContainsKey($importStatement)) { 
            $TestCases[$importStatement] 
        } else { 
            "" 
        }
        
        $attemptResult = Test-ImportStatement $importStatement $testCode
        Record-ImportAttempt $database $attemptResult
        
        if (-not $attemptResult.Success) {
            $autoFix = Generate-AutoFixSuggestion $database $importStatement $attemptResult.Errors
            $database.AutoFixSuggestions += $autoFix
            
            if ($Verbose) {
                Write-Host "自動修正提案:" -ForegroundColor Cyan
                $autoFix.Suggestions | ForEach-Object {
                    Write-Host "  - $($_.Description)" -ForegroundColor White
                }
            }
        }
        
        $sessionResults += $attemptResult
    }
    
    $sessionDuration = (Get-Date) - $sessionStartTime
    
    # セッション情報をデータベースに記録
    $database.Metadata.TotalSessions++
    
    # データベース保存
    Save-Database $database $DatabasePath
    
    # セッション結果表示
    $successCount = ($sessionResults | Where-Object { $_.Success }).Count
    $totalCount = $sessionResults.Count
    
    Write-Host "`n📊 セッション結果:" -ForegroundColor Cyan
    Write-Host "成功: $successCount / $totalCount" -ForegroundColor Green
    Write-Host "成功率: $(($successCount / $totalCount * 100).ToString('F1'))%" -ForegroundColor Green
    Write-Host "実行時間: $($sessionDuration.TotalSeconds.ToString('F1'))秒" -ForegroundColor Gray
    
    if ($ExportReport) {
        Export-LearningReport $database
    }
    
    return $database
}

# スクリプト使用例とヘルプ
if ($args.Count -eq 0) {
    Write-Host @"
🎓 Mathlib Import学習システム

使用方法:
  # 基本使用
  `$imports = @("import Mathlib.Tactic.Basic", "import Mathlib.Data.Nat.Basic")
  Start-ImportLearningSession `$imports

  # テストケース付き
  `$testCases = @{
    "import Mathlib.Data.Nat.Basic" = "theorem test : ∀ n : ℕ, n + 0 = n := add_zero"
  }
  Start-ImportLearningSession `$imports `$testCases

  # レポート生成
  Start-ImportLearningSession `$imports -ExportReport -Verbose

データベース: $DatabasePath
"@ -ForegroundColor Yellow
}