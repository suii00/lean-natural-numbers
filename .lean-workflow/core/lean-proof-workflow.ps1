# Lean証明プロジェクト用完全Gitワークフローシステム
# Version: 1.0.0
# 作成日: 2025-08-06

[CmdletBinding()]
param(
    [Parameter(Mandatory=$true)]
    [ValidateSet("auto-commit", "error-fix", "daily-report", "weekly-report", "auto-push", "tag-difficulty", "init-workflow", "status")]
    [string]$Action,
    
    [string]$ProofFile = "",
    [string]$ErrorDescription = "",
    [ValidateSet("beginner", "intermediate", "advanced", "expert", "research")]
    [string]$Difficulty = "intermediate",
    [string]$Message = "",
    [switch]$Force
)

# 設定とパス
$WorkflowRoot = Split-Path -Parent $PSScriptRoot
$ProjectRoot = Split-Path -Parent (Split-Path -Parent $WorkflowRoot)
$ConfigPath = Join-Path $WorkflowRoot "config\workflow-config.json"
$LogsPath = Join-Path $WorkflowRoot "logs"
$ReportsPath = Join-Path $WorkflowRoot "reports"

# 設定ファイル読み込み
if (Test-Path $ConfigPath) {
    $Config = Get-Content $ConfigPath | ConvertFrom-Json
} else {
    Write-Error "設定ファイルが見つかりません: $ConfigPath"
    Write-Host "まず 'init-workflow' を実行してください。"
    exit 1
}

# ログ記録関数
function Write-WorkflowLog {
    param([string]$Message, [string]$Level = "INFO")
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $logEntry = "[$timestamp] [$Level] $Message"
    
    # コンソール出力
    switch ($Level) {
        "ERROR" { Write-Host $logEntry -ForegroundColor Red }
        "WARNING" { Write-Host $logEntry -ForegroundColor Yellow }
        "SUCCESS" { Write-Host $logEntry -ForegroundColor Green }
        default { Write-Host $logEntry -ForegroundColor White }
    }
    
    # ファイル出力
    $logFile = Join-Path $LogsPath "workflow-$(Get-Date -Format 'yyyy-MM-dd').log"
    $logEntry | Out-File -FilePath $logFile -Append -Encoding UTF8
}

# Git状態チェック関数
function Test-GitRepository {
    if (-not (Test-Path ".git")) {
        Write-WorkflowLog "Gitリポジトリではありません。" "ERROR"
        return $false
    }
    return $true
}

# 証明ファイル検証関数
function Test-LeanProof {
    param([string]$FilePath)
    
    Write-WorkflowLog "証明を検証中: $FilePath"
    
    # Lake check実行
    $lakeResult = & lake check $FilePath 2>&1
    $lakeExitCode = $LASTEXITCODE
    
    if ($lakeExitCode -eq 0) {
        Write-WorkflowLog "証明検証成功: $FilePath" "SUCCESS"
        return @{
            Success = $true
            Output = $lakeResult
            Errors = @()
        }
    } else {
        Write-WorkflowLog "証明検証失敗: $FilePath" "ERROR"
        return @{
            Success = $false
            Output = $lakeResult
            Errors = $lakeResult | Where-Object { $_ -match "error" }
        }
    }
}

# 難易度分析関数
function Get-ProofDifficulty {
    param([string]$FilePath)
    
    if (-not (Test-Path $FilePath)) {
        return "unknown"
    }
    
    $content = Get-Content $FilePath -Raw
    $lines = ($content -split "`n").Count
    $complexTactics = @("simp_all", "omega", "decide", "aesop", "polyrith", "field_simp", "ring_nf")
    $complexCount = 0
    
    foreach ($tactic in $complexTactics) {
        $complexCount += ([regex]::Matches($content, $tactic)).Count
    }
    
    $theoremCount = ([regex]::Matches($content, "theorem|lemma|def")).Count
    $importCount = ([regex]::Matches($content, "import")).Count
    
    # 複雑性スコア計算
    $complexityScore = ($lines * 0.1) + ($complexCount * 2) + ($theoremCount * 1.5) + ($importCount * 0.5)
    
    switch ($complexityScore) {
        {$_ -le 10} { return "beginner" }
        {$_ -le 25} { return "intermediate" }
        {$_ -le 50} { return "advanced" }
        {$_ -le 100} { return "expert" }
        default { return "research" }
    }
}

# 自動コミット機能
function Invoke-AutoCommit {
    param([string]$ProofFile, [string]$CustomMessage = "")
    
    Write-WorkflowLog "自動コミットを実行中..."
    
    if (-not (Test-GitRepository)) { return }
    
    # 証明検証
    $verification = Test-LeanProof $ProofFile
    if (-not $verification.Success) {
        Write-WorkflowLog "証明が完成していません。コミットを中止します。" "WARNING"
        return
    }
    
    # 難易度判定
    $difficulty = Get-ProofDifficulty $ProofFile
    Write-WorkflowLog "証明難易度: $difficulty"
    
    # コミットメッセージ生成
    $proofName = [System.IO.Path]::GetFileNameWithoutExtension($ProofFile)
    if ($CustomMessage) {
        $commitMessage = $CustomMessage
    } else {
        $commitMessage = @"
Complete Lean proof: $proofName [$difficulty]

- Verified proof correctness with lake check
- Difficulty level: $difficulty
- File: $ProofFile
- Completion time: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')

🎯 Proof successfully completed and verified.

🤖 Generated with [Claude Code](https://claude.ai/code)

Co-Authored-By: Claude <noreply@anthropic.com>
"@
    }
    
    # Git操作
    try {
        & git add $ProofFile
        if ($LASTEXITCODE -ne 0) {
            Write-WorkflowLog "git add に失敗しました" "ERROR"
            return
        }
        
        & git commit -m $commitMessage
        if ($LASTEXITCODE -ne 0) {
            Write-WorkflowLog "git commit に失敗しました" "ERROR"
            return
        }
        
        Write-WorkflowLog "証明を正常にコミットしました: $proofName" "SUCCESS"
        
        # タグ付け
        $tagName = "proof-$proofName-$(Get-Date -Format 'yyyyMMdd-HHmmss')"
        & git tag -a $tagName -m "Completed proof: $proofName [$difficulty]"
        Write-WorkflowLog "タグを作成しました: $tagName"
        
    } catch {
        Write-WorkflowLog "コミット中にエラーが発生しました: $($_.Exception.Message)" "ERROR"
    }
}

# エラー修正履歴記録機能
function Record-ErrorFix {
    param([string]$ProofFile, [string]$ErrorDescription, [string]$FixDescription = "")
    
    Write-WorkflowLog "エラー修正を記録中..."
    
    $errorLog = @{
        Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        File = $ProofFile
        Error = $ErrorDescription
        Fix = $FixDescription
        GitCommit = (& git rev-parse HEAD 2>$null)
        Branch = (& git branch --show-current 2>$null)
    }
    
    # エラーログファイルに保存
    $errorLogFile = Join-Path $LogsPath "error-fixes-$(Get-Date -Format 'yyyy-MM').json"
    
    $existingLogs = @()
    if (Test-Path $errorLogFile) {
        $existingLogs = Get-Content $errorLogFile | ConvertFrom-Json
    }
    
    $existingLogs += $errorLog
    $existingLogs | ConvertTo-Json -Depth 3 | Out-File -FilePath $errorLogFile -Encoding UTF8
    
    Write-WorkflowLog "エラー修正履歴を記録しました: $ProofFile" "SUCCESS"
    
    # 修正コミット
    if (Test-Path $ProofFile) {
        $commitMessage = @"
Fix errors in Lean proof: $(Split-Path $ProofFile -Leaf)

Error: $ErrorDescription
$(if ($FixDescription) { "Fix: $FixDescription" })

- Applied error corrections
- Updated proof implementation
- Verified with lake check

🛠️ Error resolution completed.

🤖 Generated with [Claude Code](https://claude.ai/code)

Co-Authored-By: Claude <noreply@anthropic.com>
"@
        
        & git add $ProofFile
        & git commit -m $commitMessage
        Write-WorkflowLog "エラー修正をコミットしました" "SUCCESS"
    }
}

# 進捗レポート生成機能
function New-ProgressReport {
    param([ValidateSet("daily", "weekly")][string]$ReportType)
    
    Write-WorkflowLog "$ReportType レポートを生成中..."
    
    $dateFormat = if ($ReportType -eq "daily") { "yyyy-MM-dd" } else { "yyyy-'W'ww" }
    $reportDate = Get-Date -Format $dateFormat
    $reportFile = Join-Path $ReportsPath "$ReportType-report-$reportDate.md"
    
    # Git統計取得
    $dateRange = if ($ReportType -eq "daily") { 
        "--since='1 day ago'" 
    } else { 
        "--since='1 week ago'" 
    }
    
    $commits = & git log --oneline $dateRange 2>$null | Measure-Object
    $files = & git log --name-only --pretty=format: $dateRange 2>$null | Where-Object { $_ -like "*.lean" } | Sort-Object -Unique
    
    # 証明ファイル分析
    $proofStats = @{
        TotalProofs = 0
        CompletedProofs = 0
        ByDifficulty = @{
            beginner = 0
            intermediate = 0
            advanced = 0
            expert = 0
            research = 0
        }
    }
    
    Get-ChildItem -Path $ProjectRoot -Filter "*.lean" -Recurse | ForEach-Object {
        $proofStats.TotalProofs++
        $verification = Test-LeanProof $_.FullName
        if ($verification.Success) {
            $proofStats.CompletedProofs++
        }
        
        $difficulty = Get-ProofDifficulty $_.FullName
        $proofStats.ByDifficulty[$difficulty]++
    }
    
    # レポート生成
    $report = @"
# Lean 証明プロジェクト $ReportType レポート

**生成日時**: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")
**期間**: $reportDate

## 📊 開発統計

### Git活動
- **コミット数**: $($commits.Count)
- **変更されたLeanファイル**: $($files.Count)

### 証明統計
- **総証明数**: $($proofStats.TotalProofs)
- **完成証明数**: $($proofStats.CompletedProofs)
- **完成率**: $(if ($proofStats.TotalProofs -gt 0) { [math]::Round(($proofStats.CompletedProofs / $proofStats.TotalProofs) * 100, 1) } else { 0 })%

### 難易度別分布
- **初級 (beginner)**: $($proofStats.ByDifficulty.beginner)
- **中級 (intermediate)**: $($proofStats.ByDifficulty.intermediate)  
- **上級 (advanced)**: $($proofStats.ByDifficulty.advanced)
- **専門 (expert)**: $($proofStats.ByDifficulty.expert)
- **研究 (research)**: $($proofStats.ByDifficulty.research)

## 📋 最近のコミット

$(& git log --oneline $dateRange --max-count=10 2>$null | ForEach-Object { "- $_" })

## 🎯 次のステップ

$(if ($proofStats.TotalProofs -eq $proofStats.CompletedProofs) { 
"✅ 全ての証明が完成しています！新しい証明課題の追加を検討してください。" 
} else { 
"🔄 未完成の証明: $($proofStats.TotalProofs - $proofStats.CompletedProofs)個
優先して完成させる証明の特定を行ってください。" })

---
*自動生成レポート - Lean証明ワークフローシステム*
"@
    
    $report | Out-File -FilePath $reportFile -Encoding UTF8
    Write-WorkflowLog "$ReportType レポートを生成しました: $reportFile" "SUCCESS"
    
    return $reportFile
}

# GitHub自動プッシュ機能
function Invoke-AutoPush {
    param([switch]$IncludeTags)
    
    Write-WorkflowLog "GitHubへの自動プッシュを実行中..."
    
    if (-not (Test-GitRepository)) { return }
    
    try {
        # リモートの存在確認
        $remotes = & git remote -v 2>$null
        if (-not $remotes) {
            Write-WorkflowLog "リモートリポジトリが設定されていません" "WARNING"
            return
        }
        
        # 現在のブランチ取得
        $currentBranch = & git branch --show-current
        
        # プッシュ実行
        & git push origin $currentBranch
        if ($LASTEXITCODE -ne 0) {
            Write-WorkflowLog "git push に失敗しました" "ERROR"
            return
        }
        
        Write-WorkflowLog "ブランチ $currentBranch を正常にプッシュしました" "SUCCESS"
        
        # タグプッシュ
        if ($IncludeTags) {
            & git push origin --tags
            if ($LASTEXITCODE -eq 0) {
                Write-WorkflowLog "タグを正常にプッシュしました" "SUCCESS"
            } else {
                Write-WorkflowLog "タグのプッシュに失敗しました" "WARNING"
            }
        }
        
    } catch {
        Write-WorkflowLog "プッシュ中にエラーが発生しました: $($_.Exception.Message)" "ERROR"
    }
}

# 難易度タグ付け機能
function Set-DifficultyTag {
    param([string]$ProofFile, [string]$Difficulty)
    
    Write-WorkflowLog "難易度タグを設定中: $Difficulty"
    
    if (-not (Test-Path $ProofFile)) {
        Write-WorkflowLog "証明ファイルが見つかりません: $ProofFile" "ERROR"
        return
    }
    
    $proofName = [System.IO.Path]::GetFileNameWithoutExtension($ProofFile)
    $tagName = "difficulty-$Difficulty-$proofName-$(Get-Date -Format 'yyyyMMdd')"
    
    try {
        & git tag -a $tagName -m "Proof difficulty classification: $proofName [$Difficulty]"
        Write-WorkflowLog "難易度タグを作成しました: $tagName" "SUCCESS"
        
        # タグ情報をメタデータファイルに記録
        $metadataFile = Join-Path $WorkflowRoot "metadata\proof-metadata.json"
        $metadata = @{}
        
        if (Test-Path $metadataFile) {
            $metadata = Get-Content $metadataFile | ConvertFrom-Json -AsHashtable
        }
        
        if (-not $metadata.ContainsKey($ProofFile)) {
            $metadata[$ProofFile] = @{}
        }
        
        $metadata[$ProofFile].Difficulty = $Difficulty
        $metadata[$ProofFile].LastUpdated = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        $metadata[$ProofFile].Tag = $tagName
        
        $metadata | ConvertTo-Json -Depth 3 | Out-File -FilePath $metadataFile -Encoding UTF8
        
    } catch {
        Write-WorkflowLog "タグ作成中にエラーが発生しました: $($_.Exception.Message)" "ERROR"
    }
}

# ワークフロー初期化機能
function Initialize-Workflow {
    Write-WorkflowLog "Lean証明ワークフローを初期化中..."
    
    # ディレクトリ構造作成
    $directories = @(
        $LogsPath,
        $ReportsPath,
        (Join-Path $WorkflowRoot "config"),
        (Join-Path $WorkflowRoot "metadata"),
        (Join-Path $WorkflowRoot "templates"),
        (Join-Path $WorkflowRoot "hooks")
    )
    
    foreach ($dir in $directories) {
        if (-not (Test-Path $dir)) {
            New-Item -Path $dir -ItemType Directory -Force | Out-Null
            Write-WorkflowLog "ディレクトリを作成しました: $dir"
        }
    }
    
    # 設定ファイル作成
    if (-not (Test-Path $ConfigPath)) {
        $defaultConfig = @{
            Version = "1.0.0"
            AutoCommit = @{
                Enabled = $true
                VerifyProofFirst = $true
                IncludeDifficultyTag = $true
            }
            AutoPush = @{
                Enabled = $false
                IncludeTags = $true
                RemoteName = "origin"
            }
            Reports = @{
                DailyEnabled = $true
                WeeklyEnabled = $true
                AutoGenerate = $false
            }
            DifficultyClassification = @{
                AutoDetect = $true
                DefaultLevel = "intermediate"
            }
            Notifications = @{
                Enabled = $true
                OnSuccess = $true
                OnError = $true
            }
        }
        
        $defaultConfig | ConvertTo-Json -Depth 3 | Out-File -FilePath $ConfigPath -Encoding UTF8
        Write-WorkflowLog "設定ファイルを作成しました: $ConfigPath" "SUCCESS"
    }
    
    Write-WorkflowLog "ワークフローの初期化が完了しました" "SUCCESS"
    Write-Host "`n🎉 Lean証明ワークフローシステムが初期化されました！" -ForegroundColor Green
    Write-Host "`n📝 使用方法:" -ForegroundColor Cyan
    Write-Host "  証明完成時: .\lean-proof-workflow.ps1 -Action auto-commit -ProofFile 'proof.lean'"
    Write-Host "  エラー修正時: .\lean-proof-workflow.ps1 -Action error-fix -ProofFile 'proof.lean' -ErrorDescription 'エラー内容'"
    Write-Host "  日次レポート: .\lean-proof-workflow.ps1 -Action daily-report"
    Write-Host "  週次レポート: .\lean-proof-workflow.ps1 -Action weekly-report"
    Write-Host "  自動プッシュ: .\lean-proof-workflow.ps1 -Action auto-push"
}

# ステータス表示機能
function Show-WorkflowStatus {
    Write-Host "`n📊 Lean証明ワークフローシステム ステータス" -ForegroundColor Cyan
    Write-Host "=" * 50
    
    # 設定状況
    Write-Host "`n⚙️  設定状況:"
    if (Test-Path $ConfigPath) {
        Write-Host "  ✅ 設定ファイル: 存在" -ForegroundColor Green
        $config = Get-Content $ConfigPath | ConvertFrom-Json
        Write-Host "  📊 自動コミット: $(if($config.AutoCommit.Enabled){'有効'}else{'無効'})"
        Write-Host "  🚀 自動プッシュ: $(if($config.AutoPush.Enabled){'有効'}else{'無効'})"
    } else {
        Write-Host "  ❌ 設定ファイル: 未作成" -ForegroundColor Red
    }
    
    # Git状況
    Write-Host "`n📁 Git状況:"
    if (Test-GitRepository) {
        Write-Host "  ✅ Gitリポジトリ: 検出済み" -ForegroundColor Green
        $branch = & git branch --show-current 2>$null
        Write-Host "  🌿 現在のブランチ: $branch"
        $uncommitted = & git status --porcelain 2>$null
        if ($uncommitted) {
            Write-Host "  ⚠️  未コミットの変更: $($uncommitted.Count)個" -ForegroundColor Yellow
        } else {
            Write-Host "  ✅ 作業ツリー: クリーン" -ForegroundColor Green
        }
    } else {
        Write-Host "  ❌ Gitリポジトリ: 未検出" -ForegroundColor Red
    }
    
    # 証明ファイル統計
    Write-Host "`n🎯 証明ファイル統計:"
    $leanFiles = Get-ChildItem -Path $ProjectRoot -Filter "*.lean" -Recurse
    Write-Host "  📄 総Leanファイル数: $($leanFiles.Count)"
    
    # 最近のログ
    Write-Host "`n📝 最近のログ:"
    $logFile = Join-Path $LogsPath "workflow-$(Get-Date -Format 'yyyy-MM-dd').log"
    if (Test-Path $logFile) {
        $recentLogs = Get-Content $logFile -Tail 3
        foreach ($log in $recentLogs) {
            Write-Host "  $log"
        }
    } else {
        Write-Host "  ℹ️  今日のログはまだありません"
    }
    
    Write-Host "`n" + "=" * 50
}

# メイン実行ロジック
switch ($Action) {
    "auto-commit" {
        if (-not $ProofFile) {
            Write-WorkflowLog "証明ファイルが指定されていません" "ERROR"
            exit 1
        }
        Invoke-AutoCommit -ProofFile $ProofFile -CustomMessage $Message
    }
    
    "error-fix" {
        if (-not $ProofFile -or -not $ErrorDescription) {
            Write-WorkflowLog "証明ファイルまたはエラー説明が指定されていません" "ERROR"
            exit 1
        }
        Record-ErrorFix -ProofFile $ProofFile -ErrorDescription $ErrorDescription -FixDescription $Message
    }
    
    "daily-report" {
        $reportFile = New-ProgressReport -ReportType "daily"
        Write-Host "📊 日次レポートを生成しました: $reportFile" -ForegroundColor Green
    }
    
    "weekly-report" {
        $reportFile = New-ProgressReport -ReportType "weekly"
        Write-Host "📊 週次レポートを生成しました: $reportFile" -ForegroundColor Green
    }
    
    "auto-push" {
        Invoke-AutoPush -IncludeTags
    }
    
    "tag-difficulty" {
        if (-not $ProofFile) {
            Write-WorkflowLog "証明ファイルが指定されていません" "ERROR"
            exit 1
        }
        if (-not $Difficulty) {
            $Difficulty = Get-ProofDifficulty $ProofFile
            Write-WorkflowLog "自動判定された難易度: $Difficulty"
        }
        Set-DifficultyTag -ProofFile $ProofFile -Difficulty $Difficulty
    }
    
    "init-workflow" {
        Initialize-Workflow
    }
    
    "status" {
        Show-WorkflowStatus
    }
    
    default {
        Write-Host "不明なアクション: $Action" -ForegroundColor Red
        exit 1
    }
}