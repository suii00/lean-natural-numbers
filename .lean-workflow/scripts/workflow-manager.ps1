# Lean証明プロジェクト 統合ワークフロー管理システム
# Version: 1.0.0

[CmdletBinding()]
param(
    [Parameter(Mandatory=$true)]
    [ValidateSet("init", "status", "configure", "run", "deploy", "reset", "update", "validate", "benchmark")]
    [string]$Action,
    
    [string]$Component = "all",
    [string]$ConfigFile = "",
    [switch]$Force,
    [switch]$DryRun,
    [switch]$Verbose,
    [switch]$Interactive
)

# グローバル設定
$WorkflowRoot = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
$ProjectRoot = Split-Path -Parent (Split-Path -Parent $WorkflowRoot)
$ConfigPath = Join-Path $WorkflowRoot "config\master-config.json"
$LogPath = Join-Path $WorkflowRoot "logs\workflow-manager.log"

# ディレクトリ確保
if (-not (Test-Path (Split-Path $LogPath))) {
    New-Item -Path (Split-Path $LogPath) -ItemType Directory -Force | Out-Null
}

# ログ関数
function Write-WorkflowLog {
    param([string]$Message, [string]$Level = "INFO", [switch]$NoConsole)
    
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $logEntry = "[$timestamp] [$Level] $Message"
    
    # コンソール出力
    if (-not $NoConsole) {
        switch ($Level) {
            "ERROR" { Write-Host $logEntry -ForegroundColor Red }
            "WARNING" { Write-Host $logEntry -ForegroundColor Yellow }
            "SUCCESS" { Write-Host $logEntry -ForegroundColor Green }
            "INFO" { Write-Host $logEntry -ForegroundColor Cyan }
            "DEBUG" { if ($Verbose) { Write-Host $logEntry -ForegroundColor Gray } }
            default { Write-Host $logEntry -ForegroundColor White }
        }
    }
    
    # ファイル出力
    $logEntry | Out-File -FilePath $LogPath -Append -Encoding UTF8
}

# 設定読み込み
function Get-WorkflowConfig {
    param([string]$Path = $ConfigPath)
    
    if (-not (Test-Path $Path)) {
        Write-WorkflowLog "設定ファイルが見つかりません: $Path" "ERROR"
        return $null
    }
    
    try {
        $config = Get-Content $Path | ConvertFrom-Json
        Write-WorkflowLog "設定を読み込みました: $Path" "DEBUG"
        return $config
    } catch {
        Write-WorkflowLog "設定読み込みエラー: $($_.Exception.Message)" "ERROR"
        return $null
    }
}

# 設定保存
function Save-WorkflowConfig {
    param($Config, [string]$Path = $ConfigPath)
    
    try {
        $Config | ConvertTo-Json -Depth 10 | Out-File -FilePath $Path -Encoding UTF8
        Write-WorkflowLog "設定を保存しました: $Path" "SUCCESS"
    } catch {
        Write-WorkflowLog "設定保存エラー: $($_.Exception.Message)" "ERROR"
    }
}

# 環境検証
function Test-Environment {
    param($Config)
    
    Write-WorkflowLog "環境を検証中..." "INFO"
    
    $checks = @{
        Git = $false
        Lake = $false
        Lean = $false
        PowerShell = $false
        ProjectStructure = $false
    }
    
    # Git
    try {
        $gitVersion = & git --version 2>$null
        if ($gitVersion) {
            $checks.Git = $true
            Write-WorkflowLog "Git: OK ($gitVersion)" "SUCCESS"
        }
    } catch {
        Write-WorkflowLog "Git: 見つかりません" "ERROR"
    }
    
    # Lake
    try {
        $lakeVersion = & lake --version 2>$null
        if ($lakeVersion) {
            $checks.Lake = $true
            Write-WorkflowLog "Lake: OK ($lakeVersion)" "SUCCESS"
        }
    } catch {
        Write-WorkflowLog "Lake: 見つかりません" "ERROR"
    }
    
    # Lean
    try {
        $leanVersion = & lean --version 2>$null
        if ($leanVersion) {
            $checks.Lean = $true
            Write-WorkflowLog "Lean: OK ($leanVersion)" "SUCCESS"
        }
    } catch {
        Write-WorkflowLog "Lean: 見つかりません" "ERROR"
    }
    
    # PowerShell
    $psVersion = $PSVersionTable.PSVersion
    if ($psVersion.Major -ge 5) {
        $checks.PowerShell = $true
        Write-WorkflowLog "PowerShell: OK (v$psVersion)" "SUCCESS"
    } else {
        Write-WorkflowLog "PowerShell: バージョンが古すぎます (v$psVersion)" "ERROR"
    }
    
    # プロジェクト構造
    $requiredFiles = @("lakefile.lean", "lean-toolchain")
    $allExists = $true
    foreach ($file in $requiredFiles) {
        $filePath = Join-Path $ProjectRoot $file
        if (-not (Test-Path $filePath)) {
            Write-WorkflowLog "必須ファイルが見つかりません: $file" "ERROR"
            $allExists = $false
        }
    }
    $checks.ProjectStructure = $allExists
    
    if ($allExists) {
        Write-WorkflowLog "プロジェクト構造: OK" "SUCCESS"
    }
    
    return $checks
}

# ワークフロー初期化
function Initialize-Workflow {
    param($Config, [bool]$Force = $false)
    
    Write-WorkflowLog "Leanワークフローシステムを初期化中..." "INFO"
    
    # ディレクトリ構造作成
    $directories = @(
        $Config.paths.core,
        $Config.paths.automation,
        $Config.paths.errorTracking,
        $Config.paths.reporting,
        $Config.paths.github,
        $Config.paths.tagging,
        $Config.paths.config,
        $Config.paths.logs,
        $Config.paths.reports,
        $Config.paths.metadata,
        $Config.paths.templates,
        $Config.paths.hooks,
        $Config.paths.scripts
    )
    
    foreach ($dir in $directories) {
        $fullPath = Join-Path $ProjectRoot $dir
        if (-not (Test-Path $fullPath)) {
            New-Item -Path $fullPath -ItemType Directory -Force | Out-Null
            Write-WorkflowLog "ディレクトリを作成: $dir" "INFO"
        } elseif ($Force) {
            Write-WorkflowLog "ディレクトリを確認: $dir (存在済み)" "DEBUG"
        }
    }
    
    # コンポーネント設定ファイル作成
    $componentConfigs = @{
        "workflow-config.json" = @{
            AutoCommit = $Config.git.autoCommit
            AutoPush = $Config.git.autoPush
            Reports = $Config.reporting
            DifficultyClassification = $Config.difficulty
            Notifications = $Config.notifications
        }
        "github-config.json" = @{
            RemoteRepositories = $Config.github.repositories
            AutoPush = $Config.github.enabled
            Notifications = $Config.notifications
            Backup = $Config.github.backup
            Security = $Config.security
        }
        "error-config.json" = @{
            Categories = $Config.errorTracking.categories
            PatternLearning = $Config.errorTracking.patternLearning
            Retention = $Config.errorTracking.retention
            AutoRecord = $Config.errorTracking.autoRecord
        }
    }
    
    foreach ($configName in $componentConfigs.Keys) {
        $configPath = Join-Path $ProjectRoot $Config.paths.config $configName
        if (-not (Test-Path $configPath) -or $Force) {
            $componentConfigs[$configName] | ConvertTo-Json -Depth 4 | Out-File -FilePath $configPath -Encoding UTF8
            Write-WorkflowLog "設定ファイルを作成: $configName" "INFO"
        }
    }
    
    # スクリプトファイルの存在確認
    $coreScripts = @{
        "lean-proof-workflow.ps1" = Join-Path $ProjectRoot $Config.paths.core
        "auto-commit-hooks.ps1" = Join-Path $ProjectRoot $Config.paths.automation
        "error-fix-recorder.ps1" = Join-Path $ProjectRoot $Config.paths.errorTracking
        "progress-reporter.ps1" = Join-Path $ProjectRoot $Config.paths.reporting
        "auto-push-manager.ps1" = Join-Path $ProjectRoot $Config.paths.github
        "difficulty-tagger.ps1" = Join-Path $ProjectRoot $Config.paths.tagging
    }
    
    $missingScripts = @()
    foreach ($script in $coreScripts.Keys) {
        $scriptPath = Join-Path $coreScripts[$script] $script
        if (-not (Test-Path $scriptPath)) {
            $missingScripts += $script
        }
    }
    
    if ($missingScripts.Count -gt 0) {
        Write-WorkflowLog "警告: 次のコアスクリプトが見つかりません: $($missingScripts -join ', ')" "WARNING"
    } else {
        Write-WorkflowLog "全てのコアスクリプトを確認しました" "SUCCESS"
    }
    
    # Gitフック設定（オプション）
    if ($Config.git.autoCommit.enabled) {
        Setup-GitHooks $Config
    }
    
    # 初期レポート生成
    if ($Config.reporting.daily.enabled) {
        Write-WorkflowLog "初期レポートを生成中..." "INFO"
        try {
            $reportScript = Join-Path $ProjectRoot $Config.paths.reporting "progress-reporter.ps1"
            if (Test-Path $reportScript) {
                & $reportScript -ReportType daily
                Write-WorkflowLog "初期レポートを生成しました" "SUCCESS"
            }
        } catch {
            Write-WorkflowLog "初期レポート生成に失敗: $($_.Exception.Message)" "WARNING"
        }
    }
    
    # メタデータ初期化
    Update-ConfigMetadata $Config
    
    Write-WorkflowLog "ワークフロー初期化が完了しました" "SUCCESS"
    return $true
}

# Gitフック設定
function Setup-GitHooks {
    param($Config)
    
    if (-not (Test-Path ".git")) {
        Write-WorkflowLog "Gitリポジトリではありません。フック設定をスキップします" "WARNING"
        return
    }
    
    Write-WorkflowLog "Gitフックを設定中..." "INFO"
    
    $hooksDir = ".git\hooks"
    if (-not (Test-Path $hooksDir)) {
        New-Item -Path $hooksDir -ItemType Directory -Force | Out-Null
    }
    
    # pre-commit フック
    $preCommitHook = @"
#!/bin/sh
# Lean Proof Workflow - Pre-commit Hook
powershell.exe -ExecutionPolicy Bypass -File "$WorkflowRoot\automation\auto-commit-hooks.ps1" -ProofFile "`$1"
"@
    
    $preCommitPath = Join-Path $hooksDir "pre-commit"
    $preCommitHook | Out-File -FilePath $preCommitPath -Encoding UTF8
    
    # post-commit フック
    $postCommitHook = @"
#!/bin/sh
# Lean Proof Workflow - Post-commit Hook
powershell.exe -ExecutionPolicy Bypass -File "$WorkflowRoot\reporting\progress-reporter.ps1" -ReportType daily -AutoCommit
"@
    
    $postCommitPath = Join-Path $hooksDir "post-commit"
    $postCommitHook | Out-File -FilePath $postCommitPath -Encoding UTF8
    
    Write-WorkflowLog "Gitフックを設定しました" "SUCCESS"
}

# システムステータス確認
function Get-SystemStatus {
    param($Config)
    
    Write-Host "`n🚀 Lean証明ワークフローシステム ステータス" -ForegroundColor Cyan
    Write-Host "=" * 60
    
    # 基本情報
    Write-Host "`n📋 プロジェクト情報:" -ForegroundColor White
    Write-Host "  名前: $($Config.project.name)"
    Write-Host "  Lean: $($Config.project.leanVersion)"
    Write-Host "  Mathlib: $($Config.project.mathlibVersion)"
    Write-Host "  最終更新: $($Config.project.lastUpdated)"
    
    # 環境チェック
    Write-Host "`n🔧 環境状況:" -ForegroundColor White
    $envChecks = Test-Environment $Config
    
    foreach ($check in $envChecks.GetEnumerator()) {
        $status = if ($check.Value) { "✅" } else { "❌" }
        $color = if ($check.Value) { "Green" } else { "Red" }
        Write-Host "  $status $($check.Key)" -ForegroundColor $color
    }
    
    # コンポーネント状況
    Write-Host "`n⚙️  コンポーネント状況:" -ForegroundColor White
    $components = @{
        "自動コミット" = $Config.git.autoCommit.enabled
        "自動プッシュ" = $Config.git.autoPush.enabled
        "エラー追跡" = $Config.errorTracking.enabled
        "進捗レポート" = $Config.reporting.daily.enabled
        "難易度タグ" = $Config.difficulty.autoClassification
        "通知システム" = $Config.notifications.enabled
    }
    
    foreach ($comp in $components.GetEnumerator()) {
        $status = if ($comp.Value) { "🟢 有効" } else { "🔴 無効" }
        Write-Host "  $($comp.Key): $status"
    }
    
    # 最近のアクティビティ
    Write-Host "`n📊 最近のアクティビティ:" -ForegroundColor White
    
    # ログファイル確認
    $logFiles = @(
        (Join-Path $ProjectRoot $Config.paths.logs "workflow-$(Get-Date -Format 'yyyy-MM-dd').log"),
        (Join-Path $ProjectRoot $Config.paths.logs "github-push-$(Get-Date -Format 'yyyy-MM-dd').log"),
        (Join-Path $ProjectRoot $Config.paths.logs "error-tracker-$(Get-Date -Format 'yyyy-MM-dd').log")
    )
    
    $totalLogs = 0
    foreach ($logFile in $logFiles) {
        if (Test-Path $logFile) {
            $lineCount = (Get-Content $logFile | Measure-Object -Line).Lines
            $totalLogs += $lineCount
        }
    }
    
    Write-Host "  今日のログエントリ: $totalLogs 件"
    
    # 最近のレポート
    $reportsDir = Join-Path $ProjectRoot $Config.paths.reports
    if (Test-Path $reportsDir) {
        $recentReports = Get-ChildItem $reportsDir -Filter "*report*.md" | 
                        Sort-Object LastWriteTime -Descending | 
                        Select-Object -First 3
        
        Write-Host "  最近のレポート: $($recentReports.Count) 件"
        foreach ($report in $recentReports) {
            Write-Host "    - $($report.Name) ($($report.LastWriteTime.ToString('MM/dd HH:mm')))"
        }
    }
    
    # Git統計
    if (Test-Path ".git") {
        Write-Host "`n📊 Git統計:" -ForegroundColor White
        try {
            $commitCount = (& git log --oneline --since="1 week ago" 2>$null | Measure-Object).Count
            $currentBranch = & git branch --show-current 2>$null
            $status = & git status --porcelain 2>$null
            $uncommittedCount = if ($status) { $status.Count } else { 0 }
            
            Write-Host "  現在のブランチ: $currentBranch"
            Write-Host "  今週のコミット: $commitCount 件"
            Write-Host "  未コミット変更: $uncommittedCount 件"
        } catch {
            Write-Host "  Git情報取得エラー" -ForegroundColor Red
        }
    }
    
    Write-Host "`n" + "=" * 60
}

# 設定検証
function Test-Configuration {
    param($Config)
    
    Write-WorkflowLog "設定を検証中..." "INFO"
    
    $issues = @()
    
    # 必須設定チェック
    if (-not $Config.project.name) {
        $issues += "プロジェクト名が設定されていません"
    }
    
    if (-not $Config.project.leanVersion) {
        $issues += "Leanバージョンが設定されていません"
    }
    
    if (-not $Config.project.mathlibVersion) {
        $issues += "Mathlibバージョンが設定されていません"
    }
    
    # パス設定チェック
    foreach ($pathKey in $Config.paths.PSObject.Properties.Name) {
        $path = $Config.paths.$pathKey
        if ($path -and -not $path.StartsWith('.')) {
            $issues += "パス設定が相対パスではありません: $pathKey = $path"
        }
    }
    
    # Git設定チェック
    if ($Config.git.autoPush.enabled -and -not $Config.git.autoPush.remoteName) {
        $issues += "自動プッシュが有効ですが、リモート名が設定されていません"
    }
    
    # GitHub設定チェック
    if ($Config.github.enabled) {
        foreach ($repo in $Config.github.repositories.PSObject.Properties) {
            if (-not $repo.Value.url) {
                $issues += "GitHubリポジトリのURLが設定されていません: $($repo.Name)"
            }
        }
    }
    
    # 通知設定チェック
    if ($Config.notifications.channels.email.enabled) {
        if (-not $Config.notifications.channels.email.smtp.server) {
            $issues += "メール通知が有効ですが、SMTPサーバーが設定されていません"
        }
    }
    
    if ($Config.notifications.channels.slack.enabled) {
        if (-not $Config.notifications.channels.slack.webhook) {
            $issues += "Slack通知が有効ですが、Webhookが設定されていません"
        }
    }
    
    # 結果表示
    if ($issues.Count -eq 0) {
        Write-WorkflowLog "設定検証: 問題は見つかりませんでした" "SUCCESS"
        return $true
    } else {
        Write-WorkflowLog "設定検証: $($issues.Count) 件の問題が見つかりました" "WARNING"
        foreach ($issue in $issues) {
            Write-WorkflowLog "  - $issue" "WARNING"
        }
        return $false
    }
}

# 設定メタデータ更新
function Update-ConfigMetadata {
    param($Config)
    
    $Config.metadata.lastModified = Get-Date -Format "yyyy-MM-dd"
    $Config.metadata.environment.platform = $env:OS
    $Config.metadata.environment.architecture = $env:PROCESSOR_ARCHITECTURE
    $Config.metadata.environment.powershellVersion = $PSVersionTable.PSVersion.ToString()
    
    try {
        $Config.metadata.environment.gitVersion = (& git --version 2>$null) -replace "git version ", ""
        $Config.metadata.environment.leanVersion = (& lean --version 2>$null) -replace "Lean \(version ([^,]+).*", '$1'
        $Config.metadata.environment.lakeVersion = & lake --version 2>$null
    } catch {
        Write-WorkflowLog "バージョン情報の取得に部分的に失敗しました" "DEBUG"
    }
    
    # 設定ハッシュ計算（簡易版）
    $configString = $Config | ConvertTo-Json -Depth 10 -Compress
    $hash = [System.Security.Cryptography.MD5]::Create().ComputeHash([System.Text.Encoding]::UTF8.GetBytes($configString))
    $Config.metadata.configHash = [System.BitConverter]::ToString($hash) -replace "-", ""
    
    Write-WorkflowLog "設定メタデータを更新しました" "DEBUG"
}

# インタラクティブ設定
function Invoke-InteractiveConfiguration {
    param($Config)
    
    Write-Host "`n🔧 Leanワークフロー インタラクティブ設定" -ForegroundColor Cyan
    Write-Host "=" * 50
    
    # プロジェクト設定
    Write-Host "`n📋 プロジェクト基本設定" -ForegroundColor White
    $projectName = Read-Host "プロジェクト名 [$($Config.project.name)]"
    if ($projectName) { $Config.project.name = $projectName }
    
    $leanVersion = Read-Host "Leanバージョン [$($Config.project.leanVersion)]"
    if ($leanVersion) { $Config.project.leanVersion = $leanVersion }
    
    $mathlibVersion = Read-Host "Mathlibバージョン [$($Config.project.mathlibVersion)]"
    if ($mathlibVersion) { $Config.project.mathlibVersion = $mathlibVersion }
    
    # Git設定
    Write-Host "`n📊 Git設定" -ForegroundColor White
    $autoCommit = Read-Host "自動コミットを有効にしますか？ (y/n) [$($Config.git.autoCommit.enabled)]"
    if ($autoCommit -eq 'y' -or $autoCommit -eq 'yes') {
        $Config.git.autoCommit.enabled = $true
    } elseif ($autoCommit -eq 'n' -or $autoCommit -eq 'no') {
        $Config.git.autoCommit.enabled = $false
    }
    
    $autoPush = Read-Host "自動プッシュを有効にしますか？ (y/n) [$($Config.git.autoPush.enabled)]"
    if ($autoPush -eq 'y' -or $autoPush -eq 'yes') {
        $Config.git.autoPush.enabled = $true
        $remoteName = Read-Host "リモート名 [$($Config.git.autoPush.remoteName)]"
        if ($remoteName) { $Config.git.autoPush.remoteName = $remoteName }
    } elseif ($autoPush -eq 'n' -or $autoPush -eq 'no') {
        $Config.git.autoPush.enabled = $false
    }
    
    # レポート設定
    Write-Host "`n📊 レポート設定" -ForegroundColor White
    $dailyReport = Read-Host "日次レポートを有効にしますか？ (y/n) [$($Config.reporting.daily.enabled)]"
    if ($dailyReport -eq 'y' -or $dailyReport -eq 'yes') {
        $Config.reporting.daily.enabled = $true
    } elseif ($dailyReport -eq 'n' -or $dailyReport -eq 'no') {
        $Config.reporting.daily.enabled = $false
    }
    
    # 難易度タグ設定
    Write-Host "`n🏷️ 難易度タグ設定" -ForegroundColor White
    $autoTag = Read-Host "自動タグ付けを有効にしますか？ (y/n) [$($Config.difficulty.autoClassification)]"
    if ($autoTag -eq 'y' -or $autoTag -eq 'yes') {
        $Config.difficulty.autoClassification = $true
    } elseif ($autoTag -eq 'n' -or $autoTag -eq 'no') {
        $Config.difficulty.autoClassification = $false
    }
    
    Write-Host "`n✅ 設定が完了しました" -ForegroundColor Green
    
    return $Config
}

# ベンチマーク実行
function Invoke-SystemBenchmark {
    param($Config)
    
    Write-WorkflowLog "システムベンチマークを実行中..." "INFO"
    
    $benchmark = @{
        StartTime = Get-Date
        Tests = @{}
        Results = @{}
        System = @{
            Platform = $env:OS
            PowerShellVersion = $PSVersionTable.PSVersion.ToString()
            ProcessorCount = $env:NUMBER_OF_PROCESSORS
        }
    }
    
    # ビルド時間テスト
    Write-WorkflowLog "ビルド時間テスト..." "INFO"
    $buildStart = Get-Date
    try {
        $buildResult = & lake build 2>$null
        $buildEnd = Get-Date
        $buildTime = ($buildEnd - $buildStart).TotalSeconds
        
        $benchmark.Tests.BuildTime = @{
            Duration = $buildTime
            Success = ($LASTEXITCODE -eq 0)
            Result = if ($LASTEXITCODE -eq 0) { "成功" } else { "失敗" }
        }
        
        Write-WorkflowLog "ビルド時間: $buildTime 秒" "INFO"
    } catch {
        $benchmark.Tests.BuildTime = @{
            Duration = -1
            Success = $false
            Result = "エラー: $($_.Exception.Message)"
        }
    }
    
    # ファイルアクセス時間テスト
    Write-WorkflowLog "ファイルアクセス時間テスト..." "INFO"
    $accessStart = Get-Date
    try {
        $leanFiles = Get-ChildItem -Path $ProjectRoot -Filter "*.lean" -Recurse
        $accessEnd = Get-Date
        $accessTime = ($accessEnd - $accessStart).TotalMilliseconds
        
        $benchmark.Tests.FileAccess = @{
            Duration = $accessTime
            FileCount = $leanFiles.Count
            AveragePerFile = if ($leanFiles.Count -gt 0) { $accessTime / $leanFiles.Count } else { 0 }
        }
        
        Write-WorkflowLog "ファイルアクセス: $accessTime ms ($($leanFiles.Count) ファイル)" "INFO"
    } catch {
        $benchmark.Tests.FileAccess = @{
            Duration = -1
            Error = $_.Exception.Message
        }
    }
    
    # Git操作時間テスト
    if (Test-Path ".git") {
        Write-WorkflowLog "Git操作時間テスト..." "INFO"
        $gitStart = Get-Date
        try {
            $gitStatus = & git status 2>$null
            $gitLog = & git log --oneline -10 2>$null
            $gitEnd = Get-Date
            $gitTime = ($gitEnd - $gitStart).TotalMilliseconds
            
            $benchmark.Tests.GitOperations = @{
                Duration = $gitTime
                Success = $true
            }
            
            Write-WorkflowLog "Git操作: $gitTime ms" "INFO"
        } catch {
            $benchmark.Tests.GitOperations = @{
                Duration = -1
                Success = $false
                Error = $_.Exception.Message
            }
        }
    }
    
    # メモリ使用量測定
    $process = Get-Process -Id $PID
    $benchmark.Tests.MemoryUsage = @{
        WorkingSet = $process.WorkingSet64
        VirtualMemory = $process.VirtualMemorySize64
        PrivateMemory = $process.PrivateMemorySize64
    }
    
    $benchmark.EndTime = Get-Date
    $benchmark.TotalDuration = ($benchmark.EndTime - $benchmark.StartTime).TotalSeconds
    
    # 結果分析
    $benchmark.Results.Overall = if ($benchmark.Tests.BuildTime.Success) { "良好" } else { "要改善" }
    $benchmark.Results.Performance = if ($benchmark.Tests.BuildTime.Duration -lt 60) { "高速" } elseif ($benchmark.Tests.BuildTime.Duration -lt 180) { "普通" } else { "低速" }
    $benchmark.Results.Recommendations = @()
    
    if ($benchmark.Tests.BuildTime.Duration -gt 120) {
        $benchmark.Results.Recommendations += "ビルド時間が長いです。キャッシュの利用を検討してください。"
    }
    
    if ($benchmark.Tests.FileAccess.FileCount -gt 100) {
        $benchmark.Results.Recommendations += "ファイル数が多いです。プロジェクト構造の整理を検討してください。"
    }
    
    # レポート出力
    $reportPath = Join-Path $ProjectRoot $Config.paths.reports "benchmark-$(Get-Date -Format 'yyyy-MM-dd-HHmmss').json"
    $benchmark | ConvertTo-Json -Depth 4 | Out-File -FilePath $reportPath -Encoding UTF8
    
    Write-WorkflowLog "ベンチマーク完了: $reportPath" "SUCCESS"
    
    # 結果表示
    Write-Host "`n📊 ベンチマーク結果" -ForegroundColor Cyan
    Write-Host "総実行時間: $([math]::Round($benchmark.TotalDuration, 2)) 秒"
    Write-Host "ビルド時間: $([math]::Round($benchmark.Tests.BuildTime.Duration, 2)) 秒"
    Write-Host "パフォーマンス: $($benchmark.Results.Performance)"
    Write-Host "総合評価: $($benchmark.Results.Overall)"
    
    if ($benchmark.Results.Recommendations.Count -gt 0) {
        Write-Host "`n💡 推奨事項:"
        foreach ($rec in $benchmark.Results.Recommendations) {
            Write-Host "  - $rec"
        }
    }
    
    return $benchmark
}

# メイン実行ロジック
try {
    Write-WorkflowLog "Leanワークフロー管理システムを開始: $Action" "INFO"
    
    # 設定読み込み
    $config = Get-WorkflowConfig
    if (-not $config -and $Action -ne "init") {
        Write-WorkflowLog "設定ファイルが見つかりません。最初に 'init' を実行してください。" "ERROR"
        exit 1
    }
    
    switch ($Action) {
        "init" {
            if (-not $config) {
                Write-WorkflowLog "デフォルト設定を作成中..." "INFO"
                Copy-Item -Path $PSScriptRoot\..\config\master-config.json -Destination $ConfigPath -Force
                $config = Get-WorkflowConfig
            }
            
            if ($Interactive) {
                $config = Invoke-InteractiveConfiguration $config
                Save-WorkflowConfig $config
            }
            
            $success = Initialize-Workflow $config $Force
            if ($success) {
                Write-Host "`n🎉 Leanワークフローシステムの初期化が完了しました！" -ForegroundColor Green
                Write-Host "`n次のステップ:" -ForegroundColor Cyan
                Write-Host "1. 設定確認: .\workflow-manager.ps1 -Action status"
                Write-Host "2. 設定調整: .\workflow-manager.ps1 -Action configure -Interactive"
                Write-Host "3. システム実行: .\workflow-manager.ps1 -Action run"
            } else {
                Write-Host "❌ 初期化に失敗しました" -ForegroundColor Red
                exit 1
            }
        }
        
        "status" {
            Get-SystemStatus $config
        }
        
        "configure" {
            if ($Interactive) {
                $config = Invoke-InteractiveConfiguration $config
                Save-WorkflowConfig $config
                Write-Host "✅ 設定を更新しました" -ForegroundColor Green
            } else {
                Write-Host "設定ファイル: $ConfigPath" -ForegroundColor Cyan
                Write-Host "インタラクティブ設定: -Interactive フラグを使用してください"
            }
        }
        
        "validate" {
            $isValid = Test-Configuration $config
            if ($isValid) {
                Write-Host "✅ 設定検証: 問題ありません" -ForegroundColor Green
            } else {
                Write-Host "⚠️ 設定検証: 問題が見つかりました" -ForegroundColor Yellow
                exit 1
            }
        }
        
        "benchmark" {
            $benchmark = Invoke-SystemBenchmark $config
        }
        
        "run" {
            Write-Host "🚀 ワークフロー実行機能は今後実装予定です" -ForegroundColor Yellow
            Write-Host "現在は個別コンポーネントを直接実行してください:"
            Write-Host "- 証明完成時: .\.lean-workflow\core\lean-proof-workflow.ps1 -Action auto-commit -ProofFile <file>"
            Write-Host "- エラー記録時: .\.lean-workflow\error-tracking\error-fix-recorder.ps1 -Action record"
            Write-Host "- レポート生成: .\.lean-workflow\reporting\progress-reporter.ps1 -ReportType daily"
        }
        
        "deploy" {
            Write-Host "🚀 デプロイ機能は今後実装予定です" -ForegroundColor Yellow
        }
        
        "reset" {
            if ($Force -or (Read-Host "⚠️ 全ての設定とデータをリセットしますか？ (y/N)") -eq 'y') {
                Write-WorkflowLog "ワークフローをリセット中..." "WARNING"
                
                # 設定ファイル削除
                Remove-Item $ConfigPath -Force -ErrorAction SilentlyContinue
                
                # ログディレクトリクリア
                $logsDir = Join-Path $ProjectRoot $config.paths.logs
                if (Test-Path $logsDir) {
                    Get-ChildItem $logsDir | Remove-Item -Force -Recurse -ErrorAction SilentlyContinue
                }
                
                Write-Host "✅ リセットが完了しました" -ForegroundColor Green
                Write-Host "再初期化するには: .\workflow-manager.ps1 -Action init"
            } else {
                Write-Host "❌ リセットがキャンセルされました" -ForegroundColor Yellow
            }
        }
        
        "update" {
            Write-Host "🔄 更新機能は今後実装予定です" -ForegroundColor Yellow
        }
        
        default {
            Write-Host "不明なアクション: $Action" -ForegroundColor Red
            Write-Host "使用可能なアクション: init, status, configure, run, deploy, reset, update, validate, benchmark"
            exit 1
        }
    }
    
    Write-WorkflowLog "ワークフロー管理システム実行完了: $Action" "SUCCESS"
    
} catch {
    Write-WorkflowLog "実行中にエラーが発生しました: $($_.Exception.Message)" "ERROR"
    if ($Verbose) {
        Write-WorkflowLog "スタックトレース: $($_.ScriptStackTrace)" "DEBUG"
    }
    exit 1
}