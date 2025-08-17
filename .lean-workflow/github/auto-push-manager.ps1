# Lean証明プロジェクト GitHub自動プッシュマネージャー
# Version: 1.0.0

[CmdletBinding()]
param(
    [Parameter(Mandatory=$true)]
    [ValidateSet("push", "setup", "status", "sync", "configure-remote", "backup")]
    [string]$Action,
    
    [string]$RemoteName = "origin",
    [string]$Branch = "",
    [switch]$IncludeTags,
    [switch]$Force,
    [switch]$DryRun,
    [string]$BackupRemote = "backup",
    [ValidateSet("always", "on-success", "manual", "scheduled")]
    [string]$PushStrategy = "on-success"
)

# 設定とパス
$WorkflowRoot = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
$ProjectRoot = Split-Path -Parent (Split-Path -Parent $WorkflowRoot)
$ConfigPath = Join-Path $WorkflowRoot "config\github-config.json"
$LogsPath = Join-Path $WorkflowRoot "logs\github"

# ディレクトリ確保
@($LogsPath, (Split-Path $ConfigPath)) | ForEach-Object {
    if (-not (Test-Path $_)) {
        New-Item -Path $_ -ItemType Directory -Force | Out-Null
    }
}

# ログ関数
function Write-GitHubLog {
    param([string]$Message, [string]$Level = "INFO")
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $logEntry = "[$timestamp] [$Level] $Message"
    
    switch ($Level) {
        "ERROR" { Write-Host $logEntry -ForegroundColor Red }
        "WARNING" { Write-Host $logEntry -ForegroundColor Yellow }
        "SUCCESS" { Write-Host $logEntry -ForegroundColor Green }
        "INFO" { Write-Host $logEntry -ForegroundColor Cyan }
        default { Write-Host $logEntry -ForegroundColor White }
    }
    
    $logFile = Join-Path $LogsPath "github-push-$(Get-Date -Format 'yyyy-MM-dd').log"
    $logEntry | Out-File -FilePath $logFile -Append -Encoding UTF8
}

# GitHub設定読み込み・作成
function Get-GitHubConfig {
    if (Test-Path $ConfigPath) {
        try {
            return Get-Content $ConfigPath | ConvertFrom-Json
        } catch {
            Write-GitHubLog "設定ファイル読み込みエラー: $($_.Exception.Message)" "WARNING"
        }
    }
    
    # デフォルト設定
    $defaultConfig = @{
        Version = "1.0.0"
        RemoteRepositories = @{
            origin = @{
                URL = ""
                Type = "github"
                LastPush = ""
                PushCount = 0
            }
            backup = @{
                URL = ""
                Type = "backup"
                LastPush = ""
                PushCount = 0
            }
        }
        AutoPush = @{
            Enabled = $false
            Strategy = "on-success"
            IncludeTags = $true
            MaxRetries = 3
            RetryInterval = 30
        }
        Notifications = @{
            OnSuccess = $true
            OnFailure = $true
            SlackWebhook = ""
            EmailNotification = $false
        }
        Backup = @{
            Enabled = $true
            Frequency = "daily"
            RetentionDays = 30
        }
        Security = @{
            RequireSignedCommits = $false
            AllowForcePush = $false
            ProtectedBranches = @("main", "master")
        }
    }
    
    $defaultConfig | ConvertTo-Json -Depth 4 | Out-File -FilePath $ConfigPath -Encoding UTF8
    Write-GitHubLog "デフォルト設定ファイルを作成しました: $ConfigPath" "INFO"
    
    return $defaultConfig
}

# 設定保存
function Save-GitHubConfig {
    param($Config)
    
    try {
        $Config | ConvertTo-Json -Depth 4 | Out-File -FilePath $ConfigPath -Encoding UTF8
        Write-GitHubLog "設定を保存しました" "SUCCESS"
    } catch {
        Write-GitHubLog "設定保存エラー: $($_.Exception.Message)" "ERROR"
    }
}

# Git状態チェック
function Test-GitRepository {
    if (-not (Test-Path ".git")) {
        Write-GitHubLog "Gitリポジトリではありません" "ERROR"
        return $false
    }
    return $true
}

# リモート設定確認
function Test-RemoteRepository {
    param([string]$Remote)
    
    try {
        $remotes = & git remote -v 2>$null
        if (-not $remotes) {
            Write-GitHubLog "リモートリポジトリが設定されていません" "WARNING"
            return $false
        }
        
        $remoteExists = $remotes | Where-Object { $_ -match "^$Remote\s+" }
        if (-not $remoteExists) {
            Write-GitHubLog "リモート '$Remote' が見つかりません" "WARNING"
            return $false
        }
        
        Write-GitHubLog "リモート '$Remote' を確認しました" "INFO"
        return $true
        
    } catch {
        Write-GitHubLog "リモート確認エラー: $($_.Exception.Message)" "ERROR"
        return $false
    }
}

# プッシュ前チェック
function Test-PrePushConditions {
    param([string]$Branch)
    
    Write-GitHubLog "プッシュ前チェックを実行中..." "INFO"
    
    $checks = @{
        HasUncommittedChanges = $false
        HasCommitsToward = $false
        BuildPasses = $false
        TestsPasses = $false
        IsProtectedBranch = $false
    }
    
    try {
        # 未コミット変更チェック
        $status = & git status --porcelain 2>$null
        $checks.HasUncommittedChanges = ($status -and $status.Count -gt 0)
        
        # プッシュ対象コミット確認
        $unpushed = & git log "$RemoteName/$Branch..$Branch" --oneline 2>$null
        $checks.HasCommitsToward = ($unpushed -and $unpushed.Count -gt 0)
        
        # ビルドテスト
        Write-GitHubLog "Leanプロジェクトのビルド状態をチェック中..." "INFO"
        $buildResult = & lake build 2>$null
        $checks.BuildPasses = ($LASTEXITCODE -eq 0)
        
        # Leanファイル検証
        Write-GitHubLog "Leanファイルの検証を実行中..." "INFO"
        $leanFiles = Get-ChildItem -Path $ProjectRoot -Filter "*.lean" -Recurse | Select-Object -First 5
        $testsPassed = 0
        $testsTotal = $leanFiles.Count
        
        foreach ($file in $leanFiles) {
            $checkResult = & lake check $file.FullName 2>$null
            if ($LASTEXITCODE -eq 0) {
                $testsPassed++
            }
        }
        
        $checks.TestsPasses = ($testsTotal -eq 0) -or (($testsPassed / $testsTotal) -ge 0.8)
        
        # 保護ブランチチェック
        $config = Get-GitHubConfig
        $checks.IsProtectedBranch = $Branch -in $config.Security.ProtectedBranches
        
        Write-GitHubLog "プッシュ前チェック完了" "SUCCESS"
        return $checks
        
    } catch {
        Write-GitHubLog "プッシュ前チェックエラー: $($_.Exception.Message)" "ERROR"
        return $checks
    }
}

# GitHubプッシュ実行
function Invoke-GitHubPush {
    param(
        [string]$Remote,
        [string]$Branch,
        [bool]$IncludeTags,
        [bool]$Force,
        [bool]$DryRun
    )
    
    if (-not (Test-GitRepository)) {
        return $false
    }
    
    if (-not (Test-RemoteRepository $Remote)) {
        return $false
    }
    
    # 現在のブランチ取得
    if (-not $Branch) {
        $Branch = & git branch --show-current 2>$null
        if (-not $Branch) {
            Write-GitHubLog "現在のブランチを取得できませんでした" "ERROR"
            return $false
        }
    }
    
    Write-GitHubLog "GitHubプッシュを開始: $Remote/$Branch" "INFO"
    
    # プッシュ前チェック
    $preChecks = Test-PrePushConditions $Branch
    
    # チェック結果の評価
    $shouldProceed = $true
    
    if ($preChecks.HasUncommittedChanges) {
        Write-GitHubLog "未コミットの変更があります" "WARNING"
        if (-not $Force) {
            Write-GitHubLog "プッシュを中止します（-Force で強制実行可能）" "WARNING"
            $shouldProceed = $false
        }
    }
    
    if (-not $preChecks.HasCommitsToward) {
        Write-GitHubLog "プッシュする新しいコミットがありません" "INFO"
        return $true
    }
    
    if (-not $preChecks.BuildPasses) {
        Write-GitHubLog "ビルドに失敗しています" "WARNING"
        if (-not $Force) {
            Write-GitHubLog "プッシュを中止します（-Force で強制実行可能）" "WARNING"
            $shouldProceed = $false
        }
    }
    
    if (-not $preChecks.TestsPasses) {
        Write-GitHubLog "証明検証に失敗したファイルがあります" "WARNING"
        if (-not $Force) {
            Write-GitHubLog "プッシュを中止します（-Force で強制実行可能）" "WARNING"
            $shouldProceed = $false
        }
    }
    
    if (-not $shouldProceed) {
        return $false
    }
    
    try {
        # ドライラン表示
        if ($DryRun) {
            Write-GitHubLog "【ドライラン】プッシュコマンド:" "INFO"
            $pushCmd = "git push $Remote $Branch"
            if ($Force) { $pushCmd += " --force" }
            Write-GitHubLog "  $pushCmd" "INFO"
            
            if ($IncludeTags) {
                Write-GitHubLog "  git push $Remote --tags" "INFO"
            }
            
            Write-GitHubLog "ドライラン完了: 実際のプッシュは実行されませんでした" "SUCCESS"
            return $true
        }
        
        # 実際のプッシュ実行
        Write-GitHubLog "ブランチプッシュを実行中: $Remote $Branch" "INFO"
        
        $pushArgs = @($Remote, $Branch)
        if ($Force) {
            $pushArgs += "--force"
            Write-GitHubLog "強制プッシュを実行します" "WARNING"
        }
        
        $pushResult = & git push @pushArgs 2>&1
        if ($LASTEXITCODE -ne 0) {
            Write-GitHubLog "ブランチプッシュに失敗しました" "ERROR"
            Write-GitHubLog $pushResult "ERROR"
            return $false
        }
        
        Write-GitHubLog "ブランチプッシュ成功: $Remote/$Branch" "SUCCESS"
        
        # タグプッシュ
        if ($IncludeTags) {
            Write-GitHubLog "タグプッシュを実行中..." "INFO"
            $tagPushResult = & git push $Remote --tags 2>&1
            if ($LASTEXITCODE -eq 0) {
                Write-GitHubLog "タグプッシュ成功" "SUCCESS"
            } else {
                Write-GitHubLog "タグプッシュに失敗しました: $tagPushResult" "WARNING"
            }
        }
        
        # 統計更新
        Update-PushStatistics $Remote $Branch
        
        # 通知送信
        Send-PushNotification "success" $Remote $Branch
        
        return $true
        
    } catch {
        Write-GitHubLog "プッシュ中にエラーが発生しました: $($_.Exception.Message)" "ERROR"
        Send-PushNotification "failure" $Remote $Branch $_.Exception.Message
        return $false
    }
}

# プッシュ統計更新
function Update-PushStatistics {
    param([string]$Remote, [string]$Branch)
    
    try {
        $config = Get-GitHubConfig
        
        if (-not $config.RemoteRepositories.ContainsKey($Remote)) {
            $config.RemoteRepositories[$Remote] = @{
                URL = ""
                Type = "github"
                LastPush = ""
                PushCount = 0
            }
        }
        
        $config.RemoteRepositories[$Remote].LastPush = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        $config.RemoteRepositories[$Remote].PushCount++
        
        Save-GitHubConfig $config
        
        Write-GitHubLog "プッシュ統計を更新しました: $Remote (計 $($config.RemoteRepositories[$Remote].PushCount) 回)" "INFO"
        
    } catch {
        Write-GitHubLog "統計更新エラー: $($_.Exception.Message)" "WARNING"
    }
}

# 通知送信
function Send-PushNotification {
    param([string]$Status, [string]$Remote, [string]$Branch, [string]$Error = "")
    
    try {
        $config = Get-GitHubConfig
        
        if (-not $config.Notifications.OnSuccess -and $Status -eq "success") {
            return
        }
        
        if (-not $config.Notifications.OnFailure -and $Status -eq "failure") {
            return
        }
        
        $message = switch ($Status) {
            "success" { "✅ GitHub プッシュ成功: $Remote/$Branch" }
            "failure" { "❌ GitHub プッシュ失敗: $Remote/$Branch`nエラー: $Error" }
        }
        
        Write-GitHubLog "通知: $message" "INFO"
        
        # Slack通知（設定されている場合）
        if ($config.Notifications.SlackWebhook) {
            Write-GitHubLog "Slack通知送信機能は今後実装予定です" "INFO"
        }
        
        # メール通知（設定されている場合）
        if ($config.Notifications.EmailNotification) {
            Write-GitHubLog "メール通知送信機能は今後実装予定です" "INFO"
        }
        
    } catch {
        Write-GitHubLog "通知送信エラー: $($_.Exception.Message)" "WARNING"
    }
}

# リモートリポジトリセットアップ
function Setup-RemoteRepository {
    param([string]$Remote, [string]$URL)
    
    Write-GitHubLog "リモートリポジトリをセットアップ中: $Remote" "INFO"
    
    try {
        # 既存のリモートチェック
        $existingRemotes = & git remote -v 2>$null
        $remoteExists = $existingRemotes | Where-Object { $_ -match "^$Remote\s+" }
        
        if ($remoteExists) {
            Write-GitHubLog "リモート '$Remote' は既に存在します" "WARNING"
            $currentURL = ($remoteExists[0] -split '\s+')[1]
            Write-GitHubLog "現在のURL: $currentURL" "INFO"
            
            if ($URL -and $URL -ne $currentURL) {
                Write-GitHubLog "URL を更新中..." "INFO"
                & git remote set-url $Remote $URL 2>$null
                if ($LASTEXITCODE -eq 0) {
                    Write-GitHubLog "URL を更新しました: $URL" "SUCCESS"
                } else {
                    Write-GitHubLog "URL 更新に失敗しました" "ERROR"
                    return $false
                }
            }
        } else {
            if (-not $URL) {
                Write-GitHubLog "新しいリモートにはURLが必要です" "ERROR"
                return $false
            }
            
            Write-GitHubLog "新しいリモートを追加中..." "INFO"
            & git remote add $Remote $URL 2>$null
            if ($LASTEXITCODE -eq 0) {
                Write-GitHubLog "リモートを追加しました: $Remote -> $URL" "SUCCESS"
            } else {
                Write-GitHubLog "リモート追加に失敗しました" "ERROR"
                return $false
            }
        }
        
        # 接続テスト
        Write-GitHubLog "リモート接続をテスト中..." "INFO"
        $fetchResult = & git fetch $Remote 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-GitHubLog "リモート接続成功" "SUCCESS"
            
            # 設定更新
            $config = Get-GitHubConfig
            if (-not $config.RemoteRepositories.ContainsKey($Remote)) {
                $config.RemoteRepositories[$Remote] = @{}
            }
            $config.RemoteRepositories[$Remote].URL = $URL
            $config.RemoteRepositories[$Remote].Type = "github"
            Save-GitHubConfig $config
            
            return $true
        } else {
            Write-GitHubLog "リモート接続に失敗しました: $fetchResult" "ERROR"
            return $false
        }
        
    } catch {
        Write-GitHubLog "リモートセットアップエラー: $($_.Exception.Message)" "ERROR"
        return $false
    }
}

# 同期実行
function Invoke-GitSync {
    param([string]$Remote, [string]$Branch)
    
    Write-GitHubLog "Git同期を開始: $Remote/$Branch" "INFO"
    
    if (-not (Test-GitRepository)) {
        return $false
    }
    
    try {
        # フェッチ
        Write-GitHubLog "リモートからフェッチ中..." "INFO"
        $fetchResult = & git fetch $Remote 2>&1
        if ($LASTEXITCODE -ne 0) {
            Write-GitHubLog "フェッチに失敗しました: $fetchResult" "ERROR"
            return $false
        }
        
        # ローカルとリモートの差分チェック
        $behind = & git rev-list --count HEAD..$Remote/$Branch 2>$null
        $ahead = & git rev-list --count $Remote/$Branch..HEAD 2>$null
        
        Write-GitHubLog "同期状態: ローカルが $ahead コミット先行, $behind コミット後方" "INFO"
        
        if ([int]$behind -gt 0) {
            Write-GitHubLog "リモートに新しいコミットがあります" "INFO"
            Write-GitHubLog "git pull を実行して同期してください" "INFO"
        }
        
        if ([int]$ahead -gt 0) {
            Write-GitHubLog "ローカルに新しいコミットがあります" "INFO"
            Write-GitHubLog "プッシュすることを推奨します" "INFO"
            
            # 自動プッシュ設定チェック
            $config = Get-GitHubConfig
            if ($config.AutoPush.Enabled -and $config.AutoPush.Strategy -eq "always") {
                Write-GitHubLog "自動プッシュを実行します" "INFO"
                return Invoke-GitHubPush $Remote $Branch $config.AutoPush.IncludeTags $false $false
            }
        }
        
        if ([int]$behind -eq 0 -and [int]$ahead -eq 0) {
            Write-GitHubLog "ローカルとリモートは同期されています" "SUCCESS"
        }
        
        return $true
        
    } catch {
        Write-GitHubLog "同期中にエラーが発生しました: $($_.Exception.Message)" "ERROR"
        return $false
    }
}

# ステータス表示
function Show-GitHubStatus {
    Write-Host "`n📊 GitHub自動プッシュシステム ステータス" -ForegroundColor Cyan
    Write-Host "=" * 50
    
    # Git状態
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
    
    # リモート状況
    Write-Host "`n🌐 リモートリポジトリ:"
    try {
        $remotes = & git remote -v 2>$null
        if ($remotes) {
            $remoteList = $remotes | ForEach-Object {
                $parts = $_ -split '\s+'
                "$($parts[0]) -> $($parts[1])"
            } | Sort-Object -Unique
            
            foreach ($remote in $remoteList) {
                Write-Host "  📡 $remote" -ForegroundColor Green
            }
        } else {
            Write-Host "  ❌ リモートリポジトリが設定されていません" -ForegroundColor Red
        }
    } catch {
        Write-Host "  ❌ リモート情報取得エラー" -ForegroundColor Red
    }
    
    # 設定状況
    Write-Host "`n⚙️  設定状況:"
    if (Test-Path $ConfigPath) {
        Write-Host "  ✅ 設定ファイル: 存在" -ForegroundColor Green
        try {
            $config = Get-GitHubConfig
            Write-Host "  🚀 自動プッシュ: $(if($config.AutoPush.Enabled){'有効'}else{'無効'})"
            Write-Host "  📊 戦略: $($config.AutoPush.Strategy)"
            Write-Host "  🏷️  タグ込み: $(if($config.AutoPush.IncludeTags){'有効'}else{'無効'})"
        } catch {
            Write-Host "  ⚠️  設定読み込みエラー" -ForegroundColor Yellow
        }
    } else {
        Write-Host "  ❌ 設定ファイル: 未作成" -ForegroundColor Red
    }
    
    # 最近のログ
    Write-Host "`n📝 最近のログ:"
    $logFile = Join-Path $LogsPath "github-push-$(Get-Date -Format 'yyyy-MM-dd').log"
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

# バックアップ実行
function Invoke-GitHubBackup {
    param([string]$BackupRemote)
    
    Write-GitHubLog "GitHubバックアップを開始: $BackupRemote" "INFO"
    
    $config = Get-GitHubConfig
    
    # バックアップリモートの設定チェック
    if (-not (Test-RemoteRepository $BackupRemote)) {
        Write-GitHubLog "バックアップリモートが設定されていません: $BackupRemote" "WARNING"
        return $false
    }
    
    try {
        # 全ブランチのバックアップ
        $branches = & git branch -r 2>$null | Where-Object { $_ -notmatch 'HEAD' -and $_ -notmatch $BackupRemote }
        
        foreach ($branch in $branches) {
            $cleanBranch = $branch.Trim() -replace '^origin/', ''
            Write-GitHubLog "ブランチをバックアップ中: $cleanBranch" "INFO"
            
            $pushResult = & git push $BackupRemote $cleanBranch 2>&1
            if ($LASTEXITCODE -eq 0) {
                Write-GitHubLog "ブランチバックアップ成功: $cleanBranch" "SUCCESS"
            } else {
                Write-GitHubLog "ブランチバックアップ失敗: $cleanBranch - $pushResult" "WARNING"
            }
        }
        
        # タグのバックアップ
        Write-GitHubLog "タグをバックアップ中..." "INFO"
        $tagPushResult = & git push $BackupRemote --tags 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-GitHubLog "タグバックアップ成功" "SUCCESS"
        } else {
            Write-GitHubLog "タグバックアップ失敗: $tagPushResult" "WARNING"
        }
        
        # バックアップ統計更新
        Update-PushStatistics $BackupRemote "backup"
        
        Write-GitHubLog "GitHubバックアップ完了" "SUCCESS"
        return $true
        
    } catch {
        Write-GitHubLog "バックアップ中にエラーが発生しました: $($_.Exception.Message)" "ERROR"
        return $false
    }
}

# メイン実行ロジック
switch ($Action) {
    "push" {
        Write-GitHubLog "GitHub自動プッシュを開始..." "INFO"
        $success = Invoke-GitHubPush $RemoteName $Branch $IncludeTags $Force $DryRun
        if ($success) {
            Write-Host "🚀 GitHubプッシュが完了しました!" -ForegroundColor Green
        } else {
            Write-Host "❌ GitHubプッシュに失敗しました" -ForegroundColor Red
            exit 1
        }
    }
    
    "setup" {
        Write-Host "🔧 GitHub自動プッシュシステムをセットアップ中..." -ForegroundColor Cyan
        $config = Get-GitHubConfig
        
        Write-Host "基本設定を作成しました: $ConfigPath" -ForegroundColor Green
        Write-Host "`n次のステップ:"
        Write-Host "1. リモートリポジトリを設定: .\auto-push-manager.ps1 -Action configure-remote -RemoteName origin"
        Write-Host "2. 自動プッシュを有効化: 設定ファイルを編集"
        Write-Host "3. 動作確認: .\auto-push-manager.ps1 -Action status"
    }
    
    "status" {
        Show-GitHubStatus
    }
    
    "sync" {
        Write-GitHubLog "Git同期を開始..." "INFO"
        $success = Invoke-GitSync $RemoteName $Branch
        if ($success) {
            Write-Host "🔄 Git同期が完了しました!" -ForegroundColor Green
        } else {
            Write-Host "❌ Git同期に失敗しました" -ForegroundColor Red
            exit 1
        }
    }
    
    "configure-remote" {
        Write-Host "リモートリポジトリURL を入力してください:" -ForegroundColor Cyan
        $remoteURL = Read-Host "URL"
        
        if ($remoteURL) {
            $success = Setup-RemoteRepository $RemoteName $remoteURL
            if ($success) {
                Write-Host "✅ リモートリポジトリを設定しました: $RemoteName" -ForegroundColor Green
            } else {
                Write-Host "❌ リモートリポジトリの設定に失敗しました" -ForegroundColor Red
                exit 1
            }
        } else {
            Write-Host "URLが入力されませんでした" -ForegroundColor Yellow
        }
    }
    
    "backup" {
        Write-GitHubLog "GitHubバックアップを開始..." "INFO"
        $success = Invoke-GitHubBackup $BackupRemote
        if ($success) {
            Write-Host "💾 GitHubバックアップが完了しました!" -ForegroundColor Green
        } else {
            Write-Host "❌ GitHubバックアップに失敗しました" -ForegroundColor Red
            exit 1
        }
    }
    
    default {
        Write-Host "不明なアクション: $Action" -ForegroundColor Red
        Write-Host "使用可能なアクション: push, setup, status, sync, configure-remote, backup"
        exit 1
    }
}