# Lean証明プロジェクト進捗レポート生成システム
# Version: 1.0.0

[CmdletBinding()]
param(
    [Parameter(Mandatory=$true)]
    [ValidateSet("daily", "weekly", "monthly", "custom")]
    [string]$ReportType,
    
    [datetime]$StartDate = (Get-Date).AddDays(-1),
    [datetime]$EndDate = (Get-Date),
    [string]$OutputPath = "",
    [switch]$IncludeCharts,
    [switch]$SendEmail,
    [string]$EmailTo = "",
    [switch]$AutoCommit
)

# 設定とパス
$WorkflowRoot = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
$ProjectRoot = Split-Path -Parent (Split-Path -Parent $WorkflowRoot)
$ReportsPath = Join-Path $WorkflowRoot "reports"
$TemplatesPath = Join-Path $WorkflowRoot "templates"
$ConfigPath = Join-Path $WorkflowRoot "config\workflow-config.json"

# ディレクトリ確保
@($ReportsPath, $TemplatesPath) | ForEach-Object {
    if (-not (Test-Path $_)) {
        New-Item -Path $_ -ItemType Directory -Force | Out-Null
    }
}

# ログ関数
function Write-ReportLog {
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
}

# 設定読み込み
function Get-WorkflowConfig {
    if (Test-Path $ConfigPath) {
        try {
            return Get-Content $ConfigPath | ConvertFrom-Json
        } catch {
            Write-ReportLog "設定ファイル読み込みエラー: $($_.Exception.Message)" "WARNING"
        }
    }
    
    # デフォルト設定
    return @{
        Reports = @{
            IncludeGitStats = $true
            IncludeProofStats = $true
            IncludeErrorAnalysis = $true
            IncludePerformance = $true
        }
        Email = @{
            SMTPServer = ""
            Port = 587
            UseSSL = $true
            From = ""
        }
    }
}

# Git統計収集
function Get-GitStatistics {
    param([datetime]$Start, [datetime]$End)
    
    Write-ReportLog "Git統計を収集中..." "INFO"
    
    $since = $Start.ToString("yyyy-MM-dd")
    $until = $End.ToString("yyyy-MM-dd")
    
    try {
        # コミット統計
        $commits = & git log --since=$since --until=$until --oneline 2>$null
        $commitCount = if ($commits) { ($commits | Measure-Object).Count } else { 0 }
        
        # 変更されたファイル統計
        $changedFiles = & git log --since=$since --until=$until --name-only --pretty=format: 2>$null | 
                       Where-Object { $_ -and $_ -like "*.lean" } | 
                       Sort-Object -Unique
        
        # 追加・削除行数
        $diffStats = & git log --since=$since --until=$until --numstat --pretty=format: 2>$null
        $additions = 0
        $deletions = 0
        
        if ($diffStats) {
            foreach ($line in $diffStats) {
                if ($line -match '(\d+)\s+(\d+)') {
                    $additions += [int]$matches[1]
                    $deletions += [int]$matches[2]
                }
            }
        }
        
        # ブランチ情報
        $currentBranch = & git branch --show-current 2>$null
        $totalBranches = (& git branch -a 2>$null | Measure-Object).Count
        
        # 最新コミット情報
        $latestCommit = & git log -1 --pretty=format:"%h|%an|%ad|%s" --date=short 2>$null
        $commitInfo = if ($latestCommit) {
            $parts = $latestCommit -split '\|'
            @{
                Hash = $parts[0]
                Author = $parts[1]
                Date = $parts[2]
                Message = $parts[3]
            }
        } else { $null }
        
        return @{
            CommitCount = $commitCount
            ChangedLeanFiles = ($changedFiles | Measure-Object).Count
            ChangedFiles = $changedFiles
            LinesAdded = $additions
            LinesDeleted = $deletions
            NetChange = $additions - $deletions
            CurrentBranch = $currentBranch
            TotalBranches = $totalBranches
            LatestCommit = $commitInfo
            Period = @{
                Start = $since
                End = $until
            }
        }
    } catch {
        Write-ReportLog "Git統計収集エラー: $($_.Exception.Message)" "ERROR"
        return @{}
    }
}

# 証明統計収集
function Get-ProofStatistics {
    param([datetime]$Start, [datetime]$End)
    
    Write-ReportLog "証明統計を収集中..." "INFO"
    
    $stats = @{
        TotalLeanFiles = 0
        VerifiedProofs = 0
        FailedProofs = 0
        ProofsByDifficulty = @{
            beginner = 0
            intermediate = 0
            advanced = 0
            expert = 0
            research = 0
        }
        ProofsByCategory = @{}
        AverageFileSize = 0
        TotalLines = 0
        CompletionRate = 0
        NewProofsInPeriod = 0
        RecentProofs = @()
    }
    
    try {
        # 全Leanファイルを取得
        $leanFiles = Get-ChildItem -Path $ProjectRoot -Filter "*.lean" -Recurse
        $stats.TotalLeanFiles = $leanFiles.Count
        
        $totalSize = 0
        $totalLines = 0
        
        foreach ($file in $leanFiles) {
            $content = Get-Content $file.FullName -Raw -ErrorAction SilentlyContinue
            if (-not $content) { continue }
            
            $lines = ($content -split "`n").Count
            $totalLines += $lines
            $totalSize += $file.Length
            
            # 証明検証
            $verification = Test-LeanFile $file.FullName
            if ($verification.Success) {
                $stats.VerifiedProofs++
            } else {
                $stats.FailedProofs++
            }
            
            # 難易度分析
            $difficulty = Get-ProofDifficulty $file.FullName
            $stats.ProofsByDifficulty[$difficulty]++
            
            # カテゴリ分析
            $category = Get-ProofCategory $file.FullName
            if ($stats.ProofsByCategory.ContainsKey($category)) {
                $stats.ProofsByCategory[$category]++
            } else {
                $stats.ProofsByCategory[$category] = 1
            }
            
            # 期間内の新規証明チェック
            if ($file.CreationTime -ge $Start -and $file.CreationTime -le $End) {
                $stats.NewProofsInPeriod++
                $stats.RecentProofs += @{
                    Name = $file.Name
                    Path = $file.FullName
                    Created = $file.CreationTime
                    Size = $file.Length
                    Lines = $lines
                    Difficulty = $difficulty
                    Category = $category
                }
            }
        }
        
        $stats.TotalLines = $totalLines
        $stats.AverageFileSize = if ($stats.TotalLeanFiles -gt 0) { 
            [math]::Round($totalSize / $stats.TotalLeanFiles / 1KB, 2) 
        } else { 0 }
        
        $stats.CompletionRate = if ($stats.TotalLeanFiles -gt 0) {
            [math]::Round(($stats.VerifiedProofs / $stats.TotalLeanFiles) * 100, 1)
        } else { 0 }
        
        # 最新の証明を時間順でソート
        $stats.RecentProofs = $stats.RecentProofs | Sort-Object Created -Descending | Select-Object -First 10
        
        return $stats
        
    } catch {
        Write-ReportLog "証明統計収集エラー: $($_.Exception.Message)" "ERROR"
        return $stats
    }
}

# Leanファイルテスト
function Test-LeanFile {
    param([string]$FilePath)
    
    try {
        $result = & lake check $FilePath 2>&1
        return @{
            Success = ($LASTEXITCODE -eq 0)
            Output = $result
            Errors = if ($LASTEXITCODE -ne 0) { $result } else { @() }
        }
    } catch {
        return @{
            Success = $false
            Output = ""
            Errors = @("Failed to execute lake check: $($_.Exception.Message)")
        }
    }
}

# 証明難易度判定
function Get-ProofDifficulty {
    param([string]$FilePath)
    
    if (-not (Test-Path $FilePath)) { return "unknown" }
    
    try {
        $content = Get-Content $FilePath -Raw
        $lines = ($content -split "`n").Count
        
        # 複雑性指標
        $theorems = ([regex]::Matches($content, "theorem|lemma|def")).Count
        $tactics = ([regex]::Matches($content, "simp|rw|apply|exact|intro|cases|induction")).Count
        $complexTactics = ([regex]::Matches($content, "simp_all|omega|decide|aesop|polyrith")).Count
        $imports = ([regex]::Matches($content, "import")).Count
        
        $score = ($lines * 0.1) + ($theorems * 2) + ($tactics * 0.5) + ($complexTactics * 3) + ($imports * 0.3)
        
        switch ($score) {
            {$_ -le 10} { return "beginner" }
            {$_ -le 25} { return "intermediate" }
            {$_ -le 50} { return "advanced" }
            {$_ -le 100} { return "expert" }
            default { return "research" }
        }
    } catch {
        return "unknown"
    }
}

# 証明カテゴリ判定
function Get-ProofCategory {
    param([string]$FilePath)
    
    $fileName = [System.IO.Path]::GetFileNameWithoutExtension($FilePath)
    $content = Get-Content $FilePath -Raw -ErrorAction SilentlyContinue
    
    if (-not $content) { return "other" }
    
    # キーワードベースの分類
    $categories = @{
        "number_theory" = @("prime", "gcd", "lcm", "divisible", "modular", "number")
        "algebra" = @("group", "ring", "field", "module", "linear", "polynomial")
        "analysis" = @("continuous", "derivative", "integral", "limit", "convergence")
        "geometry" = @("triangle", "circle", "angle", "distance", "coordinate")
        "logic" = @("proposition", "predicate", "quantifier", "proof", "logic")
        "set_theory" = @("set", "union", "intersection", "subset", "cardinality")
        "combinatorics" = @("permutation", "combination", "factorial", "fibonacci")
        "topology" = @("open", "closed", "compact", "connected", "homeomorphism")
    }
    
    foreach ($category in $categories.Keys) {
        foreach ($keyword in $categories[$category]) {
            if ($content -match $keyword -or $fileName -match $keyword) {
                return $category
            }
        }
    }
    
    return "other"
}

# パフォーマンス統計収集
function Get-PerformanceStatistics {
    param([datetime]$Start, [datetime]$End)
    
    Write-ReportLog "パフォーマンス統計を収集中..." "INFO"
    
    $stats = @{
        BuildTimes = @()
        AverageBuildTime = 0
        ErrorRate = 0
        TestSuccessRate = 0
        CacheHitRate = 0
        ResourceUsage = @{
            PeakMemoryMB = 0
            AverageCPUPercent = 0
        }
    }
    
    try {
        # ビルド時間測定
        $buildStart = Get-Date
        $buildResult = & lake build 2>$null
        $buildEnd = Get-Date
        $buildTime = ($buildEnd - $buildStart).TotalSeconds
        
        $stats.BuildTimes += $buildTime
        $stats.AverageBuildTime = $buildTime
        
        # エラー率計算（簡易版）
        $totalFiles = (Get-ChildItem -Path $ProjectRoot -Filter "*.lean" -Recurse).Count
        $failedFiles = 0
        
        Get-ChildItem -Path $ProjectRoot -Filter "*.lean" -Recurse | ForEach-Object {
            $test = Test-LeanFile $_.FullName
            if (-not $test.Success) {
                $failedFiles++
            }
        }
        
        $stats.ErrorRate = if ($totalFiles -gt 0) { 
            [math]::Round(($failedFiles / $totalFiles) * 100, 1) 
        } else { 0 }
        
        $stats.TestSuccessRate = 100 - $stats.ErrorRate
        
        return $stats
        
    } catch {
        Write-ReportLog "パフォーマンス統計収集エラー: $($_.Exception.Message)" "ERROR"
        return $stats
    }
}

# エラー分析統計
function Get-ErrorAnalysis {
    param([datetime]$Start, [datetime]$End)
    
    Write-ReportLog "エラー分析を実行中..." "INFO"
    
    $errorLogsPath = Join-Path $WorkflowRoot "error-tracking\logs"
    
    $analysis = @{
        TotalErrors = 0
        ErrorsByType = @{}
        ErrorsByCategory = @{}
        RecentErrors = @()
        ErrorTrend = @()
        AverageResolutionTime = 0
    }
    
    if (-not (Test-Path $errorLogsPath)) {
        return $analysis
    }
    
    try {
        # エラーログファイルを検索
        $logFiles = Get-ChildItem -Path $errorLogsPath -Filter "error-fixes-*.json"
        
        $allErrors = @()
        foreach ($logFile in $logFiles) {
            try {
                $errors = Get-Content $logFile.FullName | ConvertFrom-Json
                $filteredErrors = $errors | Where-Object {
                    $errorDate = [datetime]$_.Timestamp
                    $errorDate -ge $Start -and $errorDate -le $End
                }
                $allErrors += $filteredErrors
            } catch {
                Write-ReportLog "エラーログ読み込み失敗: $($logFile.Name)" "WARNING"
            }
        }
        
        $analysis.TotalErrors = $allErrors.Count
        
        if ($allErrors.Count -gt 0) {
            # タイプ別分類
            $analysis.ErrorsByType = $allErrors | Group-Object ErrorType | ForEach-Object {
                @{
                    Type = $_.Name
                    Count = $_.Count
                    Percentage = [math]::Round(($_.Count / $allErrors.Count) * 100, 1)
                }
            }
            
            # カテゴリ別分類
            $analysis.ErrorsByCategory = $allErrors | Group-Object Category | ForEach-Object {
                @{
                    Category = $_.Name
                    Count = $_.Count
                    Percentage = [math]::Round(($_.Count / $allErrors.Count) * 100, 1)
                }
            }
            
            # 最新エラー
            $analysis.RecentErrors = $allErrors | Sort-Object Timestamp -Descending | Select-Object -First 5
            
            # 平均解決時間
            $timeEntries = $allErrors | Where-Object { $_.TimeSpentMinutes -gt 0 }
            if ($timeEntries.Count -gt 0) {
                $analysis.AverageResolutionTime = [math]::Round(($timeEntries.TimeSpentMinutes | Measure-Object -Average).Average, 1)
            }
        }
        
        return $analysis
        
    } catch {
        Write-ReportLog "エラー分析実行エラー: $($_.Exception.Message)" "ERROR"
        return $analysis
    }
}

# チャート生成（ASCII版）
function New-ASCIIChart {
    param(
        [hashtable]$Data,
        [string]$Title = "Chart",
        [string]$Type = "bar"
    )
    
    if ($Type -eq "bar" -and $Data.Count -gt 0) {
        $maxValue = ($Data.Values | Measure-Object -Maximum).Maximum
        $chart = "`n$Title`n" + ("=" * $Title.Length) + "`n"
        
        foreach ($item in $Data.GetEnumerator()) {
            $barLength = if ($maxValue -gt 0) { [math]::Floor(($item.Value / $maxValue) * 30) } else { 0 }
            $bar = "█" * $barLength
            $chart += "{0,-15} {1} {2}`n" -f $item.Key, $bar, $item.Value
        }
        
        return $chart
    }
    
    return ""
}

# レポート生成メイン機能
function New-ProgressReport {
    param([string]$Type, [datetime]$Start, [datetime]$End, [string]$OutputPath)
    
    Write-ReportLog "$Type レポートを生成中..." "INFO"
    
    # 期間設定
    switch ($Type) {
        "daily" { 
            $Start = (Get-Date).Date
            $End = (Get-Date).Date.AddDays(1).AddSeconds(-1)
        }
        "weekly" {
            $Start = (Get-Date).Date.AddDays(-(Get-Date).DayOfWeek.value__)
            $End = $Start.AddDays(7).AddSeconds(-1)
        }
        "monthly" {
            $Start = Get-Date -Day 1
            $End = $Start.AddMonths(1).AddSeconds(-1)
        }
    }
    
    # 統計データ収集
    $gitStats = Get-GitStatistics $Start $End
    $proofStats = Get-ProofStatistics $Start $End
    $performanceStats = Get-PerformanceStatistics $Start $End
    $errorAnalysis = Get-ErrorAnalysis $Start $End
    
    # レポートファイル名生成
    if (-not $OutputPath) {
        $dateFormat = switch ($Type) {
            "daily" { "yyyy-MM-dd" }
            "weekly" { "yyyy-'W'ww" }
            "monthly" { "yyyy-MM" }
            default { "yyyy-MM-dd" }
        }
        $dateString = Get-Date -Format $dateFormat
        $OutputPath = Join-Path $ReportsPath "$Type-report-$dateString.md"
    }
    
    # レポート内容生成
    $report = Generate-ReportContent $Type $gitStats $proofStats $performanceStats $errorAnalysis $Start $End
    
    # レポートファイル保存
    $report | Out-File -FilePath $OutputPath -Encoding UTF8
    
    Write-ReportLog "レポートを生成しました: $OutputPath" "SUCCESS"
    
    return $OutputPath
}

# レポート内容生成
function Generate-ReportContent {
    param($Type, $GitStats, $ProofStats, $PerformanceStats, $ErrorAnalysis, $Start, $End)
    
    $period = switch ($Type) {
        "daily" { "本日" }
        "weekly" { "今週" }
        "monthly" { "今月" }
        default { "$($Start.ToString('yyyy-MM-dd')) 〜 $($End.ToString('yyyy-MM-dd'))" }
    }
    
    return @"
# Lean証明プロジェクト $Type レポート

**生成日時**: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")  
**対象期間**: $period  
**プロジェクト**: $(Split-Path $ProjectRoot -Leaf)

---

## 📊 サマリー

| 指標 | 値 |
|------|------|
| 🔄 コミット数 | $($GitStats.CommitCount) |
| 📄 変更Leanファイル | $($GitStats.ChangedLeanFiles) |
| ✅ 検証済み証明 | $($ProofStats.VerifiedProofs) |
| ❌ 失敗証明 | $($ProofStats.FailedProofs) |
| 📈 完成率 | $($ProofStats.CompletionRate)% |
| 🆕 新規証明 | $($ProofStats.NewProofsInPeriod) |
| 🐛 エラー発生 | $($ErrorAnalysis.TotalErrors) |
| ⚡ ビルド時間 | $([math]::Round($PerformanceStats.AverageBuildTime, 1))秒 |

---

## 📈 Git活動統計

### コミット活動
- **総コミット数**: $($GitStats.CommitCount)
- **変更行数**: +$($GitStats.LinesAdded) / -$($GitStats.LinesDeleted)
- **正味変更**: $($GitStats.NetChange) 行
- **現在のブランチ**: $($GitStats.CurrentBranch)

$(if ($GitStats.LatestCommit) {
"### 最新コミット
- **ハッシュ**: $($GitStats.LatestCommit.Hash)
- **作成者**: $($GitStats.LatestCommit.Author)
- **日時**: $($GitStats.LatestCommit.Date)
- **メッセージ**: $($GitStats.LatestCommit.Message)"
})

### 変更されたファイル
$(if ($GitStats.ChangedFiles.Count -gt 0) {
foreach ($file in ($GitStats.ChangedFiles | Select-Object -First 10)) { "- $file" }
if ($GitStats.ChangedFiles.Count -gt 10) { "- ... および他 $($GitStats.ChangedFiles.Count - 10) ファイル" }
} else { "変更されたLeanファイルはありません" })

---

## 🎯 証明統計

### 全体統計
- **総Leanファイル数**: $($ProofStats.TotalLeanFiles)
- **総行数**: $($ProofStats.TotalLines.ToString("N0"))
- **平均ファイルサイズ**: $($ProofStats.AverageFileSize) KB
- **検証成功率**: $($ProofStats.CompletionRate)%

### 難易度別分布
$(foreach ($difficulty in $ProofStats.ProofsByDifficulty.GetEnumerator()) {
"- **$($difficulty.Key)**: $($difficulty.Value) ファイル"
})

### カテゴリ別分布
$(foreach ($category in ($ProofStats.ProofsByCategory.GetEnumerator() | Sort-Object Value -Descending | Select-Object -First 5)) {
"- **$($category.Key)**: $($category.Value) ファイル"
})

$(if ($ProofStats.RecentProofs.Count -gt 0) {
"### 新規作成された証明
$(foreach ($proof in $ProofStats.RecentProofs) {
"- **$($proof.Name)** ($($proof.Difficulty)) - $($proof.Lines) 行 - $($proof.Created.ToString('MM/dd HH:mm'))"
})
"
})

---

## ⚡ パフォーマンス分析

### ビルド性能
- **平均ビルド時間**: $([math]::Round($PerformanceStats.AverageBuildTime, 1)) 秒
- **テスト成功率**: $($PerformanceStats.TestSuccessRate)%
- **エラー率**: $($PerformanceStats.ErrorRate)%

### 品質指標
$(if ($PerformanceStats.TestSuccessRate -ge 90) { "✅ **優秀**: 高い成功率を維持しています" }
elseif ($PerformanceStats.TestSuccessRate -ge 70) { "⚠️ **注意**: 成功率の改善が推奨されます" }
else { "🚨 **要改善**: 成功率が低下しています" })

---

## 🐛 エラー分析

### エラー統計
- **総エラー数**: $($ErrorAnalysis.TotalErrors)
- **平均解決時間**: $($ErrorAnalysis.AverageResolutionTime) 分

$(if ($ErrorAnalysis.ErrorsByType.Count -gt 0) {
"### エラータイプ別
$(foreach ($error in ($ErrorAnalysis.ErrorsByType | Sort-Object Count -Descending)) {
"- **$($error.Type)**: $($error.Count) 件 ($($error.Percentage)%)"
})
"
})

$(if ($ErrorAnalysis.ErrorsByCategory.Count -gt 0) {
"### エラーカテゴリ別
$(foreach ($error in ($ErrorAnalysis.ErrorsByCategory | Sort-Object Count -Descending)) {
"- **$($error.Category)**: $($error.Count) 件 ($($error.Percentage)%)"
})
"
})

$(if ($ErrorAnalysis.RecentErrors.Count -gt 0) {
"### 最近のエラー
$(foreach ($error in $ErrorAnalysis.RecentErrors) {
"- **$($error.ErrorType)** in $($error.File) - $($error.Timestamp)"
})
"
})

---

## 💡 推奨事項と次のアクション

### 優先度：高
$(
$recommendations = @()

if ($ProofStats.CompletionRate -lt 80) {
    $recommendations += "🔧 検証失敗している証明の修正 (現在 $($ProofStats.FailedProofs) 件)"
}

if ($ErrorAnalysis.TotalErrors -gt 5) {
    $recommendations += "🐛 エラー発生率の削減 (現在 $($ErrorAnalysis.TotalErrors) 件)"
}

if ($PerformanceStats.ErrorRate -gt 20) {
    $recommendations += "⚡ ビルドエラー率の改善 (現在 $($PerformanceStats.ErrorRate)%)"
}

if ($GitStats.CommitCount -eq 0) {
    $recommendations += "📝 定期的なコミット習慣の確立"
}

if ($recommendations.Count -eq 0) {
    $recommendations += "✅ 現在の開発ペースを維持してください"
}

foreach ($rec in $recommendations) { "- $rec" }
)

### 改善提案
- **証明品質**: より詳細なコメントとドキュメント化
- **エラー対策**: 頻出エラーパターンの自動検出システム導入
- **効率化**: よく使用する証明パターンのライブラリ化
- **自動化**: CI/CDパイプラインでの自動検証

---

## 📅 今後の予定

### 短期目標 (今週)
- [ ] 検証失敗証明の修正完了
- [ ] 新規証明 2-3 件の追加
- [ ] エラーレート 10% 以下への改善

### 中期目標 (今月)
- [ ] 全証明の完成率 95% 達成
- [ ] 証明ライブラリの整備
- [ ] 自動テストシステムの構築

---

## 📈 トレンド分析

$(if ($Type -ne "daily") {
"### 過去との比較
- 証明完成率の変化: [前期との比較が必要]
- エラー発生頻度の推移: [トレンド分析が必要]
- 開発速度の変化: [前期のデータとの比較が必要]

### パフォーマンストレンド
- ビルド時間の推移: [履歴データが必要]
- 成功率の変化: [過去データとの比較が必要]
"
})

---

**📊 このレポートは Lean証明ワークフローシステム により自動生成されました**  
**🔄 次回更新**: $(
switch ($Type) {
    "daily" { (Get-Date).AddDays(1).ToString("yyyy-MM-dd") }
    "weekly" { (Get-Date).AddDays(7).ToString("yyyy-MM-dd") }
    "monthly" { (Get-Date).AddMonths(1).ToString("yyyy-MM") }
}
)
"@
}

# メール送信機能
function Send-ReportEmail {
    param([string]$ReportFile, [string]$To, $Config)
    
    if (-not $Config.Email.SMTPServer -or -not $To) {
        Write-ReportLog "メール設定が不完全です" "WARNING"
        return
    }
    
    try {
        $subject = "Lean証明プロジェクト - $ReportType レポート $(Get-Date -Format 'yyyy-MM-dd')"
        $body = Get-Content $ReportFile -Raw
        
        # PowerShellのSend-MailMessageは非推奨のため、簡易実装
        Write-ReportLog "メール送信機能は設定が必要です" "INFO"
        Write-ReportLog "送信先: $To" "INFO"
        Write-ReportLog "件名: $subject" "INFO"
        
    } catch {
        Write-ReportLog "メール送信エラー: $($_.Exception.Message)" "ERROR"
    }
}

# メイン実行
try {
    Write-ReportLog "Lean証明プロジェクト進捗レポート生成を開始" "INFO"
    
    $config = Get-WorkflowConfig
    
    # レポート生成
    $reportFile = New-ProgressReport $ReportType $StartDate $EndDate $OutputPath
    
    # チャート生成（オプション）
    if ($IncludeCharts) {
        Write-ReportLog "チャート生成機能は今後の拡張予定です" "INFO"
    }
    
    # メール送信（オプション）
    if ($SendEmail -and $EmailTo) {
        Send-ReportEmail $reportFile $EmailTo $config
    }
    
    # 自動コミット（オプション）
    if ($AutoCommit) {
        Write-ReportLog "レポートを自動コミット中..." "INFO"
        & git add $reportFile
        & git commit -m "Add $ReportType progress report $(Get-Date -Format 'yyyy-MM-dd')`n`n🤖 Generated with [Claude Code](https://claude.ai/code)`n`nCo-Authored-By: Claude <noreply@anthropic.com>"
    }
    
    Write-ReportLog "レポート生成完了: $reportFile" "SUCCESS"
    Write-Host "`n📊 $ReportType レポートが生成されました!" -ForegroundColor Green
    Write-Host "ファイル: $reportFile" -ForegroundColor Cyan
    
} catch {
    Write-ReportLog "レポート生成中にエラーが発生しました: $($_.Exception.Message)" "ERROR"
    exit 1
}