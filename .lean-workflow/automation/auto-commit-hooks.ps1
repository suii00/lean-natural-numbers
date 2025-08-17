# Lean証明自動コミットフック システム
# Version: 1.0.0

param(
    [string]$ProofFile,
    [switch]$DryRun,
    [switch]$Verbose
)

# 設定とパス
$WorkflowRoot = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
$ProjectRoot = Split-Path -Parent (Split-Path -Parent $WorkflowRoot)

# Git pre-commit フック
function Invoke-PreCommitHook {
    param([string]$File)
    
    Write-Host "🔍 Pre-commit検証中: $File" -ForegroundColor Yellow
    
    # 1. Leanファイル構文チェック
    if ($File -like "*.lean") {
        Write-Host "  📝 Lean構文チェック..." -ForegroundColor Gray
        
        $lakeCheck = & lake check $File 2>&1
        if ($LASTEXITCODE -ne 0) {
            Write-Host "  ❌ 構文エラーが検出されました" -ForegroundColor Red
            Write-Host $lakeCheck -ForegroundColor Red
            return $false
        }
        Write-Host "  ✅ 構文チェック: OK" -ForegroundColor Green
    }
    
    # 2. ファイルサイズチェック
    $fileSize = (Get-Item $File).Length
    if ($fileSize -gt 1MB) {
        Write-Host "  ⚠️  大きなファイルです: $([math]::Round($fileSize/1MB, 2))MB" -ForegroundColor Yellow
    }
    
    # 3. TODO/FIXMEチェック
    $content = Get-Content $File -Raw
    $todoMatches = [regex]::Matches($content, "TODO|FIXME|XXX|HACK", [System.Text.RegularExpressions.RegexOptions]::IgnoreCase)
    if ($todoMatches.Count -gt 0) {
        Write-Host "  📋 未完了項目が見つかりました: $($todoMatches.Count)個" -ForegroundColor Yellow
        if ($Verbose) {
            foreach ($match in $todoMatches) {
                $lineNum = ($content.Substring(0, $match.Index) -split "`n").Count
                Write-Host "    Line $lineNum : $($match.Value)" -ForegroundColor Gray
            }
        }
    }
    
    return $true
}

# Git post-commit フック
function Invoke-PostCommitHook {
    param([string]$File, [string]$CommitHash)
    
    Write-Host "🎉 Post-commit処理中: $File" -ForegroundColor Green
    
    # 1. 証明難易度自動判定・タグ付け
    Write-Host "  🏷️  難易度タグを追加中..." -ForegroundColor Gray
    
    $difficulty = Get-ProofDifficulty $File
    $proofName = [System.IO.Path]::GetFileNameWithoutExtension($File)
    $tagName = "auto-proof-$proofName-$(Get-Date -Format 'yyyyMMddHHmmss')"
    
    try {
        & git tag -a $tagName -m "Auto-generated: Proof completed [$difficulty] - $proofName"
        Write-Host "  ✅ タグ作成: $tagName" -ForegroundColor Green
    } catch {
        Write-Host "  ⚠️  タグ作成に失敗: $($_.Exception.Message)" -ForegroundColor Yellow
    }
    
    # 2. 証明統計更新
    Write-Host "  📊 統計情報を更新中..." -ForegroundColor Gray
    Update-ProofStatistics $File $CommitHash
    
    # 3. 自動レポート生成（設定による）
    $configPath = Join-Path $WorkflowRoot "config\workflow-config.json"
    if (Test-Path $configPath) {
        $config = Get-Content $configPath | ConvertFrom-Json
        if ($config.Reports.AutoGenerate) {
            Write-Host "  📄 自動レポート生成中..." -ForegroundColor Gray
            & "$WorkflowRoot\core\lean-proof-workflow.ps1" -Action daily-report
        }
    }
}

# 証明難易度判定（最適化版）
function Get-ProofDifficulty {
    param([string]$FilePath)
    
    if (-not (Test-Path $FilePath)) { return "unknown" }
    
    $content = Get-Content $FilePath -Raw
    
    # 複雑性指標
    $metrics = @{
        Lines = ($content -split "`n").Count
        Theorems = ([regex]::Matches($content, "theorem|lemma|def|axiom")).Count
        Imports = ([regex]::Matches($content, "import")).Count
        ComplexTactics = ([regex]::Matches($content, "simp_all|omega|decide|aesop|polyrith|field_simp|ring_nf|abel|norm_cast")).Count
        BasicTactics = ([regex]::Matches($content, "simp|rw|apply|exact|intro|cases")).Count
        ProofBlocks = ([regex]::Matches($content, "by|:=")).Count
        Comments = ([regex]::Matches($content, "--")).Count
        Sorry = ([regex]::Matches($content, "sorry")).Count
    }
    
    # 複雑性スコア計算（調整済み）
    $score = (
        ($metrics.Lines * 0.05) +
        ($metrics.Theorems * 2.0) +
        ($metrics.Imports * 0.3) +
        ($metrics.ComplexTactics * 3.0) +
        ($metrics.BasicTactics * 0.5) +
        ($metrics.ProofBlocks * 0.8) +
        ($metrics.Comments * -0.1) +  # コメントは複雑性を下げる
        ($metrics.Sorry * -2.0)       # sorryは未完成を示すので複雑性を下げる
    )
    
    # 難易度分類（改良版）
    switch ($score) {
        {$_ -le 5}   { return "beginner" }
        {$_ -le 15}  { return "intermediate" }
        {$_ -le 35}  { return "advanced" }
        {$_ -le 60}  { return "expert" }
        default      { return "research" }
    }
}

# 証明統計更新
function Update-ProofStatistics {
    param([string]$File, [string]$CommitHash)
    
    $statsFile = Join-Path $WorkflowRoot "metadata\proof-statistics.json"
    
    # 既存統計読み込み
    $stats = @{
        TotalProofs = 0
        CompletedToday = 0
        ByDifficulty = @{
            beginner = 0
            intermediate = 0
            advanced = 0
            expert = 0
            research = 0
        }
        RecentProofs = @()
        LastUpdated = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    }
    
    if (Test-Path $statsFile) {
        $existingStats = Get-Content $statsFile | ConvertFrom-Json
        $stats.TotalProofs = $existingStats.TotalProofs
        $stats.ByDifficulty = $existingStats.ByDifficulty
        $stats.RecentProofs = $existingStats.RecentProofs
    }
    
    # 今回の証明を追加
    $difficulty = Get-ProofDifficulty $File
    $stats.TotalProofs++
    $stats.ByDifficulty.$difficulty++
    
    # 今日完成したかチェック
    $today = Get-Date -Format "yyyy-MM-dd"
    if ((Get-Date -Format "yyyy-MM-dd") -eq $today) {
        $stats.CompletedToday++
    }
    
    # 最近の証明リストを更新（最新10件）
    $proofRecord = @{
        File = $File
        Difficulty = $difficulty
        Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        CommitHash = $CommitHash
    }
    
    $stats.RecentProofs = @($proofRecord) + $stats.RecentProofs | Select-Object -First 10
    
    # 統計ファイル保存
    $stats | ConvertTo-Json -Depth 3 | Out-File -FilePath $statsFile -Encoding UTF8
    
    Write-Host "  ✅ 統計更新完了: 総証明数 $($stats.TotalProofs)" -ForegroundColor Green
}

# 自動品質チェック
function Test-ProofQuality {
    param([string]$File)
    
    Write-Host "🔍 証明品質をチェック中..." -ForegroundColor Cyan
    
    $content = Get-Content $File -Raw
    $issues = @()
    
    # 1. Sorry チェック
    $sorryCount = ([regex]::Matches($content, "sorry", [System.Text.RegularExpressions.RegexOptions]::IgnoreCase)).Count
    if ($sorryCount -gt 0) {
        $issues += "未完成証明 (sorry): $sorryCount 箇所"
    }
    
    # 2. 長すぎる証明ライン
    $lines = $content -split "`n"
    $longLines = $lines | Where-Object { $_.Length -gt 120 }
    if ($longLines.Count -gt 0) {
        $issues += "長すぎる行: $($longLines.Count) 行"
    }
    
    # 3. コメントの不足
    $totalLines = $lines.Count
    $commentLines = ($lines | Where-Object { $_ -match "^\s*--" }).Count
    $commentRatio = if ($totalLines -gt 0) { $commentLines / $totalLines } else { 0 }
    
    if ($commentRatio -lt 0.1 -and $totalLines -gt 20) {
        $issues += "コメント不足 (推奨: 10%以上, 現在: $([math]::Round($commentRatio * 100, 1))%)"
    }
    
    # 4. 重複コード
    $duplicateLines = $lines | Group-Object | Where-Object { $_.Count -gt 3 -and $_.Name.Trim() -ne "" -and $_.Name -notmatch "^\s*$" }
    if ($duplicateLines.Count -gt 0) {
        $issues += "重複コードの可能性: $($duplicateLines.Count) パターン"
    }
    
    # 結果表示
    if ($issues.Count -eq 0) {
        Write-Host "  ✅ 品質チェック: 問題なし" -ForegroundColor Green
        return $true
    } else {
        Write-Host "  ⚠️  品質チェック: 改善推奨事項" -ForegroundColor Yellow
        foreach ($issue in $issues) {
            Write-Host "    - $issue" -ForegroundColor Yellow
        }
        return $false
    }
}

# メイン実行
if ($ProofFile) {
    Write-Host "`n🚀 Lean証明自動コミットシステム" -ForegroundColor Cyan
    Write-Host "=" * 50
    
    # Dry run チェック
    if ($DryRun) {
        Write-Host "🧪 ドライランモード (実際のコミットは行いません)" -ForegroundColor Magenta
    }
    
    # Pre-commit 処理
    $preCommitPassed = Invoke-PreCommitHook $ProofFile
    if (-not $preCommitPassed) {
        Write-Host "`n❌ Pre-commitチェックに失敗しました" -ForegroundColor Red
        exit 1
    }
    
    # 品質チェック
    $qualityPassed = Test-ProofQuality $ProofFile
    
    # コミット実行
    if (-not $DryRun) {
        Write-Host "`n💾 コミットを実行中..." -ForegroundColor Green
        
        # 自動コミット実行
        $result = & "$WorkflowRoot\core\lean-proof-workflow.ps1" -Action auto-commit -ProofFile $ProofFile
        
        if ($LASTEXITCODE -eq 0) {
            $commitHash = & git rev-parse HEAD
            Write-Host "  ✅ コミット完了: $commitHash" -ForegroundColor Green
            
            # Post-commit 処理
            Invoke-PostCommitHook $ProofFile $commitHash
            
            Write-Host "`n🎉 自動コミットプロセス完了！" -ForegroundColor Green
        } else {
            Write-Host "  ❌ コミットに失敗しました" -ForegroundColor Red
            exit 1
        }
    } else {
        Write-Host "`n✅ ドライラン完了: 実際のコミットは実行されませんでした" -ForegroundColor Cyan
    }
    
    Write-Host "`n" + "=" * 50
} else {
    Write-Host "使用法: .\auto-commit-hooks.ps1 -ProofFile <証明ファイル> [-DryRun] [-Verbose]" -ForegroundColor Yellow
}