# Lean証明学習日報システム（日本語版）

param(
    [Parameter(Mandatory=$false)]
    [string]$ProjectDir = ".",
    
    [Parameter(Mandatory=$false)]
    [string]$OutputDir = "daily-reports-jp",
    
    [Parameter(Mandatory=$false)]
    [switch]$ShowHistory = $false,
    
    [Parameter(Mandatory=$false)]
    [switch]$AutoGitCommit = $false
)

Write-Host "`n📚 Lean証明学習日報システム" -ForegroundColor Cyan
Write-Host "================================" -ForegroundColor Cyan

if ($ShowHistory) {
    if (Test-Path $OutputDir) {
        $reports = Get-ChildItem -Path $OutputDir -Filter "*.md" | Sort-Object Name -Descending
        Write-Host "`n📅 過去の学習記録" -ForegroundColor Green
        Write-Host "-------------------" -ForegroundColor Gray
        foreach ($report in $reports) {
            $date = $report.Name -replace 'lean-daily-report-(.+)\.md', '$1'
            Write-Host "  📝 $date のレポート" -ForegroundColor Yellow
        }
    } else {
        Write-Host "`n⚠️ まだレポートが作成されていません" -ForegroundColor Yellow
    }
    exit
}

Write-Host "`n🔍 Leanファイルを解析中..." -ForegroundColor Yellow

# 今日の日付を取得
$today = Get-Date -Format "yyyy-MM-dd"
$todayJP = Get-Date -Format "yyyy年M月d日"

# Leanファイルを検索
$leanFiles = Get-ChildItem -Path $ProjectDir -Recurse -Filter "*.lean" -ErrorAction SilentlyContinue
$modifiedFiles = @()
$allProofs = @()
$allTactics = @()

foreach ($file in $leanFiles) {
    # 今日変更されたファイルをチェック
    if ($file.LastWriteTime.ToString("yyyy-MM-dd") -eq $today) {
        $modifiedFiles += $file
        Write-Host "  ✓ 変更されたファイル: $($file.Name)" -ForegroundColor Gray
        
        # ファイル内容を解析
        $content = Get-Content $file.FullName -Encoding UTF8
        $lineNum = 0
        
        foreach ($line in $content) {
            $lineNum++
            
            # 定理、補題、例題の検出
            if ($line -match '^\s*(theorem|lemma|example)\s+([^:]+):') {
                $proofType = switch($matches[1]) {
                    'theorem' { '定理' }
                    'lemma' { '補題' }
                    'example' { '例題' }
                }
                
                $proof = @{
                    Type = $proofType
                    Name = $matches[2].Trim()
                    File = $file.Name
                    Line = $lineNum
                }
                $allProofs += $proof
            }
            
            # 戦術の検出
            $tactics = @('exact', 'rw', 'simp', 'apply', 'intro', 'intros', 'cases', 'induction', 
                        'constructor', 'use', 'have', 'calc', 'ring', 'norm_num', 
                        'rfl', 'sorry', 'obtain', 'left', 'right', 'split',
                        'assumption', 'contradiction', 'exfalso', 'decide', 'trivial',
                        'omega', 'linarith', 'field_simp', 'push_neg', 'by_contra')
            
            foreach ($tactic in $tactics) {
                if ($line -match "\b$tactic\b") {
                    $allTactics += $tactic
                }
            }
        }
    }
}

# 戦術の使用回数を集計
$tacticCounts = @{}
foreach ($tactic in $allTactics) {
    if ($tacticCounts.ContainsKey($tactic)) {
        $tacticCounts[$tactic]++
    } else {
        $tacticCounts[$tactic] = 1
    }
}

# 戦術を使用頻度でソート
$sortedTactics = $tacticCounts.GetEnumerator() | Sort-Object Value -Descending

# 戦術の日本語説明を取得
function Get-TacticDescription {
    param([string]$Tactic)
    
    $descriptions = @{
        'exact' = '厳密な証明項を直接指定'
        'rw' = '等式による書き換え'
        'simp' = '簡約化ルールの自動適用'
        'apply' = '関数や含意の適用'
        'intro' = '仮定の導入'
        'intros' = '複数仮定の導入'
        'cases' = '場合分けによる証明'
        'induction' = '数学的帰納法'
        'constructor' = '構成子の適用'
        'use' = '存在の証明で具体例を提示'
        'have' = '補助命題の導入'
        'calc' = '計算的証明の連鎖'
        'ring' = '環の公理による自動証明'
        'norm_num' = '数値計算の正規化'
        'rfl' = '反射律（自明な等式）'
        'sorry' = '証明の一時的なスキップ'
        'obtain' = '存在量化子の分解'
        'left' = '選言の左側を選択'
        'right' = '選言の右側を選択'
        'split' = '連言や同値の分解'
        'assumption' = '仮定からの自動証明'
        'contradiction' = '矛盾による証明'
        'exfalso' = '偽からの証明'
        'decide' = '決定可能な命題の自動判定'
        'trivial' = '自明な証明'
        'omega' = 'Presburger算術の決定手続き'
        'linarith' = '線形算術の自動証明'
        'field_simp' = '体における簡約化'
        'push_neg' = '否定の内側への移動'
        'by_contra' = '背理法による証明'
    }
    
    if ($descriptions.ContainsKey($Tactic)) {
        return $descriptions[$Tactic]
    } else {
        return 'Lean戦術'
    }
}

# 学習概念の特定
$learnedConcepts = @()
if ($allTactics -contains 'induction') { 
    $learnedConcepts += @{
        Name = '数学的帰納法'
        Description = '自然数に関する命題を証明する基本的な手法'
    }
}
if ($allTactics -contains 'cases' -or $allTactics -contains 'split') { 
    $learnedConcepts += @{
        Name = '場合分け証明'
        Description = '複数のケースに分けて証明を行う技法'
    }
}
if ($allTactics -contains 'calc') { 
    $learnedConcepts += @{
        Name = '連鎖等式証明'
        Description = '等式を段階的に変形していく証明手法'
    }
}
if ($allTactics -contains 'ring' -or $allTactics -contains 'field_simp') { 
    $learnedConcepts += @{
        Name = '代数的自動証明'
        Description = '環や体の性質を利用した自動証明'
    }
}
if ($allTactics -contains 'contradiction' -or $allTactics -contains 'exfalso' -or $allTactics -contains 'by_contra') { 
    $learnedConcepts += @{
        Name = '背理法'
        Description = '否定を仮定して矛盾を導く証明技法'
    }
}

# 出力ディレクトリを作成
if (!(Test-Path $OutputDir)) {
    New-Item -ItemType Directory -Path $OutputDir | Out-Null
}

# Markdownレポートの生成
$reportFile = Join-Path $OutputDir "lean-daily-report-$today.md"
$report = "# 📚 Lean証明学習日報`n`n"
$report += "**日付**: $todayJP`n`n"
$report += "---`n`n"
$report += "## 📊 本日の学習成果`n`n"
$report += "| 項目 | 数値 |`n"
$report += "|------|------|`n"
$report += "| 変更されたファイル数 | $($modifiedFiles.Count) |`n"
$report += "| 証明した定理数 | $($allProofs.Count) |`n"
$report += "| 使用した戦術の種類 | $($tacticCounts.Count) |`n"
$report += "| 戦術の総使用回数 | $($allTactics.Count) |`n"
$report += "| 学習した概念 | $($learnedConcepts.Count) |`n`n"
$report += "---`n`n"
$report += "## 🎯 証明した定理・補題・例題`n`n"

if ($allProofs.Count -gt 0) {
    # 種類別にグループ化
    $byType = $allProofs | Group-Object Type
    
    foreach ($group in $byType) {
        $report += "### $($group.Name) ($($group.Count)個)`n`n"
        foreach ($proof in $group.Group) {
            $report += "- **$($proof.Name)** ($($proof.File):$($proof.Line))`n"
        }
        $report += "`n"
    }
} else {
    $report += "*本日は新しい証明を完了していません。*`n`n"
}

$report += "---`n`n"
$report += "## ⚔️ 戦術使用統計`n`n"

if ($sortedTactics.Count -gt 0) {
    $report += "### 使用頻度ランキング`n`n"
    $report += "| 順位 | 戦術 | 使用回数 | 説明 |`n"
    $report += "|------|------|----------|------|`n"
    
    $rank = 1
    foreach ($tactic in $sortedTactics | Select-Object -First 10) {
        $description = Get-TacticDescription -Tactic $tactic.Key
        $report += "| $rank | ``$($tactic.Key)`` | $($tactic.Value) | $description |`n"
        $rank++
    }
    
    $report += "`n### 💡 最頻使用戦術`n`n"
    $topTactic = $sortedTactics | Select-Object -First 1
    $report += "本日最も多く使用された戦術は **$($topTactic.Key)** ($($topTactic.Value)回) でした。`n"
    $description = Get-TacticDescription -Tactic $topTactic.Key
    $report += "> $description`n`n"
} else {
    $report += "*本日は戦術を使用していません。*`n`n"
}

$report += "---`n`n"
$report += "## 📖 学習した概念`n`n"

if ($learnedConcepts.Count -gt 0) {
    foreach ($concept in $learnedConcepts) {
        $report += "### $($concept.Name)`n"
        $report += "$($concept.Description)`n`n"
    }
} else {
    $report += "*本日は新しい概念の学習は検出されませんでした。*`n`n"
}

# 難易度の推定
$difficultyLevel = "初級"
if ($allTactics -contains 'induction' -or $allTactics -contains 'calc') {
    $difficultyLevel = "中級"
}
if ($tacticCounts.Count -gt 10 -or $allTactics -contains 'have') {
    $difficultyLevel = "上級"
}

$report += "---`n`n"
$report += "## 📈 学習分析`n`n"
$report += "### 学習レベル評価`n`n"
$report += "本日の学習内容は **$difficultyLevel** レベルと評価されます。`n`n"

# 推奨事項
$report += "---`n`n"
$report += "## 🎯 明日への推奨事項`n`n"

if ($allTactics -contains 'sorry') {
    $sorryCount = ($allTactics | Where-Object { $_ -eq 'sorry' }).Count
    $report += "- ⚠️ ``sorry`` が $sorryCount 箇所で使用されています。これらの証明を完成させましょう。`n"
}

if ($difficultyLevel -eq "初級") {
    $report += "- 📚 より複雑な証明にチャレンジしてみましょう。`n"
} elseif ($difficultyLevel -eq "中級") {
    $report += "- 👍 良いペースで学習が進んでいます。`n"
} else {
    $report += "- 🌟 素晴らしい進捗です！`n"
}

$report += "`n---`n`n"
$report += "*このレポートは $(Get-Date -Format 'yyyy年M月d日 HH時mm分ss秒') に自動生成されました。*`n"

# レポートをファイルに保存
$report | Out-File -FilePath $reportFile -Encoding UTF8

Write-Host "`n✅ 日報が正常に生成されました！" -ForegroundColor Green
Write-Host "📁 保存場所: $reportFile" -ForegroundColor White

# サマリーの表示
Write-Host "`n📊 本日の学習成果サマリー" -ForegroundColor Magenta
Write-Host "------------------------" -ForegroundColor Gray
Write-Host "  🎯 証明数: $($allProofs.Count) 個" -ForegroundColor Yellow
Write-Host "  ⚔️ 戦術: $($tacticCounts.Count) 種類 / $($allTactics.Count) 回使用" -ForegroundColor Yellow
Write-Host "  📖 学習概念: $($learnedConcepts.Count) 個" -ForegroundColor Yellow
Write-Host "  📈 難易度: $difficultyLevel" -ForegroundColor Cyan

if ($sortedTactics.Count -gt 0) {
    $topTactic = $sortedTactics | Select-Object -First 1
    Write-Host "  🏆 最頻使用: $($topTactic.Key) ($($topTactic.Value)回)" -ForegroundColor Cyan
}

Write-Host "`n📚 今日も充実した学習お疲れ様でした！" -ForegroundColor Cyan