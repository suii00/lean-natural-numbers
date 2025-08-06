# Lean証明進捗日報システム
# Lean Proof Progress Daily Report System

param(
    [Parameter(Mandatory=$false)]
    [string]$ProjectDir = ".",
    
    [Parameter(Mandatory=$false)]
    [string]$OutputDir = "daily-reports",
    
    [Parameter(Mandatory=$false)]
    [string]$AnalyzeDate = (Get-Date -Format "yyyy-MM-dd"),
    
    [Parameter(Mandatory=$false)]
    [switch]$ShowHistory = $false,
    
    [Parameter(Mandatory=$false)]
    [switch]$AutoCommit = $false
)

# 証明進捗記録のデータ構造
class ProofProgress {
    [string]$Date
    [string]$TheoremName
    [string]$TheoremType
    [string]$Statement
    [string]$ProofMethod
    [string[]]$TacticsUsed
    [string]$Difficulty
    [string]$ConceptsLearned
    [string]$FileName
    [int]$LineNumber
    [string]$CompletionStatus
    [int]$ProofLength
    [string]$Notes
}

# 戦術使用統計
class TacticStats {
    [string]$TacticName
    [int]$UsageCount
    [string[]]$Contexts
    [string]$Description
}

# 学習概念記録
class ConceptLearned {
    [string]$ConceptName
    [string]$Category
    [string]$Description
    [string]$RelatedTheorems
    [string]$DifficultyLevel
}

# Leanファイルを解析して証明を抽出
function Analyze-LeanProofs {
    param([string]$ProjectDir, [string]$Date)
    
    $proofs = @()
    $leanFiles = Get-ChildItem -Path $ProjectDir -Recurse -Filter "*.lean"
    
    foreach ($file in $leanFiles) {
        # ファイルの最終更新日をチェック
        if ($file.LastWriteTime.ToString("yyyy-MM-dd") -eq $Date) {
            $content = Get-Content $file.FullName
            $proofs += Parse-LeanFile -FilePath $file.FullName -Content $content -Date $Date
        }
    }
    
    return $proofs
}

# Leanファイルの内容を解析
function Parse-LeanFile {
    param([string]$FilePath, [string[]]$Content, [string]$Date)
    
    $proofs = @()
    $currentTheorem = $null
    $inProof = $false
    $proofLines = @()
    $lineNumber = 0
    
    foreach ($line in $Content) {
        $lineNumber++
        $trimmedLine = $line.Trim()
        
        # 定理の開始を検出
        if ($trimmedLine -match '^(theorem|lemma|example)\s+([^:]+):\s*(.+)\s*:=\s*by\s*$') {
            $theoremName = $matches[2].Trim()
            $statement = $matches[3].Trim()
            
            $currentTheorem = [ProofProgress]::new()
            $currentTheorem.Date = $Date
            $currentTheorem.TheoremName = $theoremName
            $currentTheorem.Statement = $statement
            $currentTheorem.FileName = Split-Path $FilePath -Leaf
            $currentTheorem.LineNumber = $lineNumber
            $currentTheorem.TheoremType = $matches[1]
            $currentTheorem.CompletionStatus = "Complete"
            
            $inProof = $true
            $proofLines = @()
        }
        # 証明の終了を検出（次の定義や定理、またはファイル終端）
        elseif ($inProof -and ($trimmedLine -match '^(theorem|lemma|example|def|structure|inductive)' -or $trimmedLine -eq '')) {
            if ($currentTheorem -and $proofLines.Count -gt 0) {
                $currentTheorem = Complete-TheoremAnalysis -Theorem $currentTheorem -ProofLines $proofLines
                $proofs += $currentTheorem
            }
            $inProof = $false
            $currentTheorem = $null
            $proofLines = @()
        }
        # 証明内の行を収集
        elseif ($inProof -and $trimmedLine -ne '' -and -not $trimmedLine.StartsWith('--')) {
            $proofLines += $trimmedLine
        }
    }
    
    # ファイル終端での処理
    if ($inProof -and $currentTheorem -and $proofLines.Count -gt 0) {
        $currentTheorem = Complete-TheoremAnalysis -Theorem $currentTheorem -ProofLines $proofLines
        $proofs += $currentTheorem
    }
    
    return $proofs
}

# 定理解析の完了
function Complete-TheoremAnalysis {
    param([ProofProgress]$Theorem, [string[]]$ProofLines)
    
    $Theorem.ProofLength = $ProofLines.Count
    
    # 使用された戦術を抽出
    $tactics = @()
    $tacticPatterns = @(
        'exact', 'rw', 'simp', 'apply', 'intro', 'intros', 'cases', 'induction', 
        'constructor', 'left', 'right', 'split', 'use', 'exists', 'have', 'show',
        'calc', 'ring', 'field_simp', 'norm_num', 'linarith', 'omega', 'decide',
        'rfl', 'trivial', 'sorry', 'assumption', 'contradiction', 'exfalso'
    )
    
    foreach ($line in $ProofLines) {
        foreach ($pattern in $tacticPatterns) {
            if ($line -match "\b$pattern\b") {
                if ($tactics -notcontains $pattern) {
                    $tactics += $pattern
                }
            }
        }
    }
    
    $Theorem.TacticsUsed = $tactics
    
    # 証明方法の分類
    $Theorem.ProofMethod = Classify-ProofMethod -ProofLines $ProofLines -Tactics $tactics
    
    # 難易度の推定
    $Theorem.Difficulty = Estimate-Difficulty -ProofLines $ProofLines -Tactics $tactics
    
    # 学習した概念の推定
    $Theorem.ConceptsLearned = Identify-Concepts -TheoremName $Theorem.TheoremName -Statement $Theorem.Statement -Tactics $tactics
    
    return $Theorem
}

# 証明方法の分類
function Classify-ProofMethod {
    param([string[]]$ProofLines, [string[]]$Tactics)
    
    if ($Tactics -contains 'induction') { return "数学的帰納法" }
    if ($Tactics -contains 'cases') { return "場合分け" }
    if ($Tactics -contains 'contradiction' -or $Tactics -contains 'exfalso') { return "背理法" }
    if ($Tactics -contains 'constructor') { return "構成的証明" }
    if ($Tactics -contains 'calc') { return "計算的証明" }
    if ($Tactics -contains 'rw' -and $Tactics.Count -le 3) { return "書き換えによる証明" }
    if ($Tactics -contains 'simp' -and $Tactics.Count -le 2) { return "簡単化による証明" }
    if ($Tactics -contains 'exact' -and $Tactics.Count -eq 1) { return "直接証明" }
    
    return "一般的な証明"
}

# 難易度の推定
function Estimate-Difficulty {
    param([string[]]$ProofLines, [string[]]$Tactics)
    
    $complexTactics = @('induction', 'cases', 'calc', 'have', 'show')
    $complexCount = ($Tactics | Where-Object { $complexTactics -contains $_ }).Count
    
    if ($ProofLines.Count -eq 1 -and $Tactics -contains 'rfl') { return "初級" }
    if ($ProofLines.Count -le 3 -and $complexCount -eq 0) { return "初級" }
    if ($ProofLines.Count -le 8 -and $complexCount -le 1) { return "中級" }
    if ($complexCount -ge 2 -or $ProofLines.Count -gt 8) { return "上級" }
    
    return "中級"
}

# 学習概念の特定
function Identify-Concepts {
    param([string]$TheoremName, [string]$Statement, [string[]]$Tactics)
    
    $concepts = @()
    
    # 定理名や記述から概念を推測
    if ($Statement -match '\+|\*|\-|\/') { $concepts += "算術" }
    if ($Statement -match '≤|<|≥|>|=') { $concepts += "順序関係" }
    if ($TheoremName -match 'add|mul|sub|div') { $concepts += "代数演算" }
    if ($TheoremName -match 'assoc|comm|distrib') { $concepts += "代数法則" }
    if ($Statement -match '∀|∃') { $concepts += "量化子" }
    if ($Statement -match '→|∧|∨|¬') { $concepts += "論理演算" }
    if ($Statement -match 'Nat|Int|Real') { $concepts += "数論" }
    if ($Statement -match 'List|Array|Set') { $concepts += "データ構造" }
    
    # 戦術から概念を推測
    if ($Tactics -contains 'induction') { $concepts += "数学的帰納法" }
    if ($Tactics -contains 'cases') { $concepts += "場合分け" }
    if ($Tactics -contains 'rw') { $concepts += "等式変形" }
    if ($Tactics -contains 'simp') { $concepts += "簡単化" }
    if ($Tactics -contains 'calc') { $concepts += "連鎖等式" }
    if ($Tactics -contains 'ring' -or $Tactics -contains 'field_simp') { $concepts += "環論" }
    if ($Tactics -contains 'linarith') { $concepts += "線形算術" }
    
    return ($concepts | Select-Object -Unique) -join ", "
}

# 戦術使用統計を生成
function Generate-TacticStats {
    param([ProofProgress[]]$Proofs)
    
    $tacticUsage = @{}
    
    foreach ($proof in $Proofs) {
        foreach ($tactic in $proof.TacticsUsed) {
            if ($tacticUsage.ContainsKey($tactic)) {
                $tacticUsage[$tactic].UsageCount++
                $tacticUsage[$tactic].Contexts += "$($proof.TheoremName) ($($proof.TheoremType))"
            } else {
                $tacticStat = [TacticStats]::new()
                $tacticStat.TacticName = $tactic
                $tacticStat.UsageCount = 1
                $tacticStat.Contexts = @("$($proof.TheoremName) ($($proof.TheoremType))")
                $tacticStat.Description = Get-TacticDescription -TacticName $tactic
                $tacticUsage[$tactic] = $tacticStat
            }
        }
    }
    
    return $tacticUsage.Values | Sort-Object UsageCount -Descending
}

# 戦術の説明を取得
function Get-TacticDescription {
    param([string]$TacticName)
    
    $descriptions = @{
        'exact' = '正確な証明項を提供'
        'rw' = '等式を使った書き換え'
        'simp' = '簡単化ルールの適用'
        'apply' = '関数や含意の適用'
        'intro' = '前提の導入'
        'cases' = '場合分けによる証明'
        'induction' = '数学的帰納法'
        'constructor' = '構造の構築'
        'rfl' = '反射律の適用'
        'sorry' = '証明の一時的なスキップ'
        'have' = '補題の導入'
        'calc' = '連鎖等式計算'
        'ring' = '環の性質を利用'
        'field_simp' = '体での簡単化'
        'linarith' = '線形算術の決定手続き'
        'omega' = '整数線形算術の決定手続き'
        'norm_num' = '数値の正規化'
        'decide' = '決定可能な命題の自動証明'
    }
    
    return if ($descriptions.ContainsKey($TacticName)) { $descriptions[$TacticName] } else { "Lean戦術" }
}

# 学習概念統計を生成
function Generate-ConceptStats {
    param([ProofProgress[]]$Proofs)
    
    $conceptCounts = @{}
    
    foreach ($proof in $Proofs) {
        if ($proof.ConceptsLearned) {
            $concepts = $proof.ConceptsLearned -split ", "
            foreach ($concept in $concepts) {
                $concept = $concept.Trim()
                if ($conceptCounts.ContainsKey($concept)) {
                    $conceptCounts[$concept]++
                } else {
                    $conceptCounts[$concept] = 1
                }
            }
        }
    }
    
    return $conceptCounts
}

# Markdown日報を生成
function Generate-MarkdownReport {
    param(
        [ProofProgress[]]$Proofs, 
        [TacticStats[]]$TacticStats, 
        $ConceptStats, 
        [string]$Date,
        [string]$OutputDir
    )
    
    if (-not (Test-Path $OutputDir)) {
        New-Item -ItemType Directory -Path $OutputDir | Out-Null
    }
    
    $reportFile = Join-Path $OutputDir "daily-report-$Date.md"
    
    # Markdownレポートの生成
    $markdown = @"
# 🧮 Lean証明学習日報 - $Date

## 📊 今日の成果サマリー

- **証明完了数**: $($Proofs.Count) 個
- **使用戦術数**: $($TacticStats.Count) 種類
- **学習概念数**: $($ConceptStats.Count) 個
- **総証明行数**: $(($Proofs | Measure-Object -Property ProofLength -Sum).Sum) 行

---

## 🎯 完了した証明

"@

    if ($Proofs.Count -gt 0) {
        foreach ($proof in $Proofs) {
            $markdown += @"

### $($proof.TheoremName)

- **種類**: $($proof.TheoremType)
- **記述**: ``$($proof.Statement)``
- **証明方法**: $($proof.ProofMethod)
- **難易度**: $($proof.Difficulty)
- **証明行数**: $($proof.ProofLength) 行
- **使用戦術**: $($proof.TacticsUsed -join ', ')
- **学習概念**: $($proof.ConceptsLearned)
- **ファイル**: $($proof.FileName):$($proof.LineNumber)

"@
        }
    } else {
        $markdown += "`n今日は新しい証明を完了していません。`n"
    }

    $markdown += @"

---

## ⚔️ 戦術使用統計

| 戦術名 | 使用回数 | 説明 |
|--------|----------|------|
"@

    foreach ($tactic in $TacticStats) {
        $markdown += "|``$($tactic.TacticName)``|$($tactic.UsageCount)|$($tactic.Description)|`n"
    }

    $markdown += @"

---

## 📚 学習概念統計

"@

    if ($ConceptStats.Count -gt 0) {
        $sortedConcepts = $ConceptStats.GetEnumerator() | Sort-Object Value -Descending
        
        foreach ($concept in $sortedConcepts) {
            $markdown += "- **$($concept.Key)**: $($concept.Value) 回`n"
        }
    } else {
        $markdown += "今日は新しい概念を学習していません。`n"
    }

    $markdown += @"

---

## 💡 今日の学び

"@

    # 難易度別統計
    $difficultyStats = $Proofs | Group-Object Difficulty
    if ($difficultyStats.Count -gt 0) {
        $markdown += "`n### 📈 証明難易度分析`n`n"
        foreach ($level in $difficultyStats) {
            $markdown += "- **$($level.Name)**: $($level.Count) 個`n"
        }
    }

    # 証明方法統計
    $methodStats = $Proofs | Group-Object ProofMethod
    if ($methodStats.Count -gt 0) {
        $markdown += "`n### 🔍 使用した証明方法`n`n"
        foreach ($method in $methodStats) {
            $markdown += "- **$($method.Name)**: $($method.Count) 回`n"
        }
    }

    # 推奨事項
    $markdown += @"

---

## 🎯 明日への推奨事項

"@

    $recommendations = Generate-Recommendations -Proofs $Proofs -TacticStats $TacticStats
    foreach ($rec in $recommendations) {
        $markdown += "- $rec`n"
    }

    $markdown += @"

---

## 📅 進捗履歴

- **累積証明数**: $(Get-CumulativeProofCount -OutputDir $OutputDir -CurrentCount $Proofs.Count)
- **今月の証明数**: $(Get-MonthlyProofCount -OutputDir $OutputDir -Date $Date -CurrentCount $Proofs.Count)

---

*このレポートは $(Get-Date -Format "yyyy年MM月dd日 HH時mm分") に自動生成されました*
"@

    $markdown | Out-File -FilePath $reportFile -Encoding UTF8
    return $reportFile
}

# 推奨事項の生成
function Generate-Recommendations {
    param([ProofProgress[]]$Proofs, [TacticStats[]]$TacticStats)
    
    $recommendations = @()
    
    if ($Proofs.Count -eq 0) {
        $recommendations += "明日は簡単な定理から始めて、証明の練習をしましょう"
        return $recommendations
    }
    
    # 難易度による推奨
    $basicCount = ($Proofs | Where-Object { $_.Difficulty -eq "初級" }).Count
    $intermediateCount = ($Proofs | Where-Object { $_.Difficulty -eq "中級" }).Count
    $advancedCount = ($Proofs | Where-Object { $_.Difficulty -eq "上級" }).Count
    
    if ($basicCount -gt $intermediateCount * 2) {
        $recommendations += "中級レベルの証明にもチャレンジしてみましょう"
    }
    if ($advancedCount -eq 0 -and $intermediateCount -gt 2) {
        $recommendations += "上級レベルの複雑な証明に挑戦する準備ができています"
    }
    
    # 戦術使用の推奨
    $basicTactics = @('exact', 'rfl', 'simp')
    $advancedTactics = @('induction', 'cases', 'calc', 'have')
    
    $usedBasic = $TacticStats | Where-Object { $basicTactics -contains $_.TacticName }
    $usedAdvanced = $TacticStats | Where-Object { $advancedTactics -contains $_.TacticName }
    
    if ($usedBasic.Count -gt 0 -and $usedAdvanced.Count -eq 0) {
        $recommendations += "induction や cases などのより高度な戦術の学習を推奨します"
    }
    
    if ($TacticStats | Where-Object { $_.TacticName -eq 'sorry' }) {
        $recommendations += "sorry を使用した証明を完成させることを目標にしましょう"
    }
    
    if ($recommendations.Count -eq 0) {
        $recommendations += "素晴らしい進捗です！この調子で学習を続けましょう"
    }
    
    return $recommendations
}

# 累積証明数を取得
function Get-CumulativeProofCount {
    param([string]$OutputDir, [int]$CurrentCount)
    
    if (-not (Test-Path $OutputDir)) { return $CurrentCount }
    
    $reportFiles = Get-ChildItem -Path $OutputDir -Filter "daily-report-*.md"
    $totalCount = $CurrentCount
    
    foreach ($file in $reportFiles) {
        if ($file.Name -ne "daily-report-$(Get-Date -Format 'yyyy-MM-dd').md") {
            $content = Get-Content $file.FullName -Raw
            if ($content -match '証明完了数\*\*:\s*(\d+)') {
                $totalCount += [int]$matches[1]
            }
        }
    }
    
    return $totalCount
}

# 月間証明数を取得
function Get-MonthlyProofCount {
    param([string]$OutputDir, [string]$Date, [int]$CurrentCount)
    
    if (-not (Test-Path $OutputDir)) { return $CurrentCount }
    
    $currentMonth = $Date.Substring(0, 7) # YYYY-MM
    $reportFiles = Get-ChildItem -Path $OutputDir -Filter "daily-report-$currentMonth-*.md"
    $monthlyCount = $CurrentCount
    
    foreach ($file in $reportFiles) {
        if ($file.Name -ne "daily-report-$Date.md") {
            $content = Get-Content $file.FullName -Raw
            if ($content -match '証明完了数\*\*:\s*(\d+)') {
                $monthlyCount += [int]$matches[1]
            }
        }
    }
    
    return $monthlyCount
}

# 履歴表示機能
function Show-ReportHistory {
    param([string]$OutputDir)
    
    if (-not (Test-Path $OutputDir)) {
        Write-Host "まだ日報が作成されていません" -ForegroundColor Yellow
        return
    }
    
    $reportFiles = Get-ChildItem -Path $OutputDir -Filter "daily-report-*.md" | Sort-Object Name -Descending
    
    Write-Host "`n=== Lean証明学習履歴 ===" -ForegroundColor Cyan
    
    foreach ($file in $reportFiles) {
        $content = Get-Content $file.FullName -Raw
        $date = $file.Name -replace 'daily-report-(.+)\.md', '$1'
        
        Write-Host "`n📅 $date" -ForegroundColor Green
        Write-Host "   📁 $($file.Name)" -ForegroundColor Gray
        
        if ($content -match '証明完了数\*\*:\s*(\d+)') {
            Write-Host "   🎯 証明数: $($matches[1])" -ForegroundColor Yellow
        }
        
        if ($content -match '使用戦術数\*\*:\s*(\d+)') {
            Write-Host "   ⚔️ 戦術数: $($matches[1])" -ForegroundColor Magenta
        }
    }
}

# メイン処理
function Main {
    Write-Host "🧮 Lean証明進捗日報システム" -ForegroundColor Cyan
    Write-Host "========================================" -ForegroundColor Cyan
    
    if ($ShowHistory) {
        Show-ReportHistory -OutputDir $OutputDir
        return
    }
    
    Write-Host "📊 $AnalyzeDate の証明を解析中..." -ForegroundColor Yellow
    
    # 証明の解析
    $proofs = Analyze-LeanProofs -ProjectDir $ProjectDir -Date $AnalyzeDate
    
    if ($proofs.Count -eq 0) {
        Write-Host "⚠️ $AnalyzeDate に完了した証明が見つかりませんでした" -ForegroundColor Yellow
        Write-Host "   ファイルが更新されているか確認してください" -ForegroundColor Gray
        
        # 空の日報を作成
        $emptyReport = Generate-MarkdownReport -Proofs @() -TacticStats @() -ConceptStats @{} -Date $AnalyzeDate -OutputDir $OutputDir
        Write-Host "📝 空の日報を作成しました: $emptyReport" -ForegroundColor Green
        return
    }
    
    # 統計の生成
    $tacticStats = Generate-TacticStats -Proofs $proofs
    $conceptStats = Generate-ConceptStats -Proofs $proofs
    
    # レポートの生成
    $reportFile = Generate-MarkdownReport -Proofs $proofs -TacticStats $tacticStats -ConceptStats $conceptStats -Date $AnalyzeDate -OutputDir $OutputDir
    
    Write-Host "✅ 日報が生成されました: $reportFile" -ForegroundColor Green
    
    # Git コミット
    if ($AutoCommit) {
        try {
            git add $reportFile 2>&1 | Out-Null
            git commit -m "📊 Lean学習日報: $AnalyzeDate - $($proofs.Count)個の証明を完了" 2>&1 | Out-Null
            
            if ($LASTEXITCODE -eq 0) {
                $hash = git rev-parse HEAD 2>&1
                Write-Host "📝 日報がコミットされました (Hash: $($hash.ToString().Substring(0, 8)))" -ForegroundColor Green
            }
        }
        catch {
            Write-Warning "Git操作に失敗しました: $($_.Exception.Message)"
        }
    }
    
    # サマリーの表示
    Write-Host "`n📈 今日の成果:" -ForegroundColor Magenta
    Write-Host "   🎯 証明完了: $($proofs.Count) 個" -ForegroundColor White
    Write-Host "   ⚔️ 使用戦術: $($tacticStats.Count) 種類" -ForegroundColor White
    Write-Host "   📚 学習概念: $($conceptStats.Count) 個" -ForegroundColor White
    Write-Host "   📏 総証明行数: $(($proofs | Measure-Object -Property ProofLength -Sum).Sum) 行" -ForegroundColor White
    
    if ($tacticStats.Count -gt 0) {
        Write-Host "`n🏆 最も使用した戦術:" -ForegroundColor Magenta
        $topTactic = $tacticStats | Select-Object -First 1
        Write-Host "   $($topTactic.TacticName) ($($topTactic.UsageCount)回) - $($topTactic.Description)" -ForegroundColor Cyan
    }
}

# スクリプト実行
Main