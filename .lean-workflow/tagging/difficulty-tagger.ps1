# Lean証明難易度別タグ付けシステム
# Version: 1.0.0

[CmdletBinding()]
param(
    [Parameter(Mandatory=$true)]
    [ValidateSet("analyze", "tag", "classify", "report", "batch-tag", "update-taxonomy")]
    [string]$Action,
    
    [string]$ProofFile = "",
    [ValidateSet("auto", "beginner", "intermediate", "advanced", "expert", "research")]
    [string]$Difficulty = "auto",
    [string]$Category = "",
    [string]$Description = "",
    [switch]$Force,
    [switch]$DryRun,
    [string]$BatchPath = ""
)

# 設定とパス
$WorkflowRoot = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
$ProjectRoot = Split-Path -Parent (Split-Path -Parent $WorkflowRoot)
$TaxonomyPath = Join-Path $WorkflowRoot "tagging\proof-taxonomy.json"
$TagsPath = Join-Path $WorkflowRoot "tagging\tags"
$MetadataPath = Join-Path $WorkflowRoot "metadata\proof-metadata.json"

# ディレクトリ確保
@($TagsPath, (Split-Path $TaxonomyPath), (Split-Path $MetadataPath)) | ForEach-Object {
    if (-not (Test-Path $_)) {
        New-Item -Path $_ -ItemType Directory -Force | Out-Null
    }
}

# ログ関数
function Write-TagLog {
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

# 証明タクソノミー（分類体系）取得・作成
function Get-ProofTaxonomy {
    if (Test-Path $TaxonomyPath) {
        try {
            return Get-Content $TaxonomyPath | ConvertFrom-Json -AsHashtable
        } catch {
            Write-TagLog "タクソノミーファイル読み込みエラー: $($_.Exception.Message)" "WARNING"
        }
    }
    
    # デフォルトタクソノミー作成
    $taxonomy = @{
        Version = "1.0.0"
        DifficultyLevels = @{
            beginner = @{
                Name = "初級"
                Description = "基本的な定義と簡単な証明"
                Criteria = @{
                    MaxLines = 50
                    MaxTheorems = 3
                    MaxComplexTactics = 1
                    RequiredKnowledge = @("基本論理", "集合論初歩")
                }
                Examples = @("偶数の定義", "基本的な等式証明")
                ScoreRange = @(0, 15)
            }
            intermediate = @{
                Name = "中級"
                Description = "標準的な数学定理の証明"
                Criteria = @{
                    MaxLines = 150
                    MaxTheorems = 8
                    MaxComplexTactics = 5
                    RequiredKnowledge = @("代数基礎", "解析基礎", "基本戦術")
                }
                Examples = @("ピタゴラスの定理", "基本的な群論")
                ScoreRange = @(15, 40)
            }
            advanced = @{
                Name = "上級"
                Description = "高度な数学理論の形式化"
                Criteria = @{
                    MaxLines = 300
                    MaxTheorems = 15
                    MaxComplexTactics = 10
                    RequiredKnowledge = @("高等代数", "実解析", "位相幾何")
                }
                Examples = @("ガロア理論", "測度論基礎")
                ScoreRange = @(40, 80)
            }
            expert = @{
                Name = "専門"
                Description = "研究レベルの複雑な証明"
                Criteria = @{
                    MaxLines = 500
                    MaxTheorems = 25
                    MaxComplexTactics = 20
                    RequiredKnowledge = @("専門数学", "高度な戦術")
                }
                Examples = @("フェルマーの最終定理部分証明", "代数的位相幾何")
                ScoreRange = @(80, 150)
            }
            research = @{
                Name = "研究"
                Description = "最先端研究の形式化"
                Criteria = @{
                    MaxLines = 1000
                    MaxTheorems = 50
                    MaxComplexTactics = 50
                    RequiredKnowledge = @("最新研究", "実験的戦術")
                }
                Examples = @("未解決予想の部分結果", "新理論の基礎")
                ScoreRange = @(150, 999)
            }
        }
        Categories = @{
            number_theory = @{
                Name = "数論"
                Keywords = @("prime", "gcd", "lcm", "modular", "diophantine", "divisibility")
                Subcategories = @("elementary", "algebraic", "analytic")
            }
            algebra = @{
                Name = "代数学"
                Keywords = @("group", "ring", "field", "module", "homomorphism", "isomorphism")
                Subcategories = @("linear", "abstract", "commutative", "homological")
            }
            analysis = @{
                Name = "解析学"
                Keywords = @("limit", "continuous", "derivative", "integral", "convergence", "series")
                Subcategories = @("real", "complex", "functional", "harmonic")
            }
            geometry = @{
                Name = "幾何学"
                Keywords = @("triangle", "circle", "angle", "distance", "parallel", "congruent")
                Subcategories = @("euclidean", "analytic", "differential", "algebraic")
            }
            topology = @{
                Name = "位相数学"
                Keywords = @("open", "closed", "compact", "connected", "homeomorphism", "homotopy")
                Subcategories = @("general", "algebraic", "differential")
            }
            logic = @{
                Name = "論理学"
                Keywords = @("proposition", "predicate", "quantifier", "proof", "model", "consistency")
                Subcategories = @("propositional", "first-order", "higher-order", "modal")
            }
            set_theory = @{
                Name = "集合論"
                Keywords = @("set", "union", "intersection", "cardinality", "ordinal", "cardinal")
                Subcategories = @("naive", "axiomatic", "descriptive")
            }
            combinatorics = @{
                Name = "組合せ論"
                Keywords = @("permutation", "combination", "graph", "tree", "matching", "coloring")
                Subcategories = @("enumerative", "algebraic", "probabilistic")
            }
        }
        ComplexityFactors = @{
            LineCount = @{ Weight = 0.05; Description = "ファイルの行数" }
            TheoremCount = @{ Weight = 2.0; Description = "定理・補題の数" }
            ImportCount = @{ Weight = 0.3; Description = "インポートの数" }
            BasicTactics = @{ Weight = 0.5; Description = "基本戦術の使用回数" }
            ComplexTactics = @{ Weight = 3.0; Description = "高度戦術の使用回数" }
            ProofBlocks = @{ Weight = 0.8; Description = "証明ブロックの数" }
            SorryCount = @{ Weight = -2.0; Description = "未完成部分(sorry)の数" }
            CommentRatio = @{ Weight = -0.1; Description = "コメント比率" }
            NestedDepth = @{ Weight = 1.5; Description = "ネスト深度" }
            MathLibDependency = @{ Weight = 1.0; Description = "Mathlib依存度" }
        }
        TacticClassification = @{
            Basic = @("simp", "rw", "apply", "exact", "intro", "cases", "split", "left", "right", "exfalso")
            Intermediate = @("induction", "rcases", "have", "suffices", "calc", "convert", "refine", "use")
            Advanced = @("simp_all", "tauto", "finish", "clarify", "safe", "blast", "auto")
            Expert = @("omega", "decide", "norm_num", "ring", "field_simp", "linarith", "nlinarith")
            Research = @("polyrith", "aesop", "abel", "group", "noncomm_ring", "tactic")
        }
    }
    
    # タクソノミーファイル保存
    $taxonomy | ConvertTo-Json -Depth 6 | Out-File -FilePath $TaxonomyPath -Encoding UTF8
    Write-TagLog "デフォルトタクソノミーを作成しました: $TaxonomyPath" "SUCCESS"
    
    return $taxonomy
}

# 証明の詳細分析
function Analyze-ProofComplexity {
    param([string]$FilePath)
    
    if (-not (Test-Path $FilePath)) {
        Write-TagLog "ファイルが見つかりません: $FilePath" "ERROR"
        return $null
    }
    
    Write-TagLog "証明複雑性を分析中: $FilePath" "INFO"
    
    try {
        $content = Get-Content $FilePath -Raw
        $lines = $content -split "`n"
        
        $analysis = @{
            FilePath = $FilePath
            FileName = [System.IO.Path]::GetFileNameWithoutExtension($FilePath)
            BasicMetrics = @{}
            TacticAnalysis = @{}
            StructuralAnalysis = @{}
            ContentAnalysis = @{}
            ComplexityScore = 0
            EstimatedDifficulty = ""
            RecommendedLevel = ""
        }
        
        # 基本メトリクス
        $analysis.BasicMetrics = @{
            TotalLines = $lines.Count
            NonEmptyLines = ($lines | Where-Object { $_.Trim() -ne "" }).Count
            CommentLines = ($lines | Where-Object { $_ -match "^\s*--" }).Count
            CodeLines = $analysis.BasicMetrics.NonEmptyLines - $analysis.BasicMetrics.CommentLines
            FileSize = (Get-Item $FilePath).Length
            CommentRatio = if ($analysis.BasicMetrics.NonEmptyLines -gt 0) { 
                [math]::Round($analysis.BasicMetrics.CommentLines / $analysis.BasicMetrics.NonEmptyLines, 3) 
            } else { 0 }
        }
        
        # 戦術分析
        $taxonomy = Get-ProofTaxonomy
        $analysis.TacticAnalysis = @{
            BasicTactics = 0
            IntermediateTactics = 0
            AdvancedTactics = 0
            ExpertTactics = 0
            ResearchTactics = 0
            TotalTacticUsage = 0
            UniqueTactics = @()
            TacticFrequency = @{}
        }
        
        foreach ($tacticLevel in $taxonomy.TacticClassification.Keys) {
            foreach ($tactic in $taxonomy.TacticClassification[$tacticLevel]) {
                $matches = [regex]::Matches($content, "\b$tactic\b", [System.Text.RegularExpressions.RegexOptions]::IgnoreCase)
                if ($matches.Count -gt 0) {
                    $analysis.TacticAnalysis.TacticFrequency[$tactic] = $matches.Count
                    $analysis.TacticAnalysis.UniqueTactics += $tactic
                    $analysis.TacticAnalysis.TotalTacticUsage += $matches.Count
                    
                    switch ($tacticLevel) {
                        "Basic" { $analysis.TacticAnalysis.BasicTactics += $matches.Count }
                        "Intermediate" { $analysis.TacticAnalysis.IntermediateTactics += $matches.Count }
                        "Advanced" { $analysis.TacticAnalysis.AdvancedTactics += $matches.Count }
                        "Expert" { $analysis.TacticAnalysis.ExpertTactics += $matches.Count }
                        "Research" { $analysis.TacticAnalysis.ResearchTactics += $matches.Count }
                    }
                }
            }
        }
        
        # 構造分析
        $analysis.StructuralAnalysis = @{
            Theorems = ([regex]::Matches($content, "theorem\s+\w+")).Count
            Lemmas = ([regex]::Matches($content, "lemma\s+\w+")).Count
            Definitions = ([regex]::Matches($content, "def\s+\w+")).Count
            Axioms = ([regex]::Matches($content, "axiom\s+\w+")).Count
            Examples = ([regex]::Matches($content, "example\s*:")).Count
            ProofBlocks = ([regex]::Matches($content, "\bby\b|\:=")).Count
            Imports = ([regex]::Matches($content, "^import\s+")).Count
            Namespaces = ([regex]::Matches($content, "namespace\s+\w+")).Count
            Variables = ([regex]::Matches($content, "variable\s*[\(\[]")).Count
        }
        
        $analysis.StructuralAnalysis.TotalDeclarations = 
            $analysis.StructuralAnalysis.Theorems + 
            $analysis.StructuralAnalysis.Lemmas + 
            $analysis.StructuralAnalysis.Definitions + 
            $analysis.StructuralAnalysis.Axioms
        
        # 内容分析
        $analysis.ContentAnalysis = @{
            SorryCount = ([regex]::Matches($content, "\bsorry\b", [System.Text.RegularExpressions.RegexOptions]::IgnoreCase)).Count
            TodoCount = ([regex]::Matches($content, "TODO|FIXME|XXX", [System.Text.RegularExpressions.RegexOptions]::IgnoreCase)).Count
            MaxNestedDepth = Get-MaxNestedDepth $content
            MathLibDependencies = Get-MathLibDependencyLevel $content
            CategoryKeywords = @{}
            EstimatedCategory = ""
        }
        
        # カテゴリ判定
        foreach ($category in $taxonomy.Categories.Keys) {
            $keywordMatches = 0
            foreach ($keyword in $taxonomy.Categories[$category].Keywords) {
                $matches = [regex]::Matches($content, $keyword, [System.Text.RegularExpressions.RegexOptions]::IgnoreCase)
                $keywordMatches += $matches.Count
            }
            $analysis.ContentAnalysis.CategoryKeywords[$category] = $keywordMatches
        }
        
        $topCategory = $analysis.ContentAnalysis.CategoryKeywords.GetEnumerator() | 
                      Sort-Object Value -Descending | 
                      Select-Object -First 1
        
        $analysis.ContentAnalysis.EstimatedCategory = if ($topCategory.Value -gt 0) { $topCategory.Name } else { "other" }
        
        # 複雑性スコア計算
        $factors = $taxonomy.ComplexityFactors
        $score = 0
        
        $score += $analysis.BasicMetrics.TotalLines * $factors.LineCount.Weight
        $score += $analysis.StructuralAnalysis.TotalDeclarations * $factors.TheoremCount.Weight
        $score += $analysis.StructuralAnalysis.Imports * $factors.ImportCount.Weight
        $score += $analysis.TacticAnalysis.BasicTactics * $factors.BasicTactics.Weight
        $score += ($analysis.TacticAnalysis.AdvancedTactics + $analysis.TacticAnalysis.ExpertTactics + $analysis.TacticAnalysis.ResearchTactics) * $factors.ComplexTactics.Weight
        $score += $analysis.StructuralAnalysis.ProofBlocks * $factors.ProofBlocks.Weight
        $score += $analysis.ContentAnalysis.SorryCount * $factors.SorryCount.Weight
        $score += $analysis.BasicMetrics.CommentRatio * $factors.CommentRatio.Weight * 100
        $score += $analysis.ContentAnalysis.MaxNestedDepth * $factors.NestedDepth.Weight
        $score += $analysis.ContentAnalysis.MathLibDependencies * $factors.MathLibDependency.Weight
        
        $analysis.ComplexityScore = [math]::Round($score, 2)
        
        # 難易度判定
        foreach ($level in $taxonomy.DifficultyLevels.Keys) {
            $range = $taxonomy.DifficultyLevels[$level].ScoreRange
            if ($analysis.ComplexityScore -ge $range[0] -and $analysis.ComplexityScore -lt $range[1]) {
                $analysis.EstimatedDifficulty = $level
                $analysis.RecommendedLevel = $taxonomy.DifficultyLevels[$level].Name
                break
            }
        }
        
        # 最高レベルのケース
        if (-not $analysis.EstimatedDifficulty) {
            $analysis.EstimatedDifficulty = "research"
            $analysis.RecommendedLevel = $taxonomy.DifficultyLevels.research.Name
        }
        
        Write-TagLog "分析完了: $($analysis.FileName) - 複雑性スコア: $($analysis.ComplexityScore), 推定難易度: $($analysis.EstimatedDifficulty)" "SUCCESS"
        
        return $analysis
        
    } catch {
        Write-TagLog "分析中にエラーが発生しました: $($_.Exception.Message)" "ERROR"
        return $null
    }
}

# ネスト深度計算
function Get-MaxNestedDepth {
    param([string]$Content)
    
    $maxDepth = 0
    $currentDepth = 0
    
    $lines = $Content -split "`n"
    foreach ($line in $lines) {
        # インデント深度を計算（簡易版）
        $leadingSpaces = ($line -replace "^(\s*).*", '$1').Length
        $indentLevel = [math]::Floor($leadingSpaces / 2)  # 2スペース = 1レベルと仮定
        
        if ($indentLevel -gt $currentDepth) {
            $currentDepth = $indentLevel
            if ($currentDepth -gt $maxDepth) {
                $maxDepth = $currentDepth
            }
        }
    }
    
    return $maxDepth
}

# Mathlib依存レベル取得
function Get-MathLibDependencyLevel {
    param([string]$Content)
    
    $mathLibImports = [regex]::Matches($Content, "^import\s+Mathlib", [System.Text.RegularExpressions.RegexOptions]::Multiline)
    $advancedModules = [regex]::Matches($Content, "Mathlib\.(Analysis|Topology|CategoryTheory|AlgebraicGeometry|NumberTheory\.ArithmeticFunction)", [System.Text.RegularExpressions.RegexOptions]::IgnoreCase)
    
    $dependencyLevel = $mathLibImports.Count
    if ($advancedModules.Count -gt 0) {
        $dependencyLevel += $advancedModules.Count * 2  # 高度なモジュールは重み付け
    }
    
    return $dependencyLevel
}

# タグ作成・適用
function New-ProofTag {
    param(
        [string]$FilePath,
        [string]$Difficulty,
        [string]$Category,
        [string]$Description,
        [object]$Analysis,
        [bool]$DryRun
    )
    
    $proofName = [System.IO.Path]::GetFileNameWithoutExtension($FilePath)
    $timestamp = Get-Date -Format "yyyyMMdd-HHmmss"
    
    # タグ名生成
    $tagComponents = @("proof", $proofName, $Difficulty)
    if ($Category) { $tagComponents += $Category }
    $tagComponents += $timestamp
    
    $tagName = $tagComponents -join "-"
    
    # タグメッセージ作成
    $tagMessage = @"
Lean Proof Classification: $proofName

Difficulty: $Difficulty ($($Analysis.RecommendedLevel))
Category: $(if ($Category) { $Category } else { $Analysis.ContentAnalysis.EstimatedCategory })
Complexity Score: $($Analysis.ComplexityScore)

Analysis Summary:
- Total Declarations: $($Analysis.StructuralAnalysis.TotalDeclarations)
- Tactic Usage: $($Analysis.TacticAnalysis.TotalTacticUsage)
- File Size: $([math]::Round($Analysis.BasicMetrics.FileSize / 1KB, 2)) KB
- Lines of Code: $($Analysis.BasicMetrics.CodeLines)

$(if ($Description) { "Description: $Description" })

Auto-classified by Lean Proof Difficulty Tagger
"@
    
    try {
        if ($DryRun) {
            Write-TagLog "【ドライラン】タグ作成:" "INFO"
            Write-TagLog "  タグ名: $tagName" "INFO"
            Write-TagLog "  対象ファイル: $FilePath" "INFO"
            Write-TagLog "  難易度: $Difficulty" "INFO"
            Write-TagLog "  カテゴリ: $(if ($Category) { $Category } else { $Analysis.ContentAnalysis.EstimatedCategory })" "INFO"
            return @{
                Success = $true
                TagName = $tagName
                DryRun = $true
            }
        }
        
        # Gitタグ作成
        Write-TagLog "Gitタグを作成中: $tagName" "INFO"
        $createResult = & git tag -a $tagName -m $tagMessage 2>&1
        
        if ($LASTEXITCODE -ne 0) {
            Write-TagLog "Gitタグ作成に失敗しました: $createResult" "ERROR"
            return @{ Success = $false; Error = $createResult }
        }
        
        # メタデータ保存
        Save-ProofMetadata $FilePath $Analysis $tagName $Difficulty $Category $Description
        
        Write-TagLog "タグを正常に作成しました: $tagName" "SUCCESS"
        
        return @{
            Success = $true
            TagName = $tagName
            Analysis = $Analysis
            DryRun = $false
        }
        
    } catch {
        Write-TagLog "タグ作成中にエラーが発生しました: $($_.Exception.Message)" "ERROR"
        return @{ Success = $false; Error = $_.Exception.Message }
    }
}

# 証明メタデータ保存
function Save-ProofMetadata {
    param($FilePath, $Analysis, $TagName, $Difficulty, $Category, $Description)
    
    try {
        # 既存メタデータ読み込み
        $metadata = @{}
        if (Test-Path $MetadataPath) {
            $metadata = Get-Content $MetadataPath | ConvertFrom-Json -AsHashtable
        }
        
        # 新しいメタデータエントリ
        $proofMetadata = @{
            FilePath = $FilePath
            FileName = [System.IO.Path]::GetFileNameWithoutExtension($FilePath)
            Difficulty = $Difficulty
            Category = if ($Category) { $Category } else { $Analysis.ContentAnalysis.EstimatedCategory }
            Description = $Description
            TagName = $TagName
            ComplexityScore = $Analysis.ComplexityScore
            Analysis = @{
                TotalDeclarations = $Analysis.StructuralAnalysis.TotalDeclarations
                TacticUsage = $Analysis.TacticAnalysis.TotalTacticUsage
                FileSize = $Analysis.BasicMetrics.FileSize
                LinesOfCode = $Analysis.BasicMetrics.CodeLines
                CommentRatio = $Analysis.BasicMetrics.CommentRatio
                MathLibDependencies = $Analysis.ContentAnalysis.MathLibDependencies
            }
            Timestamps = @{
                Created = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
                LastAnalyzed = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
                LastTagged = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
            }
            Version = "1.0.0"
        }
        
        # メタデータ更新
        $metadata[$FilePath] = $proofMetadata
        
        # ファイル保存
        $metadata | ConvertTo-Json -Depth 5 | Out-File -FilePath $MetadataPath -Encoding UTF8
        
        Write-TagLog "メタデータを保存しました: $FilePath" "INFO"
        
    } catch {
        Write-TagLog "メタデータ保存エラー: $($_.Exception.Message)" "WARNING"
    }
}

# バッチタグ付け
function Invoke-BatchTagging {
    param([string]$BatchPath)
    
    if (-not $BatchPath) {
        $BatchPath = $ProjectRoot
    }
    
    Write-TagLog "バッチタグ付けを開始: $BatchPath" "INFO"
    
    $leanFiles = Get-ChildItem -Path $BatchPath -Filter "*.lean" -Recurse
    $results = @{
        Total = $leanFiles.Count
        Success = 0
        Failed = 0
        Skipped = 0
        Results = @()
    }
    
    foreach ($file in $leanFiles) {
        Write-TagLog "処理中: $($file.Name)" "INFO"
        
        try {
            # 分析実行
            $analysis = Analyze-ProofComplexity $file.FullName
            if (-not $analysis) {
                $results.Failed++
                continue
            }
            
            # 既存タグチェック
            $existingTags = & git tag -l "*$($analysis.FileName)*" 2>$null
            if ($existingTags -and -not $Force) {
                Write-TagLog "既存のタグが見つかりました。スキップします: $($file.Name)" "WARNING"
                $results.Skipped++
                continue
            }
            
            # タグ作成
            $tagResult = New-ProofTag -FilePath $file.FullName -Difficulty $analysis.EstimatedDifficulty -Category $analysis.ContentAnalysis.EstimatedCategory -Description "" -Analysis $analysis -DryRun $DryRun
            
            $results.Results += @{
                File = $file.FullName
                Difficulty = $analysis.EstimatedDifficulty
                Category = $analysis.ContentAnalysis.EstimatedCategory
                Score = $analysis.ComplexityScore
                TagName = $tagResult.TagName
                Success = $tagResult.Success
            }
            
            if ($tagResult.Success) {
                $results.Success++
                Write-TagLog "成功: $($file.Name) -> $($tagResult.TagName)" "SUCCESS"
            } else {
                $results.Failed++
                Write-TagLog "失敗: $($file.Name) -> $($tagResult.Error)" "ERROR"
            }
            
        } catch {
            Write-TagLog "処理中にエラー: $($file.Name) -> $($_.Exception.Message)" "ERROR"
            $results.Failed++
        }
        
        # プログレス表示
        $processed = $results.Success + $results.Failed + $results.Skipped
        $progress = [math]::Round(($processed / $results.Total) * 100, 1)
        Write-Progress -Activity "バッチタグ付け" -Status "$processed / $($results.Total) 処理済み" -PercentComplete $progress
    }
    
    Write-Progress -Completed -Activity "バッチタグ付け"
    
    Write-TagLog "バッチタグ付け完了: 成功 $($results.Success), 失敗 $($results.Failed), スキップ $($results.Skipped)" "SUCCESS"
    
    return $results
}

# タグレポート生成
function New-TagReport {
    Write-TagLog "タグレポートを生成中..." "INFO"
    
    try {
        # メタデータ読み込み
        $metadata = @{}
        if (Test-Path $MetadataPath) {
            $metadata = Get-Content $MetadataPath | ConvertFrom-Json -AsHashtable
        }
        
        if ($metadata.Count -eq 0) {
            Write-TagLog "メタデータが見つかりません" "WARNING"
            return
        }
        
        # 統計集計
        $stats = @{
            Total = $metadata.Count
            ByDifficulty = @{}
            ByCategory = @{}
            ComplexityDistribution = @()
            AverageComplexity = 0
            TaggedFiles = @()
        }
        
        $totalComplexity = 0
        
        foreach ($entry in $metadata.Values) {
            # 難易度別集計
            if ($stats.ByDifficulty.ContainsKey($entry.Difficulty)) {
                $stats.ByDifficulty[$entry.Difficulty]++
            } else {
                $stats.ByDifficulty[$entry.Difficulty] = 1
            }
            
            # カテゴリ別集計
            if ($stats.ByCategory.ContainsKey($entry.Category)) {
                $stats.ByCategory[$entry.Category]++
            } else {
                $stats.ByCategory[$entry.Category] = 1
            }
            
            # 複雑性統計
            $totalComplexity += $entry.ComplexityScore
            $stats.ComplexityDistribution += @{
                File = $entry.FileName
                Score = $entry.ComplexityScore
                Difficulty = $entry.Difficulty
            }
            
            $stats.TaggedFiles += @{
                Name = $entry.FileName
                Difficulty = $entry.Difficulty
                Category = $entry.Category
                Score = $entry.ComplexityScore
                Tag = $entry.TagName
            }
        }
        
        $stats.AverageComplexity = if ($stats.Total -gt 0) { 
            [math]::Round($totalComplexity / $stats.Total, 2) 
        } else { 0 }
        
        # レポート生成
        $reportFile = Join-Path $WorkflowRoot "reports\difficulty-tag-report-$(Get-Date -Format 'yyyy-MM-dd').md"
        
        $report = Generate-TagReport $stats
        $report | Out-File -FilePath $reportFile -Encoding UTF8
        
        Write-TagLog "タグレポートを生成しました: $reportFile" "SUCCESS"
        
        return $reportFile
        
    } catch {
        Write-TagLog "レポート生成エラー: $($_.Exception.Message)" "ERROR"
        return $null
    }
}

# タグレポート内容生成
function Generate-TagReport {
    param($Stats)
    
    return @"
# Lean証明難易度タグレポート

**生成日時**: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")
**分析対象**: $($Stats.Total) ファイル

---

## 📊 難易度分布

$(foreach ($difficulty in ($Stats.ByDifficulty.GetEnumerator() | Sort-Object Name)) {
    $percentage = [math]::Round(($difficulty.Value / $Stats.Total) * 100, 1)
    "- **$($difficulty.Name)**: $($difficulty.Value) ファイル ($percentage%)"
})

## 📈 カテゴリ分布

$(foreach ($category in ($Stats.ByCategory.GetEnumerator() | Sort-Object Value -Descending)) {
    $percentage = [math]::Round(($category.Value / $Stats.Total) * 100, 1)
    "- **$($category.Name)**: $($category.Value) ファイル ($percentage%)"
})

## 🎯 複雑性統計

- **平均複雑性スコア**: $($Stats.AverageComplexity)
- **最高スコア**: $($Stats.ComplexityDistribution | ForEach-Object { $_.Score } | Measure-Object -Maximum | Select-Object -ExpandProperty Maximum)
- **最低スコア**: $($Stats.ComplexityDistribution | ForEach-Object { $_.Score } | Measure-Object -Minimum | Select-Object -ExpandProperty Minimum)

### 複雑性上位10ファイル

$(foreach ($item in ($Stats.ComplexityDistribution | Sort-Object Score -Descending | Select-Object -First 10)) {
    "- **$($item.File)**: スコア $($item.Score) ($($item.Difficulty))"
})

## 🏷️ タグ付け済みファイル一覧

$(foreach ($file in ($Stats.TaggedFiles | Sort-Object Difficulty, Score -Descending)) {
    "### $($file.Name) [$($file.Difficulty)]
- **カテゴリ**: $($file.Category)
- **複雑性スコア**: $($file.Score)
- **Gitタグ**: ``$($file.Tag)``
"
})

## 💡 推奨事項

### 学習パス
1. **初心者向け**: $($Stats.ByDifficulty['beginner'] ?? 0) ファイルから開始
2. **中級者向け**: $($Stats.ByDifficulty['intermediate'] ?? 0) ファイルで理解を深化
3. **上級者向け**: $($Stats.ByDifficulty['advanced'] ?? 0) ファイルで専門知識を獲得

### 重要カテゴリ
$(foreach ($category in ($Stats.ByCategory.GetEnumerator() | Sort-Object Value -Descending | Select-Object -First 3)) {
    "- **$($category.Name)**: $($category.Value) ファイル - 重点学習推奨"
})

---

*自動生成レポート - Lean証明難易度タグシステム*
"@
}

# メイン実行ロジック
switch ($Action) {
    "analyze" {
        if (-not $ProofFile) {
            Write-TagLog "証明ファイルが指定されていません" "ERROR"
            exit 1
        }
        
        $analysis = Analyze-ProofComplexity $ProofFile
        if ($analysis) {
            Write-Host "`n🔍 証明分析結果: $($analysis.FileName)" -ForegroundColor Cyan
            Write-Host "複雑性スコア: $($analysis.ComplexityScore)"
            Write-Host "推定難易度: $($analysis.EstimatedDifficulty) ($($analysis.RecommendedLevel))"
            Write-Host "推定カテゴリ: $($analysis.ContentAnalysis.EstimatedCategory)"
            Write-Host "総宣言数: $($analysis.StructuralAnalysis.TotalDeclarations)"
            Write-Host "戦術使用数: $($analysis.TacticAnalysis.TotalTacticUsage)"
        }
    }
    
    "tag" {
        if (-not $ProofFile) {
            Write-TagLog "証明ファイルが指定されていません" "ERROR"
            exit 1
        }
        
        $analysis = Analyze-ProofComplexity $ProofFile
        if (-not $analysis) {
            Write-TagLog "分析に失敗しました" "ERROR"
            exit 1
        }
        
        $targetDifficulty = if ($Difficulty -eq "auto") { $analysis.EstimatedDifficulty } else { $Difficulty }
        $targetCategory = if ($Category) { $Category } else { $analysis.ContentAnalysis.EstimatedCategory }
        
        $tagResult = New-ProofTag -FilePath $ProofFile -Difficulty $targetDifficulty -Category $targetCategory -Description $Description -Analysis $analysis -DryRun $DryRun
        
        if ($tagResult.Success) {
            Write-Host "`n🏷️ タグ付け完了!" -ForegroundColor Green
            Write-Host "タグ名: $($tagResult.TagName)"
            Write-Host "難易度: $targetDifficulty"
            Write-Host "カテゴリ: $targetCategory"
        } else {
            Write-Host "`n❌ タグ付けに失敗しました" -ForegroundColor Red
            exit 1
        }
    }
    
    "classify" {
        if (-not $ProofFile) {
            Write-TagLog "証明ファイルが指定されていません" "ERROR"
            exit 1
        }
        
        $analysis = Analyze-ProofComplexity $ProofFile
        if ($analysis) {
            Write-Host "`n📋 証明分類結果" -ForegroundColor Cyan
            Write-Host "ファイル: $($analysis.FileName)"
            Write-Host "難易度: $($analysis.EstimatedDifficulty)"
            Write-Host "カテゴリ: $($analysis.ContentAnalysis.EstimatedCategory)"
            Write-Host "複雑性: $($analysis.ComplexityScore)"
            
            # 詳細表示
            Write-Host "`n📊 詳細分析:"
            Write-Host "  定理数: $($analysis.StructuralAnalysis.Theorems)"
            Write-Host "  補題数: $($analysis.StructuralAnalysis.Lemmas)"
            Write-Host "  定義数: $($analysis.StructuralAnalysis.Definitions)"
            Write-Host "  戦術使用: $($analysis.TacticAnalysis.TotalTacticUsage)"
            Write-Host "  コード行数: $($analysis.BasicMetrics.CodeLines)"
        }
    }
    
    "report" {
        $reportFile = New-TagReport
        if ($reportFile) {
            Write-Host "`n📊 タグレポートを生成しました!" -ForegroundColor Green
            Write-Host "ファイル: $reportFile"
        } else {
            Write-Host "`n❌ レポート生成に失敗しました" -ForegroundColor Red
            exit 1
        }
    }
    
    "batch-tag" {
        Write-Host "`n🔄 バッチタグ付けを開始..." -ForegroundColor Cyan
        $results = Invoke-BatchTagging $BatchPath
        
        Write-Host "`n📊 バッチ処理結果:" -ForegroundColor Cyan
        Write-Host "総ファイル数: $($results.Total)"
        Write-Host "成功: $($results.Success)" -ForegroundColor Green
        Write-Host "失敗: $($results.Failed)" -ForegroundColor Red
        Write-Host "スキップ: $($results.Skipped)" -ForegroundColor Yellow
    }
    
    "update-taxonomy" {
        Write-Host "`n🔧 タクソノミーを更新中..." -ForegroundColor Cyan
        $taxonomy = Get-ProofTaxonomy
        Write-Host "タクソノミーを更新しました: $TaxonomyPath" -ForegroundColor Green
        Write-Host "難易度レベル: $($taxonomy.DifficultyLevels.Keys -join ', ')"
        Write-Host "カテゴリ: $($taxonomy.Categories.Keys -join ', ')"
    }
    
    default {
        Write-Host "不明なアクション: $Action" -ForegroundColor Red
        Write-Host "使用可能なアクション: analyze, tag, classify, report, batch-tag, update-taxonomy"
        exit 1
    }
}