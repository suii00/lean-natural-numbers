# Proof Complexity Analyzer
# Analyzes and compares proof complexity before and after Mathlib migration

param(
    [string]$OriginalFile = "",
    [string]$MathlibFile = "",
    [string]$OutputFormat = "Detailed", # Detailed, Summary, JSON
    [switch]$IncludeMetrics,
    [switch]$Verbose
)

# Complexity analysis configuration
$complexityConfig = @{
    ComplexityMetrics = @{
        "ProofLength" = @{
            Description = "Total lines of proof code"
            Weight = 0.3
            ScaleType = "Linear"
        }
        "TacticComplexity" = @{
            Description = "Sophistication of tactics used"
            Weight = 0.25
            ScaleType = "Exponential"
        }
        "LogicalDepth" = @{
            Description = "Nesting level of proof structure"
            Weight = 0.2
            ScaleType = "Linear"
        }
        "TheoremDependencies" = @{
            Description = "Number of external theorem references"
            Weight = 0.15
            ScaleType = "Linear"
        }
        "SyntaxComplexity" = @{
            Description = "Unicode symbols and advanced notation"
            Weight = 0.1
            ScaleType = "Linear"
        }
    }
    
    TacticComplexityScores = @{
        # Basic tactics (low complexity)
        "trivial" = 1
        "rfl" = 1
        "sorry" = 1
        "assumption" = 2
        
        # Intermediate tactics
        "cases" = 3
        "induction" = 4
        "constructor" = 3
        "left" = 2
        "right" = 2
        "split" = 3
        "use" = 3
        "apply" = 4
        "exact" = 2
        
        # Advanced tactics
        "simp" = 5
        "rw" = 4
        "ring" = 6
        "omega" = 7
        "norm_num" = 5
        "field_simp" = 7
        "abel" = 6
        "linarith" = 8
        "nlinarith" = 9
        "polyrith" = 9
        
        # Expert tactics
        "conv" = 8
        "gcongr" = 7
        "wlog" = 9
        "contrapose" = 6
        "by_contra" = 5
        "classical" = 7
    }
    
    ComplexityCategories = @{
        "Trivial" = @{ Min = 0; Max = 10; Description = "Very simple proofs" }
        "Simple" = @{ Min = 10; Max = 25; Description = "Basic mathematical proofs" }
        "Moderate" = @{ Min = 25; Max = 50; Description = "Standard mathematical arguments" }
        "Complex" = @{ Min = 50; Max = 100; Description = "Advanced mathematical proofs" }
        "Expert" = @{ Min = 100; Max = 200; Description = "Very sophisticated proofs" }
        "Research" = @{ Min = 200; Max = 999; Description = "Research-level complexity" }
    }
}

function Parse-LeanFile {
    param([string]$FilePath)
    
    if (!(Test-Path $FilePath)) {
        throw "File not found: $FilePath"
    }
    
    $content = Get-Content $FilePath
    $analysis = @{
        FilePath = $FilePath
        FileName = Split-Path $FilePath -Leaf
        TotalLines = $content.Count
        Imports = @()
        Theorems = @()
        Definitions = @()
        Lemmas = @()
        TotalProofLines = 0
        UsedTactics = @{}
        SyntaxFeatures = @{}
    }
    
    # Extract imports
    $analysis.Imports = $content | Where-Object { $_ -match '^import\s+' }
    
    # Parse theorems, definitions, and lemmas
    $inProof = $false
    $currentProof = $null
    $proofLines = @()
    $nestingLevel = 0
    
    for ($i = 0; $i -lt $content.Count; $i++) {
        $line = $content[$i].Trim()
        
        # Skip empty lines and comments
        if ($line -eq "" -or $line -match "^--") {
            continue
        }
        
        # Detect start of theorem/lemma/definition
        if ($line -match '^(theorem|lemma|def)\s+(\w+)') {
            $itemType = $matches[1]
            $itemName = $matches[2]
            
            $item = @{
                Name = $itemName
                Type = $itemType
                StartLine = $i + 1
                ProofLines = @()
                TacticsUsed = @{}
                MaxNestingLevel = 0
                TheoremReferences = @()
                HasSorry = $false
            }
            
            # Collect the full item (including proof)
            $itemLines = @($line)
            $bracketCount = 0
            $inByBlock = $false
            
            for ($j = $i + 1; $j -lt $content.Count; $j++) {
                $nextLine = $content[$j].Trim()
                $itemLines += $nextLine
                
                # Track by blocks
                if ($nextLine -match '\bby\b') {
                    $inByBlock = $true
                }
                
                # Track nesting with indentation and keywords
                if ($inByBlock) {
                    $indentLevel = ($content[$j] -replace '\S.*$', '').Length / 2
                    $item.MaxNestingLevel = [math]::Max($item.MaxNestingLevel, $indentLevel)
                    
                    # Extract tactics
                    $tactics = [regex]::Matches($nextLine, '\b(trivial|rfl|sorry|cases|induction|constructor|left|right|split|use|apply|exact|simp|rw|ring|omega|norm_num|field_simp|abel|linarith|nlinarith|polyrith|conv|gcongr|wlog|contrapose|by_contra|classical|assumption)\b')
                    foreach ($match in $tactics) {
                        $tacticName = $match.Value
                        if ($item.TacticsUsed.ContainsKey($tacticName)) {
                            $item.TacticsUsed[$tacticName]++
                        } else {
                            $item.TacticsUsed[$tacticName] = 1
                        }
                    }
                    
                    # Check for sorry
                    if ($nextLine -match '\bsorry\b') {
                        $item.HasSorry = $true
                    }
                    
                    # Extract theorem references
                    $theoremRefs = [regex]::Matches($nextLine, '\b[A-Z][a-zA-Z_]*\.[a-zA-Z_]+\b')
                    foreach ($match in $theoremRefs) {
                        if ($match.Value -notin $item.TheoremReferences) {
                            $item.TheoremReferences += $match.Value
                        }
                    }
                }
                
                # Check for end of item
                if ($nextLine -eq "" -and $j + 1 -lt $content.Count) {
                    $followingLine = $content[$j + 1].Trim()
                    if ($followingLine -match '^(theorem|lemma|def|example|instance)' -or $followingLine -eq "") {
                        break
                    }
                }
                
                # Safety break for very long items
                if ($j - $i > 100) {
                    break
                }
            }
            
            $item.EndLine = $j + 1
            $item.ProofLines = $itemLines
            
            # Add to appropriate collection
            switch ($itemType) {
                "theorem" { $analysis.Theorems += $item }
                "lemma" { $analysis.Lemmas += $item }
                "def" { $analysis.Definitions += $item }
            }
            
            # Update global tactic usage
            foreach ($tactic in $item.TacticsUsed.Keys) {
                if ($analysis.UsedTactics.ContainsKey($tactic)) {
                    $analysis.UsedTactics[$tactic] += $item.TacticsUsed[$tactic]
                } else {
                    $analysis.UsedTactics[$tactic] = $item.TacticsUsed[$tactic]
                }
            }
            
            $i = $j
        }
    }
    
    # Calculate total proof lines
    $analysis.TotalProofLines = ($analysis.Theorems + $analysis.Lemmas | Measure-Object -Property { $_.ProofLines.Count } -Sum).Sum
    
    # Analyze syntax features
    $allContent = $content -join " "
    $analysis.SyntaxFeatures = @{
        UsesUnicode = $allContent -match '[ℕℤℝℚ∀∃λ→↔⟨⟩‹›≤≥≠±∪∩∈∉⊆⊇∅]'
        UsesAdvancedNotation = $allContent -match '[∑∏∫∂∇⊕⊗⊥⊤∧∨¬]'
        UsesSubscripts = $allContent -match '_\{[^}]+\}'
        UsesSuperscripts = $allContent -match '\^[0-9]+'
        HasComplexTypes = $allContent -match '→.*→|∀.*∀|∃.*∃'
    }
    
    if ($Verbose) {
        Write-Host "Parsed $($analysis.FileName):" -ForegroundColor Cyan
        Write-Host "  Theorems: $($analysis.Theorems.Count)" -ForegroundColor Gray
        Write-Host "  Lemmas: $($analysis.Lemmas.Count)" -ForegroundColor Gray
        Write-Host "  Definitions: $($analysis.Definitions.Count)" -ForegroundColor Gray
        Write-Host "  Total proof lines: $($analysis.TotalProofLines)" -ForegroundColor Gray
        Write-Host "  Unique tactics: $($analysis.UsedTactics.Count)" -ForegroundColor Gray
    }
    
    return $analysis
}

function Calculate-ComplexityScore {
    param([hashtable]$Analysis)
    
    $scores = @{}
    $totalScore = 0
    
    # 1. Proof Length Score
    $proofLengthScore = $Analysis.TotalProofLines * 0.5
    $scores["ProofLength"] = $proofLengthScore
    
    # 2. Tactic Complexity Score
    $tacticScore = 0
    foreach ($tactic in $Analysis.UsedTactics.Keys) {
        $tacticComplexity = if ($complexityConfig.TacticComplexityScores.ContainsKey($tactic)) {
            $complexityConfig.TacticComplexityScores[$tactic]
        } else {
            3  # Default complexity for unknown tactics
        }
        $tacticScore += $tacticComplexity * $Analysis.UsedTactics[$tactic]
    }
    $scores["TacticComplexity"] = $tacticScore
    
    # 3. Logical Depth Score
    $maxNesting = ($Analysis.Theorems + $Analysis.Lemmas | Measure-Object -Property MaxNestingLevel -Maximum).Maximum
    if ($maxNesting -eq $null) { $maxNesting = 0 }
    $logicalDepthScore = $maxNesting * 3
    $scores["LogicalDepth"] = $logicalDepthScore
    
    # 4. Theorem Dependencies Score
    $totalDependencies = ($Analysis.Theorems + $Analysis.Lemmas | ForEach-Object { $_.TheoremReferences.Count } | Measure-Object -Sum).Sum
    $dependencyScore = $totalDependencies * 2
    $scores["TheoremDependencies"] = $dependencyScore
    
    # 5. Syntax Complexity Score
    $syntaxScore = 0
    if ($Analysis.SyntaxFeatures.UsesUnicode) { $syntaxScore += 5 }
    if ($Analysis.SyntaxFeatures.UsesAdvancedNotation) { $syntaxScore += 8 }
    if ($Analysis.SyntaxFeatures.UsesSubscripts) { $syntaxScore += 3 }
    if ($Analysis.SyntaxFeatures.UsesSuperscripts) { $syntaxScore += 2 }
    if ($Analysis.SyntaxFeatures.HasComplexTypes) { $syntaxScore += 6 }
    $scores["SyntaxComplexity"] = $syntaxScore
    
    # Calculate weighted total
    foreach ($metric in $complexityConfig.ComplexityMetrics.Keys) {
        $weight = $complexityConfig.ComplexityMetrics[$metric].Weight
        $totalScore += $scores[$metric] * $weight
    }
    
    # Determine complexity category
    $category = "Unknown"
    foreach ($catName in $complexityConfig.ComplexityCategories.Keys) {
        $catInfo = $complexityConfig.ComplexityCategories[$catName]
        if ($totalScore -ge $catInfo.Min -and $totalScore -lt $catInfo.Max) {
            $category = $catName
            break
        }
    }
    
    return @{
        TotalScore = [math]::Round($totalScore, 2)
        Category = $category
        ComponentScores = $scores
        ScoreBreakdown = @{
            ProofLength = @{
                Score = $proofLengthScore
                Weight = $complexityConfig.ComplexityMetrics["ProofLength"].Weight
                WeightedScore = $proofLengthScore * $complexityConfig.ComplexityMetrics["ProofLength"].Weight
            }
            TacticComplexity = @{
                Score = $tacticScore
                Weight = $complexityConfig.ComplexityMetrics["TacticComplexity"].Weight
                WeightedScore = $tacticScore * $complexityConfig.ComplexityMetrics["TacticComplexity"].Weight
            }
            LogicalDepth = @{
                Score = $logicalDepthScore
                Weight = $complexityConfig.ComplexityMetrics["LogicalDepth"].Weight
                WeightedScore = $logicalDepthScore * $complexityConfig.ComplexityMetrics["LogicalDepth"].Weight
            }
            TheoremDependencies = @{
                Score = $dependencyScore
                Weight = $complexityConfig.ComplexityMetrics["TheoremDependencies"].Weight
                WeightedScore = $dependencyScore * $complexityConfig.ComplexityMetrics["TheoremDependencies"].Weight
            }
            SyntaxComplexity = @{
                Score = $syntaxScore
                Weight = $complexityConfig.ComplexityMetrics["SyntaxComplexity"].Weight
                WeightedScore = $syntaxScore * $complexityConfig.ComplexityMetrics["SyntaxComplexity"].Weight
            }
        }
    }
}

function Compare-ProofComplexity {
    param([hashtable]$OriginalAnalysis, [hashtable]$MathlibAnalysis)
    
    $originalComplexity = Calculate-ComplexityScore $OriginalAnalysis
    $mathlibComplexity = Calculate-ComplexityScore $MathlibAnalysis
    
    $comparison = @{
        Original = @{
            Analysis = $OriginalAnalysis
            Complexity = $originalComplexity
        }
        Mathlib = @{
            Analysis = $MathlibAnalysis
            Complexity = $mathlibComplexity
        }
        Changes = @{
            TotalScoreChange = $mathlibComplexity.TotalScore - $originalComplexity.TotalScore
            CategoryChange = @{
                From = $originalComplexity.Category
                To = $mathlibComplexity.Category
            }
            MetricChanges = @{}
        }
        Insights = @()
    }
    
    # Calculate metric changes
    foreach ($metric in $complexityConfig.ComplexityMetrics.Keys) {
        $originalScore = $originalComplexity.ComponentScores[$metric]
        $mathlibScore = $mathlibComplexity.ComponentScores[$metric]
        $change = $mathlibScore - $originalScore
        $percentChange = if ($originalScore -gt 0) { ($change / $originalScore) * 100 } else { 0 }
        
        $comparison.Changes.MetricChanges[$metric] = @{
            Original = $originalScore
            Mathlib = $mathlibScore
            Change = $change
            PercentChange = [math]::Round($percentChange, 1)
        }
    }
    
    # Generate insights
    $totalChange = $comparison.Changes.TotalScoreChange
    if ($totalChange > 5) {
        $comparison.Insights += "Mathlib migration significantly increased complexity (+$($totalChange.ToString('F1')) points)"
    } elseif ($totalChange < -5) {
        $comparison.Insights += "Mathlib migration significantly reduced complexity ($($totalChange.ToString('F1')) points)"
    } else {
        $comparison.Insights += "Mathlib migration had minimal impact on overall complexity"
    }
    
    # Analyze specific changes
    $tacticChange = $comparison.Changes.MetricChanges["TacticComplexity"].PercentChange
    if ($tacticChange > 20) {
        $comparison.Insights += "Tactics became significantly more sophisticated (+$($tacticChange.ToString('F1'))%)"
    } elseif ($tacticChange < -20) {
        $comparison.Insights += "Tactics became simpler (-$($tacticChange.ToString('F1'))%)"
    }
    
    $lengthChange = $comparison.Changes.MetricChanges["ProofLength"].PercentChange
    if ($lengthChange > 15) {
        $comparison.Insights += "Proofs became notably longer (+$($lengthChange.ToString('F1'))%)"
    } elseif ($lengthChange < -15) {
        $comparison.Insights += "Proofs became notably shorter ($($lengthChange.ToString('F1'))%)"
    }
    
    $dependencyChange = $comparison.Changes.MetricChanges["TheoremDependencies"].PercentChange
    if ($dependencyChange > 25) {
        $comparison.Insights += "Much heavier reliance on external theorems (+$($dependencyChange.ToString('F1'))%)"
    } elseif ($dependencyChange < -25) {
        $comparison.Insights += "Reduced dependence on external theorems ($($dependencyChange.ToString('F1'))%)"
    }
    
    return $comparison
}

function Format-ComparisonResult {
    param([hashtable]$Comparison, [string]$Format)
    
    switch ($Format) {
        "Summary" {
            return Format-SummaryReport $Comparison
        }
        "JSON" {
            return $Comparison | ConvertTo-Json -Depth 10
        }
        default {
            return Format-DetailedReport $Comparison
        }
    }
}

function Format-SummaryReport {
    param([hashtable]$Comparison)
    
    $report = @"
Proof Complexity Comparison Summary
==================================

Original Complexity: $($Comparison.Original.Complexity.TotalScore) ($($Comparison.Original.Complexity.Category))
Mathlib Complexity:  $($Comparison.Mathlib.Complexity.TotalScore) ($($Comparison.Mathlib.Complexity.Category))
Change: $($Comparison.Changes.TotalScoreChange.ToString('+0.0;-0.0;0.0')) points

Key Changes:
"@

    foreach ($insight in $Comparison.Insights) {
        $report += "`n- $insight"
    }
    
    return $report
}

function Format-DetailedReport {
    param([hashtable]$Comparison)
    
    $report = @"
Detailed Proof Complexity Comparison
====================================

File Comparison:
  Original: $($Comparison.Original.Analysis.FileName)
  Mathlib:  $($Comparison.Mathlib.Analysis.FileName)

Overall Complexity:
  Original: $($Comparison.Original.Complexity.TotalScore) points ($($Comparison.Original.Complexity.Category))
  Mathlib:  $($Comparison.Mathlib.Complexity.TotalScore) points ($($Comparison.Mathlib.Complexity.Category))
  Change:   $($Comparison.Changes.TotalScoreChange.ToString('+0.0;-0.0;0.0')) points

Metric Breakdown:
"@

    foreach ($metric in $complexityConfig.ComplexityMetrics.Keys) {
        $change = $Comparison.Changes.MetricChanges[$metric]
        $report += @"

$metric`:
  Original: $($change.Original.ToString('F1'))
  Mathlib:  $($change.Mathlib.ToString('F1'))
  Change:   $($change.Change.ToString('+0.0;-0.0;0.0')) ($($change.PercentChange.ToString('+0.0;-0.0;0.0'))%)
"@
    }
    
    # File statistics comparison
    $report += @"

File Statistics Comparison:
                    Original    Mathlib     Change
Total Lines:        $($Comparison.Original.Analysis.TotalLines.ToString().PadLeft(8))    $($Comparison.Mathlib.Analysis.TotalLines.ToString().PadLeft(7))    $((($Comparison.Mathlib.Analysis.TotalLines - $Comparison.Original.Analysis.TotalLines).ToString('+0;-0;0')).PadLeft(9))
Proof Lines:        $($Comparison.Original.Analysis.TotalProofLines.ToString().PadLeft(8))    $($Comparison.Mathlib.Analysis.TotalProofLines.ToString().PadLeft(7))    $((($Comparison.Mathlib.Analysis.TotalProofLines - $Comparison.Original.Analysis.TotalProofLines).ToString('+0;-0;0')).PadLeft(9))
Theorems:           $($Comparison.Original.Analysis.Theorems.Count.ToString().PadLeft(8))    $($Comparison.Mathlib.Analysis.Theorems.Count.ToString().PadLeft(7))    $((($Comparison.Mathlib.Analysis.Theorems.Count - $Comparison.Original.Analysis.Theorems.Count).ToString('+0;-0;0')).PadLeft(9))
Unique Tactics:     $($Comparison.Original.Analysis.UsedTactics.Count.ToString().PadLeft(8))    $($Comparison.Mathlib.Analysis.UsedTactics.Count.ToString().PadLeft(7))    $((($Comparison.Mathlib.Analysis.UsedTactics.Count - $Comparison.Original.Analysis.UsedTactics.Count).ToString('+0;-0;0')).PadLeft(9))
"@
    
    # Tactic comparison
    $allTactics = ($Comparison.Original.Analysis.UsedTactics.Keys + $Comparison.Mathlib.Analysis.UsedTactics.Keys) | Sort-Object -Unique
    if ($allTactics.Count -gt 0) {
        $report += "`n`nTactic Usage Comparison:"
        $report += "`nTactic              Original    Mathlib     Change"
        $report += "`n" + "-" * 50
        
        foreach ($tactic in $allTactics) {
            $origCount = if ($Comparison.Original.Analysis.UsedTactics.ContainsKey($tactic)) { $Comparison.Original.Analysis.UsedTactics[$tactic] } else { 0 }
            $mathlibCount = if ($Comparison.Mathlib.Analysis.UsedTactics.ContainsKey($tactic)) { $Comparison.Mathlib.Analysis.UsedTactics[$tactic] } else { 0 }
            $change = $mathlibCount - $origCount
            
            $report += "`n$($tactic.PadRight(18))  $($origCount.ToString().PadLeft(8))    $($mathlibCount.ToString().PadLeft(7))    $($change.ToString('+0;-0;0').PadLeft(9))"
        }
    }
    
    if ($Comparison.Insights.Count -gt 0) {
        $report += "`n`nKey Insights:"
        foreach ($insight in $Comparison.Insights) {
            $report += "`n- $insight"
        }
    }
    
    return $report
}

# Main execution
if ($OriginalFile -and $MathlibFile) {
    Write-Host "Analyzing proof complexity comparison..." -ForegroundColor Cyan
    
    try {
        $originalAnalysis = Parse-LeanFile $OriginalFile
        $mathlibAnalysis = Parse-LeanFile $MathlibFile
        
        $comparison = Compare-ProofComplexity $originalAnalysis $mathlibAnalysis
        $report = Format-ComparisonResult $comparison $OutputFormat
        
        Write-Host $report
        
        # Save report if requested
        if ($IncludeMetrics) {
            $reportPath = "mathlib-comparison\complexity_comparison_$(Get-Date -Format 'yyyyMMdd_HHmmss').txt"
            $report | Out-File -FilePath $reportPath -Encoding UTF8
            Write-Host "`nDetailed report saved to: $reportPath" -ForegroundColor Green
        }
        
    } catch {
        Write-Host "Error during complexity analysis: $($_.Exception.Message)" -ForegroundColor Red
    }
} else {
    Write-Host @"
Proof Complexity Analyzer

Usage:
  .\ProofComplexityAnalyzer.ps1 -OriginalFile <path> -MathlibFile <path> [-OutputFormat <format>] [-IncludeMetrics] [-Verbose]

Output Formats:
  Detailed - Full comparison report (default)
  Summary  - Brief comparison summary
  JSON     - Machine-readable output

Examples:
  .\ProofComplexityAnalyzer.ps1 -OriginalFile "original.lean" -MathlibFile "migrated.lean"
  .\ProofComplexityAnalyzer.ps1 -OriginalFile "proof.lean" -MathlibFile "proof_mathlib.lean" -OutputFormat Summary
"@ -ForegroundColor Cyan
}

Export-ModuleMember -Function Parse-LeanFile, Calculate-ComplexityScore, Compare-ProofComplexity