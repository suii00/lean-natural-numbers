# Learning Cost Evaluator
# Assesses the educational investment required for Mathlib adoption

param(
    [string]$OriginalFile = "",
    [string]$MathlibFile = "",
    [string]$UserLevel = "Intermediate", # Beginner, Intermediate, Advanced
    [string]$OutputFormat = "Detailed", # Detailed, Summary, JSON
    [switch]$IncludeTrainingPlan,
    [switch]$Verbose
)

# Learning cost evaluation configuration
$learningConfig = @{
    UserLevels = @{
        "Beginner" = @{
            Description = "New to theorem proving and Lean"
            BaseKnowledge = 1
            LearningMultiplier = 2.0
            EstimatedHours = @{
                BasicConcepts = 40
                TacticFamiliarity = 60
                MathlibNavigation = 30
            }
        }
        "Intermediate" = @{
            Description = "Familiar with Lean basics"
            BaseKnowledge = 5
            LearningMultiplier = 1.0
            EstimatedHours = @{
                BasicConcepts = 10
                TacticFamiliarity = 25
                MathlibNavigation = 15
            }
        }
        "Advanced" = @{
            Description = "Experienced with Lean and theorem proving"
            BaseKnowledge = 8
            LearningMultiplier = 0.5
            EstimatedHours = @{
                BasicConcepts = 2
                TacticFamiliarity = 8
                MathlibNavigation = 5
            }
        }
    }
    
    ConceptDifficulty = @{
        # Basic concepts
        "trivial" = @{ Difficulty = 1; Category = "Basic"; Prerequisites = @() }
        "rfl" = @{ Difficulty = 1; Category = "Basic"; Prerequisites = @() }
        "assumption" = @{ Difficulty = 2; Category = "Basic"; Prerequisites = @() }
        "exact" = @{ Difficulty = 2; Category = "Basic"; Prerequisites = @() }
        
        # Structural reasoning
        "cases" = @{ Difficulty = 4; Category = "Structural"; Prerequisites = @("Pattern matching", "Inductive types") }
        "induction" = @{ Difficulty = 6; Category = "Structural"; Prerequisites = @("Mathematical induction", "Inductive types") }
        "constructor" = @{ Difficulty = 3; Category = "Structural"; Prerequisites = @("Data constructors") }
        "split" = @{ Difficulty = 3; Category = "Structural"; Prerequisites = @("Conjunction") }
        
        # Mathlib-specific tactics
        "simp" = @{ Difficulty = 7; Category = "Simplification"; Prerequisites = @("Simp lemmas", "Rewriting rules") }
        "rw" = @{ Difficulty = 5; Category = "Rewriting"; Prerequisites = @("Equality reasoning", "Rewrite rules") }
        "ring" = @{ Difficulty = 8; Category = "Algebraic"; Prerequisites = @("Ring theory", "Algebraic structures") }
        "omega" = @{ Difficulty = 9; Category = "Arithmetic"; Prerequisites = @("Linear arithmetic", "Decision procedures") }
        "linarith" = @{ Difficulty = 8; Category = "Arithmetic"; Prerequisites = @("Linear inequalities", "Ordered fields") }
        "nlinarith" = @{ Difficulty = 10; Category = "Arithmetic"; Prerequisites = @("Nonlinear arithmetic", "Polynomial inequalities") }
        "conv" = @{ Difficulty = 9; Category = "Advanced"; Prerequisites = @("Advanced rewriting", "Expression manipulation") }
        "wlog" = @{ Difficulty = 10; Category = "Advanced"; Prerequisites = @("Symmetry arguments", "Case analysis") }
        
        # Import complexity
        "Mathlib.Tactic.Basic" = @{ Difficulty = 3; Category = "Import"; Prerequisites = @("Basic Mathlib structure") }
        "Mathlib.Algebra.Ring" = @{ Difficulty = 6; Category = "Import"; Prerequisites = @("Ring theory", "Algebraic structures") }
        "Mathlib.Tactic.Linarith" = @{ Difficulty = 7; Category = "Import"; Prerequisites = @("Linear arithmetic theory") }
        "Mathlib.Data.Nat.Basic" = @{ Difficulty = 4; Category = "Import"; Prerequisites = @("Natural number theory") }
    }
    
    LearningCategories = @{
        "Immediate" = @{ MaxHours = 2; Description = "Can learn immediately" }
        "Quick" = @{ MaxHours = 8; Description = "Can learn in a day" }
        "Moderate" = @{ MaxHours = 20; Description = "Requires several days" }
        "Substantial" = @{ MaxHours = 40; Description = "Requires weeks of study" }
        "Intensive" = @{ MaxHours = 100; Description = "Requires intensive study" }
        "Expert" = @{ MaxHours = 999; Description = "Expert-level knowledge required" }
    }
    
    TopicAreas = @{
        "BasicTactics" = @{
            Description = "Fundamental proof tactics"
            Tactics = @("trivial", "rfl", "assumption", "exact", "sorry")
            BaselineHours = 5
        }
        "StructuralReasoning" = @{
            Description = "Pattern matching and inductive reasoning"
            Tactics = @("cases", "induction", "constructor", "split", "left", "right")
            BaselineHours = 15
        }
        "EqualityReasoning" = @{
            Description = "Working with equalities and rewrites"
            Tactics = @("rw", "simp", "calc")
            BaselineHours = 12
        }
        "AlgebraicAutomation" = @{
            Description = "Automated algebraic tactics"
            Tactics = @("ring", "field_simp", "abel", "polyrith")
            BaselineHours = 20
        }
        "ArithmeticDecision" = @{
            Description = "Arithmetic decision procedures"
            Tactics = @("omega", "linarith", "nlinarith", "norm_num")
            BaselineHours = 25
        }
        "AdvancedTechniques" = @{
            Description = "Sophisticated proof techniques"
            Tactics = @("conv", "wlog", "by_contra", "contrapose")
            BaselineHours = 30
        }
        "MathlibNavigation" = @{
            Description = "Understanding Mathlib structure and imports"
            Tactics = @()
            BaselineHours = 10
        }
    }
}

function Analyze-LearningRequirements {
    param([string]$FilePath)
    
    if (!(Test-Path $FilePath)) {
        throw "File not found: $FilePath"
    }
    
    $content = Get-Content $FilePath
    $analysis = @{
        FilePath = $FilePath
        FileName = Split-Path $FilePath -Leaf
        RequiredTactics = @{}
        RequiredImports = @()
        RequiredConcepts = @{}
        TopicAreas = @{}
        NewConceptsIntroduced = 0
        TotalLearningComplexity = 0
    }
    
    # Extract imports
    $imports = $content | Where-Object { $_ -match '^import\s+' }
    foreach ($import in $imports) {
        $importName = [regex]::Match($import, 'import\s+(.+)').Groups[1].Value.Trim()
        $analysis.RequiredImports += $importName
        
        if ($learningConfig.ConceptDifficulty.ContainsKey($importName)) {
            $conceptInfo = $learningConfig.ConceptDifficulty[$importName]
            $analysis.RequiredConcepts[$importName] = $conceptInfo
            $analysis.TotalLearningComplexity += $conceptInfo.Difficulty
        }
    }
    
    # Extract tactics used
    $allContent = $content -join " "
    foreach ($tacticName in $learningConfig.ConceptDifficulty.Keys) {
        if ($tacticName -notmatch "^Mathlib" -and $allContent -match "\b$tacticName\b") {
            $matches = [regex]::Matches($allContent, "\b$tacticName\b")
            $analysis.RequiredTactics[$tacticName] = $matches.Count
            
            if ($learningConfig.ConceptDifficulty.ContainsKey($tacticName)) {
                $conceptInfo = $learningConfig.ConceptDifficulty[$tacticName]
                $analysis.RequiredConcepts[$tacticName] = $conceptInfo
                $analysis.TotalLearningComplexity += $conceptInfo.Difficulty * $matches.Count
            }
        }
    }
    
    # Categorize by topic areas
    foreach ($topicName in $learningConfig.TopicAreas.Keys) {
        $topicInfo = $learningConfig.TopicAreas[$topicName]
        $topicTactics = @()
        
        foreach ($tactic in $topicInfo.Tactics) {
            if ($analysis.RequiredTactics.ContainsKey($tactic)) {
                $topicTactics += @{
                    Tactic = $tactic
                    Usage = $analysis.RequiredTactics[$tactic]
                }
            }
        }
        
        if ($topicTactics.Count -gt 0) {
            $analysis.TopicAreas[$topicName] = @{
                Description = $topicInfo.Description
                RequiredTactics = $topicTactics
                BaselineHours = $topicInfo.BaselineHours
                IsRequired = $true
            }
        }
    }
    
    # Count new concepts
    $analysis.NewConceptsIntroduced = $analysis.RequiredConcepts.Keys.Count
    
    if ($Verbose) {
        Write-Host "Learning analysis for $($analysis.FileName):" -ForegroundColor Cyan
        Write-Host "  Required tactics: $($analysis.RequiredTactics.Count)" -ForegroundColor Gray
        Write-Host "  Required imports: $($analysis.RequiredImports.Count)" -ForegroundColor Gray
        Write-Host "  New concepts: $($analysis.NewConceptsIntroduced)" -ForegroundColor Gray
        Write-Host "  Topic areas: $($analysis.TopicAreas.Count)" -ForegroundColor Gray
    }
    
    return $analysis
}

function Calculate-LearningCost {
    param([hashtable]$Analysis, [string]$UserLevel)
    
    $userProfile = $learningConfig.UserLevels[$UserLevel]
    $multiplier = $userProfile.LearningMultiplier
    
    $costEstimate = @{
        UserLevel = $UserLevel
        UserProfile = $userProfile
        TotalEstimatedHours = 0
        CategoryBreakdown = @{}
        TopicBreakdown = @{}
        ConceptDifficulty = @{
            Easy = 0
            Medium = 0  
            Hard = 0
            Expert = 0
        }
        LearningPath = @()
        Prerequisites = @()
        TimeToProductivity = @{
            Basic = 0
            Intermediate = 0
            Advanced = 0
        }
    }
    
    # Calculate hours for each topic area
    foreach ($topicName in $Analysis.TopicAreas.Keys) {
        $topicInfo = $Analysis.TopicAreas[$topicName]
        $baseHours = $topicInfo.BaselineHours
        $adjustedHours = $baseHours * $multiplier
        
        # Adjust based on complexity of tactics actually used
        $complexityBonus = 0
        foreach ($tacticInfo in $topicInfo.RequiredTactics) {
            $tacticName = $tacticInfo.Tactic
            if ($learningConfig.ConceptDifficulty.ContainsKey($tacticName)) {
                $difficulty = $learningConfig.ConceptDifficulty[$tacticName].Difficulty
                $complexityBonus += ($difficulty - 5) * 0.5  # Bonus/penalty based on difficulty
            }
        }
        
        $finalHours = [math]::Max(1, $adjustedHours + $complexityBonus)
        
        $costEstimate.TopicBreakdown[$topicName] = @{
            BaseHours = $baseHours
            AdjustedHours = [math]::Round($adjustedHours, 1)
            ComplexityBonus = [math]::Round($complexityBonus, 1)
            FinalHours = [math]::Round($finalHours, 1)
            TacticsRequired = $topicInfo.RequiredTactics.Count
        }
        
        $costEstimate.TotalEstimatedHours += $finalHours
    }
    
    # Categorize concepts by difficulty
    foreach ($conceptName in $Analysis.RequiredConcepts.Keys) {
        $conceptInfo = $Analysis.RequiredConcepts[$conceptName]
        $difficulty = $conceptInfo.Difficulty
        
        if ($difficulty -le 3) {
            $costEstimate.ConceptDifficulty.Easy++
        } elseif ($difficulty -le 6) {
            $costEstimate.ConceptDifficulty.Medium++
        } elseif ($difficulty -le 8) {
            $costEstimate.ConceptDifficulty.Hard++
        } else {
            $costEstimate.ConceptDifficulty.Expert++
        }
        
        # Collect prerequisites
        foreach ($prereq in $conceptInfo.Prerequisites) {
            if ($prereq -notin $costEstimate.Prerequisites) {
                $costEstimate.Prerequisites += $prereq
            }
        }
    }
    
    # Determine learning category
    $totalHours = $costEstimate.TotalEstimatedHours
    $learningCategory = "Expert"
    
    foreach ($catName in $learningConfig.LearningCategories.Keys) {
        $catInfo = $learningConfig.LearningCategories[$catName]
        if ($totalHours -le $catInfo.MaxHours) {
            $learningCategory = $catName
            break
        }
    }
    
    $costEstimate.LearningCategory = $learningCategory
    
    # Estimate time to productivity levels
    $costEstimate.TimeToProductivity.Basic = [math]::Round($totalHours * 0.3, 1)
    $costEstimate.TimeToProductivity.Intermediate = [math]::Round($totalHours * 0.7, 1) 
    $costEstimate.TimeToProductivity.Advanced = [math]::Round($totalHours, 1)
    
    # Generate learning path
    $sortedTopics = $costEstimate.TopicBreakdown.GetEnumerator() | Sort-Object { $_.Value.FinalHours }
    foreach ($topic in $sortedTopics) {
        $costEstimate.LearningPath += @{
            Topic = $topic.Key
            EstimatedHours = $topic.Value.FinalHours
            Description = if ($learningConfig.TopicAreas.ContainsKey($topic.Key)) { 
                $learningConfig.TopicAreas[$topic.Key].Description 
            } else { 
                "Advanced topic" 
            }
        }
    }
    
    return $costEstimate
}

function Compare-LearningCosts {
    param([hashtable]$OriginalAnalysis, [hashtable]$MathlibAnalysis, [string]$UserLevel)
    
    $originalCost = Calculate-LearningCost $OriginalAnalysis $UserLevel
    $mathlibCost = Calculate-LearningCost $MathlibAnalysis $UserLevel
    
    $comparison = @{
        UserLevel = $UserLevel
        Original = @{
            Analysis = $OriginalAnalysis
            LearningCost = $originalCost
        }
        Mathlib = @{
            Analysis = $MathlibAnalysis
            LearningCost = $mathlibCost
        }
        Changes = @{
            AdditionalHours = $mathlibCost.TotalEstimatedHours - $originalCost.TotalEstimatedHours
            NewConcepts = $MathlibAnalysis.NewConceptsIntroduced - $OriginalAnalysis.NewConceptsIntroduced
            NewTopicAreas = @()
            ConceptDifficultyChange = @{}
            LearningCategoryChange = @{
                From = $originalCost.LearningCategory
                To = $mathlibCost.LearningCategory
            }
        }
        Insights = @()
        Recommendations = @()
    }
    
    # Find new topic areas
    foreach ($topicName in $mathlibCost.TopicBreakdown.Keys) {
        if (-not $originalCost.TopicBreakdown.ContainsKey($topicName)) {
            $comparison.Changes.NewTopicAreas += $topicName
        }
    }
    
    # Compare concept difficulty distribution
    foreach ($diffLevel in @("Easy", "Medium", "Hard", "Expert")) {
        $originalCount = $originalCost.ConceptDifficulty[$diffLevel]
        $mathlibCount = $mathlibCost.ConceptDifficulty[$diffLevel]
        $change = $mathlibCount - $originalCount
        
        $comparison.Changes.ConceptDifficultyChange[$diffLevel] = @{
            Original = $originalCount
            Mathlib = $mathlibCount
            Change = $change
        }
    }
    
    # Generate insights
    $hourIncrease = $comparison.Changes.AdditionalHours
    if ($hourIncrease -gt 30) {
        $comparison.Insights += "Mathlib adoption requires substantial additional learning (+$($hourIncrease.ToString('F1')) hours)"
    } elseif ($hourIncrease -gt 10) {
        $comparison.Insights += "Moderate learning investment required for Mathlib (+$($hourIncrease.ToString('F1')) hours)"
    } elseif ($hourIncrease -gt 0) {
        $comparison.Insights += "Minimal additional learning required (+$($hourIncrease.ToString('F1')) hours)"
    } else {
        $comparison.Insights += "Mathlib may actually simplify the learning requirements"
    }
    
    if ($comparison.Changes.NewTopicAreas.Count -gt 0) {
        $comparison.Insights += "Introduces $($comparison.Changes.NewTopicAreas.Count) new topic areas: $($comparison.Changes.NewTopicAreas -join ', ')"
    }
    
    $expertIncrease = $comparison.Changes.ConceptDifficultyChange["Expert"].Change
    if ($expertIncrease -gt 0) {
        $comparison.Insights += "Adds $expertIncrease expert-level concepts"
    }
    
    # Generate recommendations
    if ($hourIncrease -gt 20 -and $UserLevel -eq "Beginner") {
        $comparison.Recommendations += "Consider gradual adoption - start with basic Mathlib imports before advanced tactics"
    }
    
    if ($comparison.Changes.NewTopicAreas -contains "AlgebraicAutomation") {
        $comparison.Recommendations += "Focus learning on algebraic automation tactics - they provide high value for the investment"
    }
    
    if ($comparison.Changes.NewTopicAreas -contains "ArithmeticDecision") {
        $comparison.Recommendations += "Arithmetic decision procedures can greatly simplify proofs - prioritize learning these"
    }
    
    if ($mathlibCost.Prerequisites.Count -gt 10) {
        $comparison.Recommendations += "Review mathematical prerequisites before diving into Mathlib tactics"
    }
    
    return $comparison
}

function Format-LearningCostReport {
    param([hashtable]$Comparison, [string]$Format)
    
    switch ($Format) {
        "Summary" {
            return Format-SummaryLearningCost $Comparison
        }
        "JSON" {
            return $Comparison | ConvertTo-Json -Depth 10
        }
        default {
            return Format-DetailedLearningCost $Comparison
        }
    }
}

function Format-DetailedLearningCost {
    param([hashtable]$Comparison)
    
    $report = @"
Learning Cost Evaluation Report
==============================

User Level: $($Comparison.UserLevel) 
Files Compared:
  Original: $($Comparison.Original.Analysis.FileName)
  Mathlib:  $($Comparison.Mathlib.Analysis.FileName)

Learning Investment Summary:
  Original estimated hours: $($Comparison.Original.LearningCost.TotalEstimatedHours.ToString('F1'))
  Mathlib estimated hours:  $($Comparison.Mathlib.LearningCost.TotalEstimatedHours.ToString('F1'))
  Additional investment:    $($Comparison.Changes.AdditionalHours.ToString('+0.0;-0.0;0.0')) hours

Learning Category:
  Original: $($Comparison.Original.LearningCost.LearningCategory)
  Mathlib:  $($Comparison.Mathlib.LearningCost.LearningCategory)

Concept Difficulty Distribution:
                Original    Mathlib     Change
Easy concepts:  $($Comparison.Original.LearningCost.ConceptDifficulty.Easy.ToString().PadLeft(8))    $($Comparison.Mathlib.LearningCost.ConceptDifficulty.Easy.ToString().PadLeft(7))    $($Comparison.Changes.ConceptDifficultyChange["Easy"].Change.ToString('+0;-0;0').PadLeft(9))
Medium concepts:$($Comparison.Original.LearningCost.ConceptDifficulty.Medium.ToString().PadLeft(8))    $($Comparison.Mathlib.LearningCost.ConceptDifficulty.Medium.ToString().PadLeft(7))    $($Comparison.Changes.ConceptDifficultyChange["Medium"].Change.ToString('+0;-0;0').PadLeft(9))
Hard concepts:  $($Comparison.Original.LearningCost.ConceptDifficulty.Hard.ToString().PadLeft(8))    $($Comparison.Mathlib.LearningCost.ConceptDifficulty.Hard.ToString().PadLeft(7))    $($Comparison.Changes.ConceptDifficultyChange["Hard"].Change.ToString('+0;-0;0').PadLeft(9))
Expert concepts:$($Comparison.Original.LearningCost.ConceptDifficulty.Expert.ToString().PadLeft(8))    $($Comparison.Mathlib.LearningCost.ConceptDifficulty.Expert.ToString().PadLeft(7))    $($Comparison.Changes.ConceptDifficultyChange["Expert"].Change.ToString('+0;-0;0').PadLeft(9))

Time to Productivity:
  Basic level:        $($Comparison.Mathlib.LearningCost.TimeToProductivity.Basic) hours
  Intermediate level: $($Comparison.Mathlib.LearningCost.TimeToProductivity.Intermediate) hours  
  Advanced level:     $($Comparison.Mathlib.LearningCost.TimeToProductivity.Advanced) hours

Topic Area Breakdown:
"@

    foreach ($topic in $Comparison.Mathlib.LearningCost.TopicBreakdown.GetEnumerator() | Sort-Object { $_.Value.FinalHours } -Descending) {
        $report += "`n$($topic.Key.PadRight(20)): $($topic.Value.FinalHours.ToString('F1').PadLeft(5)) hours ($($topic.Value.TacticsRequired) tactics)"
    }

    if ($Comparison.Changes.NewTopicAreas.Count -gt 0) {
        $report += "`n`nNew Topic Areas Introduced:"
        foreach ($topic in $Comparison.Changes.NewTopicAreas) {
            $topicInfo = $Comparison.Mathlib.LearningCost.TopicBreakdown[$topic]
            $report += "`n- $topic`: $($topicInfo.FinalHours) hours"
        }
    }

    if ($Comparison.Mathlib.LearningCost.Prerequisites.Count -gt 0) {
        $report += "`n`nPrerequisite Knowledge Required:"
        $prereqGroups = $Comparison.Mathlib.LearningCost.Prerequisites | Group-Object | Sort-Object Count -Descending | Select-Object -First 10
        foreach ($prereq in $prereqGroups) {
            $report += "`n- $($prereq.Name)"
        }
    }

    if ($IncludeTrainingPlan) {
        $report += "`n`nRecommended Learning Path:"
        $step = 1
        foreach ($pathItem in $Comparison.Mathlib.LearningCost.LearningPath) {
            $report += "`n$step. $($pathItem.Topic) ($($pathItem.EstimatedHours) hours)"
            $report += "`n   $($pathItem.Description)"
            $step++
        }
    }

    if ($Comparison.Insights.Count -gt 0) {
        $report += "`n`nKey Insights:"
        foreach ($insight in $Comparison.Insights) {
            $report += "`n- $insight"
        }
    }

    if ($Comparison.Recommendations.Count -gt 0) {
        $report += "`n`nLearning Recommendations:"
        foreach ($rec in $Comparison.Recommendations) {
            $report += "`n- $rec"
        }
    }
    
    return $report
}

function Format-SummaryLearningCost {
    param([hashtable]$Comparison)
    
    $report = @"
Learning Cost Summary ($($Comparison.UserLevel) level)
========================================

Learning Investment: $($Comparison.Changes.AdditionalHours.ToString('+0.0;-0.0;0.0')) hours ($($Comparison.Mathlib.LearningCost.LearningCategory))
New concepts: $($Comparison.Changes.NewConcepts)
New topic areas: $($Comparison.Changes.NewTopicAreas.Count)

Time to productivity: $($Comparison.Mathlib.LearningCost.TimeToProductivity.Basic) hours (basic) to $($Comparison.Mathlib.LearningCost.TimeToProductivity.Advanced) hours (advanced)

Key insights:
"@

    foreach ($insight in $Comparison.Insights) {
        $report += "`n- $insight"
    }
    
    return $report
}

# Main execution
if ($OriginalFile -and $MathlibFile) {
    Write-Host "Evaluating learning cost comparison..." -ForegroundColor Cyan
    
    try {
        $originalAnalysis = Analyze-LearningRequirements $OriginalFile
        $mathlibAnalysis = Analyze-LearningRequirements $MathlibFile
        
        $comparison = Compare-LearningCosts $originalAnalysis $mathlibAnalysis $UserLevel
        $report = Format-LearningCostReport $comparison $OutputFormat
        
        Write-Host $report
        
        # Save report if requested
        if ($IncludeTrainingPlan) {
            $reportPath = "mathlib-comparison\learning_cost_$(Get-Date -Format 'yyyyMMdd_HHmmss').txt"
            $report | Out-File -FilePath $reportPath -Encoding UTF8
            Write-Host "`nLearning cost report saved to: $reportPath" -ForegroundColor Green
        }
        
    } catch {
        Write-Host "Error during learning cost evaluation: $($_.Exception.Message)" -ForegroundColor Red
    }
} else {
    Write-Host @"
Learning Cost Evaluator

Usage:
  .\LearningCostEvaluator.ps1 -OriginalFile <path> -MathlibFile <path> [-UserLevel <level>] [-OutputFormat <format>] [-IncludeTrainingPlan] [-Verbose]

Parameters:
  UserLevel          - Beginner, Intermediate, or Advanced (default: Intermediate)
  OutputFormat       - Detailed, Summary, or JSON
  IncludeTrainingPlan - Include detailed learning path recommendations
  Verbose           - Show detailed analysis progress

Examples:
  .\LearningCostEvaluator.ps1 -OriginalFile "original.lean" -MathlibFile "migrated.lean"
  .\LearningCostEvaluator.ps1 -OriginalFile "proof.lean" -MathlibFile "proof_mathlib.lean" -UserLevel Beginner -IncludeTrainingPlan
"@ -ForegroundColor Cyan
}

Export-ModuleMember -Function Analyze-LearningRequirements, Calculate-LearningCost, Compare-LearningCosts