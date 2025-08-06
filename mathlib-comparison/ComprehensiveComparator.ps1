# Comprehensive Mathlib Comparison System
# Combines all comparison components into unified analysis

param(
    [string]$OriginalFile = "",
    [string]$MathlibFile = "",
    [string]$UserLevel = "Intermediate", # Beginner, Intermediate, Advanced
    [string]$OutputFormat = "Full", # Full, Summary, JSON, HTML
    [int]$BenchmarkRuns = 3,
    [switch]$IncludePerformance,
    [switch]$IncludeTrainingPlan,
    [switch]$SaveReport,
    [switch]$Verbose
)

# Import all comparison modules
$scriptPath = Split-Path $MyInvocation.MyCommand.Path -Parent

# Dot source the other comparison scripts
. "$scriptPath\ProofComplexityAnalyzer.ps1"
. "$scriptPath\TacticComparator.ps1"
. "$scriptPath\LearningCostEvaluator.ps1"

if ($IncludePerformance) {
    . "$scriptPath\PerformanceBenchmarker.ps1"
}

# Comprehensive comparison configuration
$comparisonConfig = @{
    ReportSections = @{
        "ExecutiveSummary" = @{
            Description = "High-level overview of migration impact"
            Weight = 0.3
            Priority = 1
        }
        "ComplexityAnalysis" = @{
            Description = "Proof complexity comparison"
            Weight = 0.25
            Priority = 2
        }
        "TacticAnalysis" = @{
            Description = "Tactic usage and availability changes"
            Weight = 0.2
            Priority = 3
        }
        "LearningCostAnalysis" = @{
            Description = "Educational investment assessment"
            Weight = 0.15
            Priority = 4
        }
        "PerformanceAnalysis" = @{
            Description = "Compilation and runtime performance"
            Weight = 0.1
            Priority = 5
        }
    }
    
    ImpactCategories = @{
        "Positive" = @{
            Description = "Benefits of migration"
            Color = "Green"
            Indicators = @("Simplified proofs", "New powerful tactics", "Reduced complexity")
        }
        "Neutral" = @{
            Description = "Minimal impact"
            Color = "Yellow"
            Indicators = @("Similar complexity", "No major changes")
        }
        "Negative" = @{
            Description = "Costs of migration"
            Color = "Red"
            Indicators = @("Increased complexity", "Performance degradation", "High learning cost")
        }
    }
    
    RecommendationTypes = @{
        "HighPriority" = @{ 
            Description = "Critical actions needed"
            Symbol = "⚠️"
            Color = "Red"
        }
        "Medium" = @{
            Description = "Important considerations"
            Symbol = "💡"
            Color = "Yellow"
        }
        "LowPriority" = @{
            Description = "Optional improvements"
            Symbol = "💭"
            Color = "Green"
        }
    }
}

function Run-ComprehensiveComparison {
    param([string]$OriginalFile, [string]$MathlibFile, [string]$UserLevel)
    
    $results = @{
        Files = @{
            Original = $OriginalFile
            Mathlib = $MathlibFile
        }
        UserLevel = $UserLevel
        AnalysisTimestamp = Get-Date
        ComplexityComparison = $null
        TacticComparison = $null
        LearningCostComparison = $null
        PerformanceComparison = $null
        OverallAssessment = @{}
        ExecutiveSummary = @{}
        Recommendations = @{
            HighPriority = @()
            Medium = @()
            LowPriority = @()
        }
    }
    
    Write-Host "Running comprehensive Mathlib comparison..." -ForegroundColor Cyan
    
    try {
        # 1. Complexity Analysis
        Write-Host "  Analyzing proof complexity..." -ForegroundColor Gray
        $originalAnalysis = Parse-LeanFile $OriginalFile
        $mathlibAnalysis = Parse-LeanFile $MathlibFile
        $results.ComplexityComparison = Compare-ProofComplexity $originalAnalysis $mathlibAnalysis
        
        # 2. Tactic Analysis
        Write-Host "  Analyzing tactic usage..." -ForegroundColor Gray
        $originalTactics = Extract-TacticUsage $OriginalFile
        $mathlibTactics = Extract-TacticUsage $MathlibFile
        $results.TacticComparison = Compare-TacticUsage $originalTactics $mathlibTactics
        
        # 3. Learning Cost Analysis
        Write-Host "  Evaluating learning costs..." -ForegroundColor Gray
        $originalLearning = Analyze-LearningRequirements $OriginalFile
        $mathlibLearning = Analyze-LearningRequirements $MathlibFile
        $results.LearningCostComparison = Compare-LearningCosts $originalLearning $mathlibLearning $UserLevel
        
        # 4. Performance Analysis (if requested)
        if ($IncludePerformance) {
            Write-Host "  Benchmarking performance..." -ForegroundColor Gray
            $originalPerf = Measure-LeanCompilation $OriginalFile $BenchmarkRuns
            $mathlibPerf = Measure-LeanCompilation $MathlibFile $BenchmarkRuns
            $results.PerformanceComparison = Compare-Performance $originalPerf $mathlibPerf
        }
        
        # 5. Generate Overall Assessment
        $results.OverallAssessment = Generate-OverallAssessment $results
        
        # 6. Create Executive Summary
        $results.ExecutiveSummary = Create-ExecutiveSummary $results
        
        # 7. Compile Recommendations
        $results.Recommendations = Compile-Recommendations $results
        
        Write-Host "  Comprehensive analysis complete!" -ForegroundColor Green
        
    } catch {
        Write-Host "Error during comprehensive analysis: $($_.Exception.Message)" -ForegroundColor Red
        throw
    }
    
    return $results
}

function Generate-OverallAssessment {
    param([hashtable]$Results)
    
    $assessment = @{
        OverallImpact = "Neutral"
        ImpactScore = 0
        MajorBenefits = @()
        MajorConcerns = @()
        NetComplexityChange = 0
        NetPerformanceChange = 0
        TotalLearningInvestment = 0
        MigrationRecommendation = "Conditional"
    }
    
    # Calculate net complexity change
    if ($Results.ComplexityComparison) {
        $assessment.NetComplexityChange = $Results.ComplexityComparison.Changes.TotalScoreChange
    }
    
    # Calculate net performance change
    if ($Results.PerformanceComparison) {
        $assessment.NetPerformanceChange = $Results.PerformanceComparison.Changes.OverallPerformanceScore
    }
    
    # Calculate total learning investment
    if ($Results.LearningCostComparison) {
        $assessment.TotalLearningInvestment = $Results.LearningCostComparison.Changes.AdditionalHours
    }
    
    # Determine major benefits
    if ($Results.TacticComparison.Changes.TacticsAdded.Count -gt 3) {
        $assessment.MajorBenefits += "Access to $($Results.TacticComparison.Changes.TacticsAdded.Count) new powerful tactics"
    }
    
    if ($assessment.NetComplexityChange -lt -10) {
        $assessment.MajorBenefits += "Significant proof simplification"
    }
    
    $automatedTactics = $Results.TacticComparison.Changes.TacticsAdded | Where-Object { 
        $Results.TacticComparison.Original.FilePath -and
        $tacticDatabase.MathlibTactics.ContainsKey($_) -and 
        $tacticDatabase.MathlibTactics[$_].AutomatesCalculations 
    }
    if ($automatedTactics.Count -gt 0) {
        $assessment.MajorBenefits += "Gained automated calculation tactics"
    }
    
    # Determine major concerns
    if ($assessment.TotalLearningInvestment -gt 30) {
        $assessment.MajorConcerns += "Substantial learning investment required ($($assessment.TotalLearningInvestment.ToString('F1')) hours)"
    }
    
    if ($assessment.NetComplexityChange -gt 20) {
        $assessment.MajorConcerns += "Significant complexity increase"
    }
    
    if ($Results.PerformanceComparison -and $assessment.NetPerformanceChange -lt -100) {
        $assessment.MajorConcerns += "Notable performance degradation"
    }
    
    # Calculate overall impact score
    $impactScore = 0
    
    # Benefits contribute positively
    $impactScore += ($Results.TacticComparison.Changes.TacticsAdded.Count * 10)
    $impactScore -= $assessment.NetComplexityChange
    if ($Results.PerformanceComparison) {
        $impactScore += $assessment.NetPerformanceChange * 0.1
    }
    
    # Costs contribute negatively
    $impactScore -= ($assessment.TotalLearningInvestment * 2)
    
    $assessment.ImpactScore = [math]::Round($impactScore, 1)
    
    # Determine overall impact
    if ($assessment.ImpactScore -gt 20) {
        $assessment.OverallImpact = "Positive"
        $assessment.MigrationRecommendation = "Recommended"
    } elseif ($assessment.ImpactScore -lt -20) {
        $assessment.OverallImpact = "Negative"  
        $assessment.MigrationRecommendation = "Not Recommended"
    } else {
        $assessment.OverallImpact = "Neutral"
        $assessment.MigrationRecommendation = "Conditional"
    }
    
    return $assessment
}

function Create-ExecutiveSummary {
    param([hashtable]$Results)
    
    $summary = @{
        MigrationViability = $Results.OverallAssessment.MigrationRecommendation
        KeyFindings = @()
        CriticalNumbers = @{
            ComplexityChange = if ($Results.ComplexityComparison) { $Results.ComplexityComparison.Changes.TotalScoreChange } else { 0 }
            NewTactics = if ($Results.TacticComparison) { $Results.TacticComparison.Changes.TacticsAdded.Count } else { 0 }
            LearningHours = if ($Results.LearningCostComparison) { $Results.LearningCostComparison.Changes.AdditionalHours } else { 0 }
            PerformanceImpact = if ($Results.PerformanceComparison) { $Results.PerformanceComparison.Changes.OverallPerformanceScore } else { 0 }
        }
        BusinessCase = @{
            Benefits = @()
            Costs = @()
            ROIAssessment = "Neutral"
        }
    }
    
    # Generate key findings
    if ($summary.CriticalNumbers.NewTactics -gt 5) {
        $summary.KeyFindings += "Significant tactical capabilities enhancement (+$($summary.CriticalNumbers.NewTactics) tactics)"
    }
    
    if ($summary.CriticalNumbers.ComplexityChange -lt -5) {
        $summary.KeyFindings += "Proof simplification achieved"
    } elseif ($summary.CriticalNumbers.ComplexityChange -gt 10) {
        $summary.KeyFindings += "Notable complexity increase"
    }
    
    if ($summary.CriticalNumbers.LearningHours -gt 20) {
        $summary.KeyFindings += "Substantial learning investment required"
    }
    
    # Build business case
    if ($Results.OverallAssessment.MajorBenefits.Count -gt 0) {
        $summary.BusinessCase.Benefits = $Results.OverallAssessment.MajorBenefits
    }
    
    if ($Results.OverallAssessment.MajorConcerns.Count -gt 0) {
        $summary.BusinessCase.Costs = $Results.OverallAssessment.MajorConcerns
    }
    
    # ROI Assessment
    $benefitScore = $Results.OverallAssessment.MajorBenefits.Count * 25 + ($summary.CriticalNumbers.NewTactics * 5)
    $costScore = $Results.OverallAssessment.MajorConcerns.Count * 30 + ($summary.CriticalNumbers.LearningHours * 2)
    
    if ($benefitScore -gt $costScore * 1.5) {
        $summary.BusinessCase.ROIAssessment = "High"
    } elseif ($benefitScore -gt $costScore) {
        $summary.BusinessCase.ROIAssessment = "Moderate"
    } else {
        $summary.BusinessCase.ROIAssessment = "Low"
    }
    
    return $summary
}

function Compile-Recommendations {
    param([hashtable]$Results)
    
    $recommendations = @{
        HighPriority = @()
        Medium = @()
        LowPriority = @()
    }
    
    # High Priority Recommendations
    if ($Results.OverallAssessment.TotalLearningInvestment -gt 40) {
        $recommendations.HighPriority += "Plan extensive training program for team - budget $($Results.OverallAssessment.TotalLearningInvestment.ToString('F0')) hours"
    }
    
    if ($Results.PerformanceComparison -and $Results.PerformanceComparison.Changes.OverallPerformanceScore -lt -150) {
        $recommendations.HighPriority += "Address performance concerns before migration - consider selective Mathlib adoption"
    }
    
    if ($Results.OverallAssessment.NetComplexityChange -gt 30) {
        $recommendations.HighPriority += "Review migration approach - current strategy may overcomplicate proofs"
    }
    
    # Medium Priority Recommendations  
    if ($Results.TacticComparison -and $Results.TacticComparison.Changes.TacticsAdded -contains "simp") {
        $recommendations.Medium += "Invest in 'simp' tactic training - high-value skill for Mathlib usage"
    }
    
    if ($Results.LearningCostComparison.Changes.NewTopicAreas -contains "AlgebraicAutomation") {
        $recommendations.Medium += "Focus on algebraic automation tactics - significant productivity gains available"
    }
    
    if ($Results.ComplexityComparison -and $Results.ComplexityComparison.Changes.TotalScoreChange -gt 0 -and $Results.ComplexityComparison.Changes.TotalScoreChange -lt 15) {
        $recommendations.Medium += "Migration adds moderate complexity - ensure team understands new patterns"
    }
    
    # Low Priority Recommendations
    if ($Results.TacticComparison -and $Results.TacticComparison.Changes.TacticsRemoved.Count -gt 0) {
        $recommendations.LowPriority += "Document deprecated tactics for reference"
    }
    
    if ($Results.PerformanceComparison -and $Results.PerformanceComparison.Changes.CompilationTimeChange.Original -lt 2) {
        $recommendations.LowPriority += "Consider precompiled Mathlib cache to maintain fast build times"
    }
    
    $recommendations.LowPriority += "Gradually introduce team to new Mathlib tactics through examples"
    
    return $recommendations
}

function Format-ComprehensiveReport {
    param([hashtable]$Results, [string]$Format)
    
    switch ($Format) {
        "Summary" {
            return Format-SummaryReport $Results
        }
        "JSON" {
            return $Results | ConvertTo-Json -Depth 15
        }
        "HTML" {
            return Format-HTMLReport $Results
        }
        default {
            return Format-FullReport $Results
        }
    }
}

function Format-FullReport {
    param([hashtable]$Results)
    
    $report = @"
Comprehensive Mathlib Migration Analysis
=======================================

Analysis Date: $($Results.AnalysisTimestamp.ToString('yyyy-MM-dd HH:mm:ss'))
User Level: $($Results.UserLevel)

Files Analyzed:
  Original: $($Results.Files.Original | Split-Path -Leaf)
  Mathlib:  $($Results.Files.Mathlib | Split-Path -Leaf)

EXECUTIVE SUMMARY
================

Migration Recommendation: $($Results.ExecutiveSummary.MigrationViability)
Overall Impact: $($Results.OverallAssessment.OverallImpact) (Score: $($Results.OverallAssessment.ImpactScore))
ROI Assessment: $($Results.ExecutiveSummary.BusinessCase.ROIAssessment)

Critical Numbers:
  Complexity Change:    $($Results.ExecutiveSummary.CriticalNumbers.ComplexityChange.ToString('+0.0;-0.0;0.0')) points
  New Tactics:          $($Results.ExecutiveSummary.CriticalNumbers.NewTactics)
  Learning Investment:  $($Results.ExecutiveSummary.CriticalNumbers.LearningHours.ToString('F1')) hours
"@

    if ($Results.PerformanceComparison) {
        $report += "`n  Performance Impact:   $($Results.ExecutiveSummary.CriticalNumbers.PerformanceImpact.ToString('+0.0;-0.0;0.0'))%"
    }

    if ($Results.ExecutiveSummary.KeyFindings.Count -gt 0) {
        $report += "`n`nKey Findings:"
        foreach ($finding in $Results.ExecutiveSummary.KeyFindings) {
            $report += "`n- $finding"
        }
    }

    # Business Case
    $report += "`n`nBUSINESS CASE"
    $report += "`n============="
    
    if ($Results.ExecutiveSummary.BusinessCase.Benefits.Count -gt 0) {
        $report += "`n`nBenefits:"
        foreach ($benefit in $Results.ExecutiveSummary.BusinessCase.Benefits) {
            $report += "`n✓ $benefit"
        }
    }
    
    if ($Results.ExecutiveSummary.BusinessCase.Costs.Count -gt 0) {
        $report += "`n`nCosts/Concerns:"
        foreach ($cost in $Results.ExecutiveSummary.BusinessCase.Costs) {
            $report += "`n✗ $cost"
        }
    }

    # Detailed Analysis Sections
    if ($Results.ComplexityComparison) {
        $report += "`n`nCOMPLEXITY ANALYSIS"
        $report += "`n==================="
        $report += "`n$(Format-DetailedReport $Results.ComplexityComparison)"
    }

    if ($Results.TacticComparison) {
        $report += "`n`nTACTIC USAGE ANALYSIS"
        $report += "`n=====================" 
        $report += "`n$(Format-ComprehensiveComparison $Results.TacticComparison)"
    }

    if ($Results.LearningCostComparison) {
        $report += "`n`nLEARNING COST ANALYSIS"
        $report += "`n======================"
        $report += "`n$(Format-DetailedLearningCost $Results.LearningCostComparison)"
    }

    if ($Results.PerformanceComparison) {
        $report += "`n`nPERFORMANCE ANALYSIS"
        $report += "`n===================="
        $report += "`n$(Format-DetailedBenchmark $Results.PerformanceComparison)"
    }

    # Recommendations
    $report += "`n`nRECOMMENDATIONS"
    $report += "`n==============="

    if ($Results.Recommendations.HighPriority.Count -gt 0) {
        $report += "`n`nHigh Priority Actions:"
        foreach ($rec in $Results.Recommendations.HighPriority) {
            $report += "`n⚠️  $rec"
        }
    }

    if ($Results.Recommendations.Medium.Count -gt 0) {
        $report += "`n`nMedium Priority Actions:"
        foreach ($rec in $Results.Recommendations.Medium) {
            $report += "`n💡 $rec"
        }
    }

    if ($Results.Recommendations.LowPriority.Count -gt 0) {
        $report += "`n`nOptional Improvements:"
        foreach ($rec in $Results.Recommendations.LowPriority) {
            $report += "`n💭 $rec"
        }
    }

    $report += "`n`n" + "=" * 50
    $report += "`nAnalysis completed at $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')"
    $report += "`nGenerated by Mathlib Comprehensive Comparison System"
    
    return $report
}

function Format-SummaryReport {
    param([hashtable]$Results)
    
    $report = @"
Mathlib Migration Analysis Summary
=================================

Recommendation: $($Results.ExecutiveSummary.MigrationViability)
Overall Impact: $($Results.OverallAssessment.OverallImpact) 
ROI: $($Results.ExecutiveSummary.BusinessCase.ROIAssessment)

Key Numbers:
- Complexity: $($Results.ExecutiveSummary.CriticalNumbers.ComplexityChange.ToString('+0.0;-0.0;0.0')) points
- New Tactics: $($Results.ExecutiveSummary.CriticalNumbers.NewTactics)
- Learning: $($Results.ExecutiveSummary.CriticalNumbers.LearningHours.ToString('F1')) hours
"@

    if ($Results.PerformanceComparison) {
        $report += "`n- Performance: $($Results.ExecutiveSummary.CriticalNumbers.PerformanceImpact.ToString('+0.0;-0.0;0.0'))%"
    }

    if ($Results.Recommendations.HighPriority.Count -gt 0) {
        $report += "`n`nPriority Actions:"
        foreach ($rec in $Results.Recommendations.HighPriority) {
            $report += "`n- $rec"
        }
    }
    
    return $report
}

# Main execution
if ($OriginalFile -and $MathlibFile) {
    if (!(Test-Path $OriginalFile)) {
        Write-Host "Original file not found: $OriginalFile" -ForegroundColor Red
        exit 1
    }
    
    if (!(Test-Path $MathlibFile)) {
        Write-Host "Mathlib file not found: $MathlibFile" -ForegroundColor Red
        exit 1
    }
    
    try {
        $results = Run-ComprehensiveComparison $OriginalFile $MathlibFile $UserLevel
        $report = Format-ComprehensiveReport $results $OutputFormat
        
        Write-Host $report
        
        if ($SaveReport) {
            $timestamp = Get-Date -Format 'yyyyMMdd_HHmmss'
            $reportPath = "mathlib-comparison\comprehensive_analysis_$timestamp.txt"
            $report | Out-File -FilePath $reportPath -Encoding UTF8
            Write-Host "`nComprehensive analysis saved to: $reportPath" -ForegroundColor Green
            
            # Also save JSON version for programmatic access
            $jsonPath = "mathlib-comparison\comprehensive_analysis_$timestamp.json"
            $results | ConvertTo-Json -Depth 15 | Out-File -FilePath $jsonPath -Encoding UTF8
            Write-Host "JSON data saved to: $jsonPath" -ForegroundColor Green
        }
        
    } catch {
        Write-Host "Error during comprehensive analysis: $($_.Exception.Message)" -ForegroundColor Red
        exit 1
    }
} else {
    Write-Host @"
Comprehensive Mathlib Comparison System
======================================

Combines all analysis components into unified migration assessment

Usage:
  .\ComprehensiveComparator.ps1 -OriginalFile <path> -MathlibFile <path> [-UserLevel <level>] [-OutputFormat <format>] [options]

Parameters:
  -OriginalFile       Path to original Lean file
  -MathlibFile        Path to migrated Mathlib version
  -UserLevel          Beginner, Intermediate, Advanced (default: Intermediate)
  -OutputFormat       Full, Summary, JSON, HTML (default: Full)
  -BenchmarkRuns      Number of performance benchmark runs (default: 3)
  -IncludePerformance Include compilation performance analysis
  -IncludeTrainingPlan Include detailed learning recommendations
  -SaveReport         Save comprehensive report to files
  -Verbose           Show detailed progress

Examples:
  .\ComprehensiveComparator.ps1 -OriginalFile "original.lean" -MathlibFile "migrated.lean" -SaveReport
  .\ComprehensiveComparator.ps1 -OriginalFile "proof.lean" -MathlibFile "proof_mathlib.lean" -IncludePerformance -IncludeTrainingPlan
  .\ComprehensiveComparator.ps1 -OriginalFile "theorem.lean" -MathlibFile "theorem_mathlib.lean" -UserLevel Beginner -OutputFormat Summary

Analysis Components:
✓ Proof Complexity Analysis - Measures proof sophistication changes
✓ Tactic Usage Comparison - Analyzes available and used tactics  
✓ Learning Cost Evaluation - Assesses educational investment required
✓ Performance Benchmarking - Measures compilation and runtime impact (optional)
✓ Comprehensive Reporting - Unified business case with recommendations
"@ -ForegroundColor Cyan
}

Export-ModuleMember -Function Run-ComprehensiveComparison, Format-ComprehensiveReport