# Tactic Usage Comparison System
# Analyzes changes in available and used tactics before/after Mathlib migration

param(
    [string]$OriginalFile = "",
    [string]$MathlibFile = "",
    [string]$ComparisonMode = "Comprehensive", # Comprehensive, Usage, Availability
    [switch]$IncludeExamples,
    [switch]$Verbose
)

# Tactic knowledge base
$tacticDatabase = @{
    StandardTactics = @{
        "trivial" = @{
            Category = "Basic"
            Description = "Solves goals that are definitionally true"
            Complexity = 1
            RequiredKnowledge = "None"
            Examples = @("theorem t : True := trivial")
        }
        "rfl" = @{
            Category = "Basic"
            Description = "Proves reflexivity (a = a)"
            Complexity = 1
            RequiredKnowledge = "Equality"
            Examples = @("theorem t : 1 = 1 := rfl")
        }
        "sorry" = @{
            Category = "Placeholder"
            Description = "Admits any goal (for incomplete proofs)"
            Complexity = 1
            RequiredKnowledge = "None"
            Examples = @("theorem t : False := sorry")
        }
        "assumption" = @{
            Category = "Basic"
            Description = "Uses an assumption from the context"
            Complexity = 2
            RequiredKnowledge = "Context management"
            Examples = @("theorem t (h : P) : P := assumption")
        }
        "cases" = @{
            Category = "Structural"
            Description = "Pattern matching and case analysis"
            Complexity = 3
            RequiredKnowledge = "Inductive types, pattern matching"
            Examples = @("cases h with | inl => ... | inr => ...")
        }
        "induction" = @{
            Category = "Structural"
            Description = "Proof by mathematical induction"
            Complexity = 4
            RequiredKnowledge = "Mathematical induction principle"
            Examples = @("induction n with | zero => ... | succ => ...")
        }
        "constructor" = @{
            Category = "Structural"
            Description = "Constructs values of inductive types"
            Complexity = 3
            RequiredKnowledge = "Inductive type constructors"
            Examples = @("constructor")
        }
        "left" = @{
            Category = "Structural"
            Description = "Chooses left side of disjunction (Or)"
            Complexity = 2
            RequiredKnowledge = "Disjunction"
            Examples = @("left; exact h")
        }
        "right" = @{
            Category = "Structural"
            Description = "Chooses right side of disjunction (Or)"
            Complexity = 2
            RequiredKnowledge = "Disjunction"
            Examples = @("right; exact h")
        }
        "split" = @{
            Category = "Structural"
            Description = "Splits conjunction (And) into components"
            Complexity = 3
            RequiredKnowledge = "Conjunction"
            Examples = @("split; [exact h1; exact h2]")
        }
        "apply" = @{
            Category = "Intermediate"
            Description = "Applies a function or theorem"
            Complexity = 4
            RequiredKnowledge = "Function application, theorem usage"
            Examples = @("apply h")
        }
        "exact" = @{
            Category = "Basic"
            Description = "Provides exact proof term"
            Complexity = 2
            RequiredKnowledge = "Proof terms"
            Examples = @("exact h")
        }
    }
    
    MathlibTactics = @{
        "use" = @{
            Category = "Existential"
            Description = "Provides witness for existential quantification"
            Complexity = 3
            RequiredKnowledge = "Existential quantification"
            RequiredImport = "Mathlib.Tactic.Use"
            Examples = @("use 42")
            Replaces = @("exact ⟨42⟩")
        }
        "simp" = @{
            Category = "Simplification"
            Description = "Simplifies expressions using simp lemmas"
            Complexity = 5
            RequiredKnowledge = "Simp lemmas, simplification rules"
            RequiredImport = "Mathlib.Tactic.Simp"
            Examples = @("simp", "simp [h1, h2]", "simp only [add_zero]")
        }
        "rw" = @{
            Category = "Rewriting"
            Description = "Rewrites using equality theorems"
            Complexity = 4
            RequiredKnowledge = "Equality, rewrite rules"
            RequiredImport = "Mathlib.Tactic.Rewrite"
            Examples = @("rw [h]", "rw [← h]", "rw [add_comm]")
        }
        "ring" = @{
            Category = "Algebraic"
            Description = "Solves goals in ring theory"
            Complexity = 6
            RequiredKnowledge = "Ring theory, algebraic manipulation"
            RequiredImport = "Mathlib.Tactic.Ring"
            Examples = @("ring")
            AutomatesCalculations = $true
        }
        "omega" = @{
            Category = "Arithmetic"
            Description = "Linear integer arithmetic decision procedure"
            Complexity = 7
            RequiredKnowledge = "Linear arithmetic, integer constraints"
            RequiredImport = "Mathlib.Tactic.Omega"
            Examples = @("omega")
            AutomatesCalculations = $true
        }
        "norm_num" = @{
            Category = "Arithmetic"
            Description = "Normalizes numerical expressions"
            Complexity = 5
            RequiredKnowledge = "Numerical computation"
            RequiredImport = "Mathlib.Tactic.NormNum"
            Examples = @("norm_num")
            AutomatesCalculations = $true
        }
        "field_simp" = @{
            Category = "Algebraic"
            Description = "Simplifies field expressions"
            Complexity = 7
            RequiredKnowledge = "Field theory, fraction arithmetic"
            RequiredImport = "Mathlib.Tactic.FieldSimp"
            Examples = @("field_simp")
            AutomatesCalculations = $true
        }
        "abel" = @{
            Category = "Algebraic"
            Description = "Abelian group arithmetic"
            Complexity = 6
            RequiredKnowledge = "Abelian groups, group theory"
            RequiredImport = "Mathlib.Tactic.Abel"
            Examples = @("abel")
        }
        "linarith" = @{
            Category = "Arithmetic"
            Description = "Linear arithmetic over ordered fields"
            Complexity = 8
            RequiredKnowledge = "Linear inequalities, ordered fields"
            RequiredImport = "Mathlib.Tactic.Linarith"
            Examples = @("linarith")
            AutomatesCalculations = $true
        }
        "nlinarith" = @{
            Category = "Arithmetic"
            Description = "Nonlinear arithmetic decision procedure"
            Complexity = 9
            RequiredKnowledge = "Nonlinear inequalities, polynomial arithmetic"
            RequiredImport = "Mathlib.Tactic.Linarith"
            Examples = @("nlinarith")
            AutomatesCalculations = $true
        }
        "polyrith" = @{
            Category = "Algebraic"
            Description = "Polynomial arithmetic over rings"
            Complexity = 9
            RequiredKnowledge = "Polynomial rings, algebraic manipulations"
            RequiredImport = "Mathlib.Tactic.Polyrith"
            Examples = @("polyrith")
            AutomatesCalculations = $true
        }
        "conv" = @{
            Category = "Advanced"
            Description = "Conversion mode for targeted rewriting"
            Complexity = 8
            RequiredKnowledge = "Advanced rewriting, expression manipulation"
            RequiredImport = "Mathlib.Tactic.Conv"
            Examples = @("conv => rw [h]", "conv_lhs => simp")
        }
        "gcongr" = @{
            Category = "Monotonicity"
            Description = "Congruence closure with monotonicity"
            Complexity = 7
            RequiredKnowledge = "Monotonicity, inequalities"
            RequiredImport = "Mathlib.Tactic.GCongr"
            Examples = @("gcongr")
        }
        "wlog" = @{
            Category = "Advanced"
            Description = "Without loss of generality"
            Complexity = 9
            RequiredKnowledge = "Symmetry arguments, case reduction"
            RequiredImport = "Mathlib.Tactic.WLOG"
            Examples = @("wlog h : a ≤ b")
        }
        "contrapose" = @{
            Category = "Logic"
            Description = "Proof by contraposition"
            Complexity = 6
            RequiredKnowledge = "Contrapositive logic"
            RequiredImport = "Mathlib.Tactic.Contrapose"
            Examples = @("contrapose h")
        }
        "by_contra" = @{
            Category = "Logic"
            Description = "Proof by contradiction"
            Complexity = 5
            RequiredKnowledge = "Proof by contradiction"
            RequiredImport = "Mathlib.Tactic.ByContra"
            Examples = @("by_contra h")
        }
        "classical" = @{
            Category = "Logic"
            Description = "Classical reasoning (excluded middle)"
            Complexity = 7
            RequiredKnowledge = "Classical logic, excluded middle"
            RequiredImport = "Mathlib.Logic.Basic"
            Examples = @("classical")
        }
    }
    
    TacticCategories = @{
        "Basic" = @{
            Description = "Fundamental tactics requiring minimal knowledge"
            LearningCost = 1
            Color = "Green"
        }
        "Structural" = @{
            Description = "Tactics for working with data structures and pattern matching"
            LearningCost = 2
            Color = "Cyan"
        }
        "Intermediate" = @{
            Description = "Tactics requiring moderate mathematical knowledge"
            LearningCost = 3
            Color = "Yellow"
        }
        "Logic" = @{
            Description = "Advanced logical reasoning tactics"
            LearningCost = 4
            Color = "Blue"
        }
        "Simplification" = @{
            Description = "Automated simplification and rewriting"
            LearningCost = 4
            Color = "Magenta"
        }
        "Rewriting" = @{
            Description = "Equality-based rewriting tactics"
            LearningCost = 3
            Color = "White"
        }
        "Algebraic" = @{
            Description = "Tactics for algebraic structures and calculations"
            LearningCost = 5
            Color = "Yellow"
        }
        "Arithmetic" = @{
            Description = "Automated arithmetic and numerical tactics"
            LearningCost = 5
            Color = "Green"
        }
        "Advanced" = @{
            Description = "Sophisticated tactics for expert users"
            LearningCost = 6
            Color = "Red"
        }
        "Placeholder" = @{
            Description = "Non-proof tactics (sorry, etc.)"
            LearningCost = 0
            Color = "Gray"
        }
    }
}

function Extract-TacticUsage {
    param([string]$FilePath)
    
    if (!(Test-Path $FilePath)) {
        throw "File not found: $FilePath"
    }
    
    $content = Get-Content $FilePath
    $tacticUsage = @{
        FilePath = $FilePath
        FileName = Split-Path $FilePath -Leaf
        UsedTactics = @{}
        TacticContexts = @{}
        TotalTacticUsage = 0
        UsedCategories = @{}
    }
    
    # Extract all tactics from the file
    $allTactics = ($tacticDatabase.StandardTactics.Keys + $tacticDatabase.MathlibTactics.Keys) | Sort-Object -Unique
    
    foreach ($line in $content) {
        foreach ($tactic in $allTactics) {
            $matches = [regex]::Matches($line, "\b$tactic\b")
            if ($matches.Count -gt 0) {
                # Count usage
                if ($tacticUsage.UsedTactics.ContainsKey($tactic)) {
                    $tacticUsage.UsedTactics[$tactic] += $matches.Count
                } else {
                    $tacticUsage.UsedTactics[$tactic] = $matches.Count
                }
                
                # Store context (line where used)
                if (!$tacticUsage.TacticContexts.ContainsKey($tactic)) {
                    $tacticUsage.TacticContexts[$tactic] = @()
                }
                $tacticUsage.TacticContexts[$tactic] += $line.Trim()
                
                $tacticUsage.TotalTacticUsage += $matches.Count
            }
        }
    }
    
    # Categorize used tactics
    foreach ($tactic in $tacticUsage.UsedTactics.Keys) {
        $category = $null
        
        # Check standard tactics
        if ($tacticDatabase.StandardTactics.ContainsKey($tactic)) {
            $category = $tacticDatabase.StandardTactics[$tactic].Category
        }
        # Check Mathlib tactics
        elseif ($tacticDatabase.MathlibTactics.ContainsKey($tactic)) {
            $category = $tacticDatabase.MathlibTactics[$tactic].Category
        }
        
        if ($category) {
            if ($tacticUsage.UsedCategories.ContainsKey($category)) {
                $tacticUsage.UsedCategories[$category] += $tacticUsage.UsedTactics[$tactic]
            } else {
                $tacticUsage.UsedCategories[$category] = $tacticUsage.UsedTactics[$tactic]
            }
        }
    }
    
    if ($Verbose) {
        Write-Host "Extracted tactics from $($tacticUsage.FileName):" -ForegroundColor Cyan
        Write-Host "  Total tactic usage: $($tacticUsage.TotalTacticUsage)" -ForegroundColor Gray
        Write-Host "  Unique tactics: $($tacticUsage.UsedTactics.Count)" -ForegroundColor Gray
        Write-Host "  Categories used: $($tacticUsage.UsedCategories.Count)" -ForegroundColor Gray
    }
    
    return $tacticUsage
}

function Analyze-TacticAvailability {
    param([string]$FilePath)
    
    $content = Get-Content $FilePath
    $imports = $content | Where-Object { $_ -match '^import\s+' }
    
    $availability = @{
        FilePath = $FilePath
        StandardTacticsAvailable = $tacticDatabase.StandardTactics.Keys
        MathlibTacticsAvailable = @()
        UnavailableTactics = @()
        ImportedModules = $imports
    }
    
    # Check which Mathlib tactics are available based on imports
    foreach ($tacticName in $tacticDatabase.MathlibTactics.Keys) {
        $tacticInfo = $tacticDatabase.MathlibTactics[$tacticName]
        $requiredImport = $tacticInfo.RequiredImport
        
        # Check if required import is present
        $isAvailable = $false
        foreach ($import in $imports) {
            if ($import -match $requiredImport -or $import -match "Mathlib\.Tactic\.Basic") {
                $isAvailable = $true
                break
            }
        }
        
        if ($isAvailable) {
            $availability.MathlibTacticsAvailable += $tacticName
        } else {
            $availability.UnavailableTactics += $tacticName
        }
    }
    
    return $availability
}

function Compare-TacticUsage {
    param([hashtable]$OriginalUsage, [hashtable]$MathlibUsage)
    
    $comparison = @{
        Original = $OriginalUsage
        Mathlib = $MathlibUsage
        Changes = @{
            TacticsAdded = @()
            TacticsRemoved = @()
            TacticsChanged = @{}
            CategoryChanges = @{}
            ComplexityChange = 0
        }
        Insights = @()
        Recommendations = @()
    }
    
    # Find added and removed tactics
    $originalTactics = $OriginalUsage.UsedTactics.Keys
    $mathlibTactics = $MathlibUsage.UsedTactics.Keys
    
    $comparison.Changes.TacticsAdded = $mathlibTactics | Where-Object { $_ -notin $originalTactics }
    $comparison.Changes.TacticsRemoved = $originalTactics | Where-Object { $_ -notin $mathlibTactics }
    
    # Find changed usage counts
    foreach ($tactic in ($originalTactics + $mathlibTactics | Sort-Object -Unique)) {
        $originalCount = if ($OriginalUsage.UsedTactics.ContainsKey($tactic)) { $OriginalUsage.UsedTactics[$tactic] } else { 0 }
        $mathlibCount = if ($MathlibUsage.UsedTactics.ContainsKey($tactic)) { $MathlibUsage.UsedTactics[$tactic] } else { 0 }
        $change = $mathlibCount - $originalCount
        
        if ($change -ne 0) {
            $comparison.Changes.TacticsChanged[$tactic] = @{
                Original = $originalCount
                Mathlib = $mathlibCount
                Change = $change
                PercentChange = if ($originalCount -gt 0) { ($change / $originalCount) * 100 } else { 100 }
            }
        }
    }
    
    # Compare category usage
    $allCategories = ($OriginalUsage.UsedCategories.Keys + $MathlibUsage.UsedCategories.Keys) | Sort-Object -Unique
    foreach ($category in $allCategories) {
        $originalCount = if ($OriginalUsage.UsedCategories.ContainsKey($category)) { $OriginalUsage.UsedCategories[$category] } else { 0 }
        $mathlibCount = if ($MathlibUsage.UsedCategories.ContainsKey($category)) { $MathlibUsage.UsedCategories[$category] } else { 0 }
        $change = $mathlibCount - $originalCount
        
        $comparison.Changes.CategoryChanges[$category] = @{
            Original = $originalCount
            Mathlib = $mathlibCount
            Change = $change
        }
    }
    
    # Calculate complexity change
    $originalComplexity = 0
    $mathlibComplexity = 0
    
    foreach ($tactic in $originalTactics) {
        $complexity = 3  # Default
        if ($tacticDatabase.StandardTactics.ContainsKey($tactic)) {
            $complexity = $tacticDatabase.StandardTactics[$tactic].Complexity
        } elseif ($tacticDatabase.MathlibTactics.ContainsKey($tactic)) {
            $complexity = $tacticDatabase.MathlibTactics[$tactic].Complexity
        }
        $originalComplexity += $complexity * $OriginalUsage.UsedTactics[$tactic]
    }
    
    foreach ($tactic in $mathlibTactics) {
        $complexity = 3  # Default
        if ($tacticDatabase.StandardTactics.ContainsKey($tactic)) {
            $complexity = $tacticDatabase.StandardTactics[$tactic].Complexity
        } elseif ($tacticDatabase.MathlibTactics.ContainsKey($tactic)) {
            $complexity = $tacticDatabase.MathlibTactics[$tactic].Complexity
        }
        $mathlibComplexity += $complexity * $MathlibUsage.UsedTactics[$tactic]
    }
    
    $comparison.Changes.ComplexityChange = $mathlibComplexity - $originalComplexity
    
    # Generate insights
    if ($comparison.Changes.TacticsAdded.Count -gt 0) {
        $newMathlibTactics = $comparison.Changes.TacticsAdded | Where-Object { $_ -in $tacticDatabase.MathlibTactics.Keys }
        if ($newMathlibTactics.Count -gt 0) {
            $comparison.Insights += "Added $($newMathlibTactics.Count) new Mathlib-specific tactics: $($newMathlibTactics -join ', ')"
        }
    }
    
    if ($comparison.Changes.TacticsRemoved.Count -gt 0) {
        $comparison.Insights += "Removed $($comparison.Changes.TacticsRemoved.Count) tactics: $($comparison.Changes.TacticsRemoved -join ', ')"
    }
    
    if ($comparison.Changes.ComplexityChange -gt 10) {
        $comparison.Insights += "Tactics became significantly more complex (+$($comparison.Changes.ComplexityChange) complexity points)"
    } elseif ($comparison.Changes.ComplexityChange -lt -10) {
        $comparison.Insights += "Tactics became simpler (-$([math]::Abs($comparison.Changes.ComplexityChange)) complexity points)"
    }
    
    # Check for automation improvements
    $automatedTactics = $comparison.Changes.TacticsAdded | Where-Object {
        $tacticDatabase.MathlibTactics.ContainsKey($_) -and $tacticDatabase.MathlibTactics[$_].AutomatesCalculations
    }
    
    if ($automatedTactics.Count -gt 0) {
        $comparison.Insights += "Gained access to $($automatedTactics.Count) automated calculation tactics: $($automatedTactics -join ', ')"
    }
    
    # Generate recommendations
    $sorryUsage = if ($comparison.Changes.TacticsChanged.ContainsKey("sorry")) { $comparison.Changes.TacticsChanged["sorry"].Mathlib } else { 0 }
    if ($sorryUsage -gt 0) {
        $comparison.Recommendations += "Consider replacing $sorryUsage sorry statements with actual proofs using new Mathlib tactics"
    }
    
    if ($comparison.Changes.TacticsAdded -contains "ring" -or $comparison.Changes.TacticsAdded -contains "omega") {
        $comparison.Recommendations += "Leverage automated tactics like 'ring' and 'omega' to simplify arithmetic proofs"
    }
    
    return $comparison
}

function Format-TacticComparison {
    param([hashtable]$Comparison, [string]$Mode)
    
    switch ($Mode) {
        "Usage" {
            return Format-UsageComparison $Comparison
        }
        "Availability" {
            return Format-AvailabilityComparison $Comparison
        }
        default {
            return Format-ComprehensiveComparison $Comparison
        }
    }
}

function Format-ComprehensiveComparison {
    param([hashtable]$Comparison)
    
    $report = @"
Comprehensive Tactic Comparison Report
=====================================

Files Compared:
  Original: $($Comparison.Original.FileName)
  Mathlib:  $($Comparison.Mathlib.FileName)

Usage Statistics:
  Original total usage: $($Comparison.Original.TotalTacticUsage)
  Mathlib total usage:  $($Comparison.Mathlib.TotalTacticUsage)
  Change: $($Comparison.Mathlib.TotalTacticUsage - $Comparison.Original.TotalTacticUsage) tactics

  Original unique tactics: $($Comparison.Original.UsedTactics.Count)
  Mathlib unique tactics:  $($Comparison.Mathlib.UsedTactics.Count)
  Change: $($Comparison.Mathlib.UsedTactics.Count - $Comparison.Original.UsedTactics.Count) tactics

Tactic Changes:
"@

    if ($Comparison.Changes.TacticsAdded.Count -gt 0) {
        $report += "`nAdded Tactics ($($Comparison.Changes.TacticsAdded.Count)):"
        foreach ($tactic in $Comparison.Changes.TacticsAdded) {
            $category = "Unknown"
            $description = "No description available"
            
            if ($tacticDatabase.StandardTactics.ContainsKey($tactic)) {
                $category = $tacticDatabase.StandardTactics[$tactic].Category
                $description = $tacticDatabase.StandardTactics[$tactic].Description
            } elseif ($tacticDatabase.MathlibTactics.ContainsKey($tactic)) {
                $category = $tacticDatabase.MathlibTactics[$tactic].Category
                $description = $tacticDatabase.MathlibTactics[$tactic].Description
            }
            
            $usage = $Comparison.Mathlib.UsedTactics[$tactic]
            $report += "`n  + $tactic ($category) - used $usage time(s)"
            $report += "`n    $description"
        }
    }
    
    if ($Comparison.Changes.TacticsRemoved.Count -gt 0) {
        $report += "`n`nRemoved Tactics ($($Comparison.Changes.TacticsRemoved.Count)):"
        foreach ($tactic in $Comparison.Changes.TacticsRemoved) {
            $usage = $Comparison.Original.UsedTactics[$tactic]
            $report += "`n  - $tactic - was used $usage time(s)"
        }
    }
    
    if ($Comparison.Changes.TacticsChanged.Count -gt 0) {
        $report += "`n`nChanged Usage:"
        foreach ($tactic in ($Comparison.Changes.TacticsChanged.Keys | Sort-Object)) {
            $change = $Comparison.Changes.TacticsChanged[$tactic]
            $report += "`n  $tactic`: $($change.Original) → $($change.Mathlib) ($($change.Change.ToString('+0;-0;0')))"
        }
    }
    
    # Category comparison
    $report += "`n`nTactic Category Usage:"
    $allCategories = ($Comparison.Changes.CategoryChanges.Keys | Sort-Object)
    foreach ($category in $allCategories) {
        $change = $Comparison.Changes.CategoryChanges[$category]
        $report += "`n  $category`: $($change.Original) → $($change.Mathlib) ($($change.Change.ToString('+0;-0;0')))"
    }
    
    if ($Comparison.Insights.Count -gt 0) {
        $report += "`n`nKey Insights:"
        foreach ($insight in $Comparison.Insights) {
            $report += "`n- $insight"
        }
    }
    
    if ($Comparison.Recommendations.Count -gt 0) {
        $report += "`n`nRecommendations:"
        foreach ($rec in $Comparison.Recommendations) {
            $report += "`n- $rec"
        }
    }
    
    return $report
}

function Format-UsageComparison {
    param([hashtable]$Comparison)
    
    $report = @"
Tactic Usage Comparison
=======================

Summary:
  Added $($Comparison.Changes.TacticsAdded.Count) new tactics
  Removed $($Comparison.Changes.TacticsRemoved.Count) tactics
  Changed usage for $($Comparison.Changes.TacticsChanged.Count) tactics
  Complexity change: $($Comparison.Changes.ComplexityChange.ToString('+0;-0;0')) points

Key Changes:
"@

    foreach ($insight in $Comparison.Insights) {
        $report += "`n- $insight"
    }
    
    return $report
}

# Main execution
if ($OriginalFile -and $MathlibFile) {
    Write-Host "Analyzing tactic usage comparison..." -ForegroundColor Cyan
    
    try {
        $originalUsage = Extract-TacticUsage $OriginalFile
        $mathlibUsage = Extract-TacticUsage $MathlibFile
        
        $comparison = Compare-TacticUsage $originalUsage $mathlibUsage
        $report = Format-TacticComparison $comparison $ComparisonMode
        
        Write-Host $report
        
        if ($IncludeExamples) {
            Write-Host "`nTactic Examples:" -ForegroundColor Yellow
            $newTactics = $comparison.Changes.TacticsAdded | Where-Object { $tacticDatabase.MathlibTactics.ContainsKey($_) }
            foreach ($tactic in $newTactics | Select-Object -First 3) {
                $examples = $tacticDatabase.MathlibTactics[$tactic].Examples
                Write-Host "`n$tactic examples:" -ForegroundColor Cyan
                foreach ($example in $examples) {
                    Write-Host "  $example" -ForegroundColor Gray
                }
            }
        }
        
    } catch {
        Write-Host "Error during tactic analysis: $($_.Exception.Message)" -ForegroundColor Red
    }
} else {
    Write-Host @"
Tactic Usage Comparison System

Usage:
  .\TacticComparator.ps1 -OriginalFile <path> -MathlibFile <path> [-ComparisonMode <mode>] [-IncludeExamples] [-Verbose]

Comparison Modes:
  Comprehensive - Full tactic analysis (default)
  Usage         - Focus on usage patterns
  Availability  - Focus on available tactics

Examples:
  .\TacticComparator.ps1 -OriginalFile "proof.lean" -MathlibFile "proof_mathlib.lean"
  .\TacticComparator.ps1 -OriginalFile "theorem.lean" -MathlibFile "theorem_mathlib.lean" -IncludeExamples
"@ -ForegroundColor Cyan
}

Export-ModuleMember -Function Extract-TacticUsage, Analyze-TacticAvailability, Compare-TacticUsage