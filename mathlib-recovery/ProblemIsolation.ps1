# Problem Isolation Framework for Mathlib Migration
# Identifies and isolates specific problematic components

param(
    [string]$ProjectPath = ".",
    [string]$IsolationMode = "Smart", # Smart, Aggressive, Conservative
    [switch]$AnalyzeOnly,
    [switch]$Verbose
)

# Isolation strategies configuration
$isolationConfig = @{
    FileAnalysis = @{
        MaxFileSizeKB = 500
        IgnorePatterns = @("*.md", "*.json", "*.log", "*.tmp")
        CriticalFiles = @("lakefile.lean", "Main.lean")
    }
    ImportAnalysis = @{
        SafeImports = @("import Std", "import Mathlib.Tactic.Basic")
        ProblematicPatterns = @("import Mathlib.Data.*", "import Mathlib.Algebra.*")
        MaxImportsPerFile = 10
    }
    ErrorCorrelation = @{
        CorrelationThreshold = 0.7
        MinOccurrences = 2
        ErrorMemoryDays = 7
    }
}

function Analyze-ProjectStructure {
    Write-Host "🔍 Analyzing project structure..." -ForegroundColor Cyan
    
    $leanFiles = Get-ChildItem -Path $ProjectPath -Filter "*.lean" -Recurse | Where-Object {
        $_.Name -notmatch "temp_|debug_|test_"
    }
    
    $projectStructure = @{
        TotalFiles = $leanFiles.Count
        FilesBySize = @{}
        FilesByImportCount = @{}
        DependencyGraph = @{}
        ProblematicFiles = @()
    }
    
    Write-Host "📁 Found $($leanFiles.Count) Lean files" -ForegroundColor Gray
    
    foreach ($file in $leanFiles) {
        $fileInfo = Analyze-LeanFile $file.FullName
        
        # Categorize by size
        $sizeCategory = if ($fileInfo.SizeKB -lt 10) { "Small" } 
                       elseif ($fileInfo.SizeKB -lt 50) { "Medium" } 
                       else { "Large" }
        
        if (!$projectStructure.FilesBySize.ContainsKey($sizeCategory)) {
            $projectStructure.FilesBySize[$sizeCategory] = @()
        }
        $projectStructure.FilesBySize[$sizeCategory] += $fileInfo
        
        # Categorize by import count
        $importCategory = if ($fileInfo.ImportCount -eq 0) { "NoImports" }
                         elseif ($fileInfo.ImportCount -lt 3) { "FewImports" }
                         elseif ($fileInfo.ImportCount -lt 10) { "ManyImports" }
                         else { "ExcessiveImports" }
        
        if (!$projectStructure.FilesByImportCount.ContainsKey($importCategory)) {
            $projectStructure.FilesByImportCount[$importCategory] = @()
        }
        $projectStructure.FilesByImportCount[$importCategory] += $fileInfo
        
        # Mark problematic files
        if ($fileInfo.HasErrors -or $fileInfo.ImportCount -gt $isolationConfig.ImportAnalysis.MaxImportsPerFile) {
            $projectStructure.ProblematicFiles += $fileInfo
        }
    }
    
    if ($Verbose) {
        Write-Host "📊 Project Analysis Results:" -ForegroundColor Yellow
        Write-Host "   Small files: $($projectStructure.FilesBySize['Small'].Count ?? 0)" -ForegroundColor Gray
        Write-Host "   Medium files: $($projectStructure.FilesBySize['Medium'].Count ?? 0)" -ForegroundColor Gray  
        Write-Host "   Large files: $($projectStructure.FilesBySize['Large'].Count ?? 0)" -ForegroundColor Gray
        Write-Host "   Problematic files: $($projectStructure.ProblematicFiles.Count)" -ForegroundColor Red
    }
    
    return $projectStructure
}

function Analyze-LeanFile {
    param([string]$FilePath)
    
    $fileContent = Get-Content $FilePath -ErrorAction SilentlyContinue
    if (!$fileContent) {
        return @{
            Path = $FilePath
            SizeKB = 0
            ImportCount = 0
            Imports = @()
            HasErrors = $true
            ErrorReason = "Could not read file"
        }
    }
    
    $imports = $fileContent | Where-Object { $_ -match '^import\s+' }
    $fileSize = (Get-Item $FilePath).Length / 1KB
    
    # Check for syntax patterns that might cause issues
    $hasComplexSyntax = $fileContent | Where-Object { 
        $_ -match '∀|∃|λ|→|↔|⟨|⟩|‹|›' -or
        $_ -match 'by\s+(ring|omega|simp|rw|norm_num)' -or
        $_ -match 'have\s+.*:.*:='
    }
    
    # Check for problematic import patterns
    $hasProblematicImports = $imports | Where-Object {
        foreach ($pattern in $isolationConfig.ImportAnalysis.ProblematicPatterns) {
            if ($_ -match $pattern.Replace("*", ".*")) { return $true }
        }
        return $false
    }
    
    return @{
        Path = $FilePath
        Name = Split-Path $FilePath -Leaf
        SizeKB = [math]::Round($fileSize, 2)
        ImportCount = $imports.Count
        Imports = $imports
        HasComplexSyntax = $hasComplexSyntax.Count -gt 0
        HasProblematicImports = $hasProblematicImports.Count -gt 0
        HasErrors = $hasProblematicImports.Count -gt 0
        ComplexityScore = ($hasComplexSyntax.Count * 0.3) + ($imports.Count * 0.1) + ($fileSize * 0.01)
    }
}

function Correlate-ErrorsWithFiles {
    param([array]$ErrorLog, [array]$FileList)
    
    Write-Host "🔗 Correlating errors with files..." -ForegroundColor Cyan
    
    $errorCorrelations = @()
    
    foreach ($file in $FileList) {
        $fileName = Split-Path $file.Path -Leaf
        $correlatedErrors = @()
        
        foreach ($error in $ErrorLog) {
            $correlationScore = 0
            
            # Direct file name match
            if ($error.Message -match [regex]::Escape($fileName)) {
                $correlationScore += 0.9
            }
            
            # Import pattern match
            foreach ($import in $file.Imports) {
                $importModule = ($import -replace '^import\s+', '')
                if ($error.Message -match [regex]::Escape($importModule)) {
                    $correlationScore += 0.6
                }
            }
            
            # Error type correlation with file characteristics
            if ($error.Type -eq "ImportError" -and $file.HasProblematicImports) {
                $correlationScore += 0.4
            }
            
            if ($error.Type -eq "SyntaxError" -and $file.HasComplexSyntax) {
                $correlationScore += 0.4
            }
            
            if ($correlationScore -gt $isolationConfig.ErrorCorrelation.CorrelationThreshold) {
                $correlatedErrors += @{
                    Error = $error
                    CorrelationScore = $correlationScore
                    CorrelationReasons = @()
                }
            }
        }
        
        if ($correlatedErrors.Count -gt 0) {
            $errorCorrelations += @{
                File = $file
                Errors = $correlatedErrors
                TotalCorrelationScore = ($correlatedErrors | Measure-Object -Property CorrelationScore -Sum).Sum
                IsolationPriority = "High"
            }
        }
    }
    
    # Sort by correlation strength
    $errorCorrelations = $errorCorrelations | Sort-Object TotalCorrelationScore -Descending
    
    if ($Verbose) {
        Write-Host "📊 Error Correlation Results:" -ForegroundColor Yellow
        $errorCorrelations | Select-Object -First 5 | ForEach-Object {
            Write-Host "   $($_.File.Name): Score $($_.TotalCorrelationScore.ToString('F2'))" -ForegroundColor Gray
        }
    }
    
    return $errorCorrelations
}

function Create-IsolationPlan {
    param([hashtable]$ProjectStructure, [array]$ErrorCorrelations, [string]$Strategy)
    
    Write-Host "📋 Creating isolation plan: $Strategy" -ForegroundColor Cyan
    
    $isolationPlan = @{
        Strategy = $Strategy
        PrimaryTargets = @()   # Files to isolate immediately
        SecondaryTargets = @() # Files to isolate if primary fails
        SafeFiles = @()        # Files to keep active
        IsolationOrder = @()   # Order of isolation operations
    }
    
    switch ($Strategy) {
        "Smart" {
            # Isolate based on error correlation and complexity
            $isolationPlan.PrimaryTargets = $ErrorCorrelations | 
                Where-Object { $_.TotalCorrelationScore -gt 1.0 } |
                ForEach-Object { $_.File }
            
            $isolationPlan.SecondaryTargets = $ProjectStructure.ProblematicFiles | 
                Where-Object { $_.ComplexityScore -gt 2.0 }
            
            $isolationPlan.SafeFiles = $ProjectStructure.FilesByImportCount['NoImports'] + 
                                      $ProjectStructure.FilesByImportCount['FewImports'] |
                                      Where-Object { !$_.HasErrors }
        }
        
        "Aggressive" {
            # Isolate all potentially problematic files
            $isolationPlan.PrimaryTargets = $ProjectStructure.ProblematicFiles
            $isolationPlan.SecondaryTargets = $ProjectStructure.FilesByImportCount['ManyImports'] + 
                                             $ProjectStructure.FilesByImportCount['ExcessiveImports']
            $isolationPlan.SafeFiles = $ProjectStructure.FilesByImportCount['NoImports']
        }
        
        "Conservative" {
            # Only isolate files with direct error correlations
            $isolationPlan.PrimaryTargets = $ErrorCorrelations | 
                Where-Object { $_.TotalCorrelationScore -gt 1.5 } |
                ForEach-Object { $_.File }
            
            $isolationPlan.SafeFiles = $ProjectStructure.FilesBySize['Small'] + 
                                      $ProjectStructure.FilesBySize['Medium'] |
                                      Where-Object { !$_.HasErrors }
        }
    }
    
    # Create isolation order (most problematic first)
    $allTargets = $isolationPlan.PrimaryTargets + $isolationPlan.SecondaryTargets
    $isolationPlan.IsolationOrder = $allTargets | 
        Sort-Object ComplexityScore -Descending |
        ForEach-Object { 
            @{
                File = $_
                Priority = if ($_ -in $isolationPlan.PrimaryTargets) { "High" } else { "Medium" }
                Method = "Move"  # Move, Rename, Comment, etc.
            }
        }
    
    Write-Host "🎯 Isolation Plan Summary:" -ForegroundColor Yellow
    Write-Host "   Primary targets: $($isolationPlan.PrimaryTargets.Count)" -ForegroundColor Red
    Write-Host "   Secondary targets: $($isolationPlan.SecondaryTargets.Count)" -ForegroundColor Yellow
    Write-Host "   Safe files: $($isolationPlan.SafeFiles.Count)" -ForegroundColor Green
    
    return $isolationPlan
}

function Execute-FileIsolation {
    param([hashtable]$IsolationPlan)
    
    if ($AnalyzeOnly) {
        Write-Host "🔍 ANALYSIS ONLY - No files will be modified" -ForegroundColor Cyan
        return $IsolationPlan
    }
    
    Write-Host "🚧 Executing file isolation..." -ForegroundColor Yellow
    
    # Create isolation directory
    $isolationDir = "mathlib-recovery\isolated_files"
    if (!(Test-Path $isolationDir)) {
        New-Item -ItemType Directory -Path $isolationDir -Force | Out-Null
    }
    
    $isolationResults = @{
        Isolated = @()
        Failed = @()
        Preserved = @()
    }
    
    foreach ($isolationItem in $IsolationPlan.IsolationOrder) {
        $file = $isolationItem.File
        $timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
        
        try {
            switch ($isolationItem.Method) {
                "Move" {
                    $isolatedPath = "$isolationDir\$timestamp`_$($file.Name)"
                    Copy-Item $file.Path $isolatedPath -ErrorAction Stop
                    
                    # Create placeholder file
                    $placeholder = @"
// ISOLATED FILE: $($file.Name)
// Original location: $($file.Path) 
// Isolated on: $(Get-Date)
// Reason: Mathlib migration error prevention
// To restore: Copy from $isolatedPath

// Placeholder to prevent import errors
theorem placeholder_$($file.Name.Replace('.lean', '').Replace('-', '_')) : True := trivial
"@
                    $placeholder | Out-File $file.Path -Encoding UTF8
                    
                    Write-Host "✅ Isolated: $($file.Name)" -ForegroundColor Green
                    $isolationResults.Isolated += @{
                        Original = $file.Path
                        Backup = $isolatedPath
                        Method = "Move"
                        Timestamp = $timestamp
                    }
                }
                
                "Rename" {
                    $renamedPath = "$($file.Path).isolated_$timestamp"
                    Rename-Item $file.Path $renamedPath -ErrorAction Stop
                    
                    Write-Host "✅ Renamed: $($file.Name)" -ForegroundColor Green
                    $isolationResults.Isolated += @{
                        Original = $file.Path
                        Backup = $renamedPath
                        Method = "Rename"
                        Timestamp = $timestamp
                    }
                }
                
                "Comment" {
                    # Comment out problematic imports
                    $content = Get-Content $file.Path
                    $modifiedContent = $content | ForEach-Object {
                        if ($_ -match '^import\s+' -and $file.HasProblematicImports) {
                            "-- ISOLATED: $_"
                        } else {
                            $_
                        }
                    }
                    $modifiedContent | Out-File $file.Path -Encoding UTF8
                    
                    Write-Host "✅ Commented imports: $($file.Name)" -ForegroundColor Green
                    $isolationResults.Isolated += @{
                        Original = $file.Path
                        Method = "Comment"
                        Timestamp = $timestamp
                    }
                }
            }
            
        } catch {
            Write-Host "❌ Failed to isolate $($file.Name): $_" -ForegroundColor Red
            $isolationResults.Failed += @{
                File = $file
                Error = $_.Exception.Message
                Timestamp = $timestamp
            }
        }
    }
    
    # Preserve safe files (create backup list)
    foreach ($safeFile in $IsolationPlan.SafeFiles) {
        $isolationResults.Preserved += $safeFile.Path
    }
    
    Write-Host "📊 Isolation Results:" -ForegroundColor Yellow
    Write-Host "   Successfully isolated: $($isolationResults.Isolated.Count)" -ForegroundColor Green
    Write-Host "   Failed to isolate: $($isolationResults.Failed.Count)" -ForegroundColor Red
    Write-Host "   Files preserved: $($isolationResults.Preserved.Count)" -ForegroundColor Cyan
    
    return $isolationResults
}

function Generate-IsolationReport {
    param([hashtable]$IsolationResults, [hashtable]$ProjectStructure)
    
    $reportPath = "mathlib-recovery\isolation_report.md"
    
    $report = @"
# Problem Isolation Report

**Generated**: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')

## Isolation Summary

- **Total Files Analyzed**: $($ProjectStructure.TotalFiles)
- **Files Isolated**: $($IsolationResults.Isolated.Count)
- **Files Preserved**: $($IsolationResults.Preserved.Count)
- **Isolation Failures**: $($IsolationResults.Failed.Count)

## Isolated Files

"@

    foreach ($isolated in $IsolationResults.Isolated) {
        $report += @"

### $($isolated.Original | Split-Path -Leaf)
- **Method**: $($isolated.Method)
- **Backup Location**: `$($isolated.Backup)`
- **Timestamp**: $($isolated.Timestamp)

"@
    }
    
    $report += @"

## Restoration Instructions

To restore isolated files after fixing issues:

```powershell
# Restore specific file
Copy-Item "mathlib-recovery\isolated_files\TIMESTAMP_filename.lean" "original\path\filename.lean"

# Restore all files
Get-ChildItem "mathlib-recovery\isolated_files" | ForEach-Object {
    # Parse original location from backup filename and restore
}
```

## Safe Files (Not Isolated)

"@

    $IsolationResults.Preserved | ForEach-Object {
        $report += "- $($_ | Split-Path -Leaf)`n"
    }
    
    $report += @"

---
*Report generated by Problem Isolation Framework*
"@

    [System.IO.File]::WriteAllText($reportPath, $report)
    Write-Host "📄 Isolation report saved: $reportPath" -ForegroundColor Green
    
    return $reportPath
}

# Main isolation function
function Start-ProblemIsolation {
    param([array]$ErrorLog = @())
    
    Write-Host "🔬 PROBLEM ISOLATION STARTED" -ForegroundColor Cyan
    Write-Host "Mode: $IsolationMode" -ForegroundColor Gray
    Write-Host "="*50 -ForegroundColor Cyan
    
    # Analyze project structure
    $projectStructure = Analyze-ProjectStructure
    
    # Correlate errors with files if error log provided
    $errorCorrelations = if ($ErrorLog.Count -gt 0) {
        Correlate-ErrorsWithFiles $ErrorLog $projectStructure.ProblematicFiles
    } else {
        @()
    }
    
    # Create isolation plan
    $isolationPlan = Create-IsolationPlan $projectStructure $errorCorrelations $IsolationMode
    
    # Execute isolation
    $isolationResults = Execute-FileIsolation $isolationPlan
    
    # Generate report
    $reportPath = Generate-IsolationReport $isolationResults $projectStructure
    
    Write-Host "="*50 -ForegroundColor Cyan
    Write-Host "🏁 PROBLEM ISOLATION COMPLETED" -ForegroundColor Green
    Write-Host "Report: $reportPath" -ForegroundColor Gray
    
    return @{
        Results = $isolationResults
        Plan = $isolationPlan
        Structure = $projectStructure
        ReportPath = $reportPath
    }
}

Export-ModuleMember -Function Start-ProblemIsolation