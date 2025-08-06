# Performance Benchmarking System
# Compares compilation time, memory usage, and execution speed before/after Mathlib migration

param(
    [string]$OriginalFile = "",
    [string]$MathlibFile = "",
    [int]$BenchmarkRuns = 3,
    [string]$OutputFormat = "Detailed", # Detailed, Summary, JSON
    [switch]$IncludeMemoryProfiling,
    [switch]$Verbose
)

# Performance benchmarking configuration
$benchmarkConfig = @{
    BenchmarkTypes = @{
        "CompilationTime" = @{
            Description = "Time to compile the Lean file"
            Weight = 0.4
            Unit = "seconds"
            Command = "lake build"
        }
        "ImportResolution" = @{
            Description = "Time to resolve imports"
            Weight = 0.25
            Unit = "seconds" 
            Command = "lean --deps-only"
        }
        "TypeChecking" = @{
            Description = "Type checking duration"
            Weight = 0.2
            Unit = "seconds"
            Command = "lean --check"
        }
        "MemoryUsage" = @{
            Description = "Peak memory consumption"
            Weight = 0.15
            Unit = "MB"
            Command = "lean --memory-profile"
        }
    }
    
    PerformanceCategories = @{
        "Excellent" = @{ Min = 0; Max = 1.2; Description = "Very fast compilation" }
        "Good" = @{ Min = 1.2; Max = 3.0; Description = "Acceptable performance" }
        "Moderate" = @{ Min = 3.0; Max = 8.0; Description = "Noticeable delay" }
        "Slow" = @{ Min = 8.0; Max = 20.0; Description = "Significant delay" }
        "Poor" = @{ Min = 20.0; Max = 999.0; Description = "Very slow compilation" }
    }
    
    AcceptableThresholds = @{
        CompilationTimeIncrease = 200  # 200% increase is concerning
        MemoryIncrease = 300          # 300% memory increase is concerning
        ImportResolutionIncrease = 150 # 150% import time increase is concerning
    }
}

function Measure-LeanCompilation {
    param([string]$FilePath, [int]$Runs = 3)
    
    if (!(Test-Path $FilePath)) {
        throw "File not found: $FilePath"
    }
    
    $measurements = @{
        FilePath = $FilePath
        FileName = Split-Path $FilePath -Leaf
        CompilationTimes = @()
        ImportTimes = @()
        TypeCheckTimes = @()
        MemoryUsage = @()
        AverageMetrics = @{}
        ProcessInfo = @{}
    }
    
    Write-Host "Benchmarking $($measurements.FileName) ($Runs runs)..." -ForegroundColor Cyan
    
    # Get file directory for lake commands
    $fileDir = Split-Path $FilePath -Parent
    $originalPath = Get-Location
    
    try {
        if ($fileDir) {
            Set-Location $fileDir
        }
        
        # Run multiple benchmark iterations
        for ($i = 1; $i -le $Runs; $i++) {
            if ($Verbose) {
                Write-Host "  Run $i/$Runs" -ForegroundColor Gray
            }
            
            # 1. Measure full compilation time
            $compileTimer = [System.Diagnostics.Stopwatch]::StartNew()
            try {
                $compileResult = & lake build 2>&1
                $compileTimer.Stop()
                $compileTime = $compileTimer.ElapsedMilliseconds / 1000.0
                $measurements.CompilationTimes += $compileTime
                
                if ($Verbose) {
                    Write-Host "    Compilation: $($compileTime.ToString('F2'))s" -ForegroundColor Gray
                }
            } catch {
                $compileTimer.Stop()
                $measurements.CompilationTimes += 999.0  # Error indicator
                Write-Warning "Compilation failed on run $i"
            }
            
            # 2. Measure import resolution
            $importTimer = [System.Diagnostics.Stopwatch]::StartNew()
            try {
                $importResult = & lean --deps-only $FilePath 2>&1
                $importTimer.Stop()
                $importTime = $importTimer.ElapsedMilliseconds / 1000.0
                $measurements.ImportTimes += $importTime
                
                if ($Verbose) {
                    Write-Host "    Import resolution: $($importTime.ToString('F2'))s" -ForegroundColor Gray
                }
            } catch {
                $importTimer.Stop()
                $measurements.ImportTimes += 10.0  # Error indicator
            }
            
            # 3. Measure type checking
            $typeTimer = [System.Diagnostics.Stopwatch]::StartNew()
            try {
                $typeResult = & lean --check $FilePath 2>&1
                $typeTimer.Stop()
                $typeTime = $typeTimer.ElapsedMilliseconds / 1000.0
                $measurements.TypeCheckTimes += $typeTime
                
                if ($Verbose) {
                    Write-Host "    Type checking: $($typeTime.ToString('F2'))s" -ForegroundColor Gray
                }
            } catch {
                $typeTimer.Stop()
                $measurements.TypeCheckTimes += 5.0  # Error indicator
            }
            
            # 4. Measure memory usage (if available)
            if ($IncludeMemoryProfiling) {
                try {
                    # Simple memory measurement using lean with memory profiling
                    $memResult = & lean --memory $FilePath 2>&1 | Select-String "peak.*MB"
                    if ($memResult) {
                        $memValue = [regex]::Match($memResult.ToString(), "(\d+\.?\d*)\s*MB").Groups[1].Value
                        $measurements.MemoryUsage += [double]$memValue
                    } else {
                        $measurements.MemoryUsage += 50.0  # Default estimate
                    }
                } catch {
                    $measurements.MemoryUsage += 100.0  # Error estimate
                }
            }
            
            # Small delay between runs to avoid interference
            if ($i -lt $Runs) {
                Start-Sleep -Milliseconds 500
            }
        }
        
        # Calculate averages
        $measurements.AverageMetrics = @{
            CompilationTime = ($measurements.CompilationTimes | Measure-Object -Average).Average
            ImportTime = ($measurements.ImportTimes | Measure-Object -Average).Average  
            TypeCheckTime = ($measurements.TypeCheckTimes | Measure-Object -Average).Average
            MemoryUsage = if ($measurements.MemoryUsage.Count -gt 0) { 
                ($measurements.MemoryUsage | Measure-Object -Average).Average 
            } else { 0 }
        }
        
        # Add process information
        $measurements.ProcessInfo = @{
            TotalRuns = $Runs
            SuccessfulRuns = ($measurements.CompilationTimes | Where-Object { $_ -lt 900 }).Count
            FailedRuns = ($measurements.CompilationTimes | Where-Object { $_ -ge 900 }).Count
            BenchmarkTime = Get-Date
        }
        
    } finally {
        Set-Location $originalPath
    }
    
    return $measurements
}

function Compare-Performance {
    param([hashtable]$OriginalMeasurement, [hashtable]$MathlibMeasurement)
    
    $comparison = @{
        Original = $OriginalMeasurement
        Mathlib = $MathlibMeasurement
        Changes = @{
            CompilationTimeChange = @{}
            ImportTimeChange = @{}
            TypeCheckTimeChange = @{}
            MemoryUsageChange = @{}
            OverallPerformanceScore = 0
        }
        PerformanceInsights = @()
        Recommendations = @()
        PerformanceCategory = "Unknown"
    }
    
    # Calculate performance changes
    $origCompile = $OriginalMeasurement.AverageMetrics.CompilationTime
    $mathlibCompile = $MathlibMeasurement.AverageMetrics.CompilationTime
    $compileChange = $mathlibCompile - $origCompile
    $compilePercentChange = if ($origCompile -gt 0) { ($compileChange / $origCompile) * 100 } else { 0 }
    
    $comparison.Changes.CompilationTimeChange = @{
        Original = [math]::Round($origCompile, 2)
        Mathlib = [math]::Round($mathlibCompile, 2) 
        Change = [math]::Round($compileChange, 2)
        PercentChange = [math]::Round($compilePercentChange, 1)
        Severity = if ($compilePercentChange -gt $benchmarkConfig.AcceptableThresholds.CompilationTimeIncrease) { "High" } 
                   elseif ($compilePercentChange -gt 50) { "Medium" } 
                   else { "Low" }
    }
    
    # Import time change
    $origImport = $OriginalMeasurement.AverageMetrics.ImportTime
    $mathlibImport = $MathlibMeasurement.AverageMetrics.ImportTime
    $importChange = $mathlibImport - $origImport
    $importPercentChange = if ($origImport -gt 0) { ($importChange / $origImport) * 100 } else { 0 }
    
    $comparison.Changes.ImportTimeChange = @{
        Original = [math]::Round($origImport, 2)
        Mathlib = [math]::Round($mathlibImport, 2)
        Change = [math]::Round($importChange, 2)
        PercentChange = [math]::Round($importPercentChange, 1)
        Severity = if ($importPercentChange -gt $benchmarkConfig.AcceptableThresholds.ImportResolutionIncrease) { "High" } 
                   elseif ($importPercentChange -gt 30) { "Medium" } 
                   else { "Low" }
    }
    
    # Type check time change
    $origType = $OriginalMeasurement.AverageMetrics.TypeCheckTime
    $mathlibType = $MathlibMeasurement.AverageMetrics.TypeCheckTime
    $typeChange = $mathlibType - $origType
    $typePercentChange = if ($origType -gt 0) { ($typeChange / $origType) * 100 } else { 0 }
    
    $comparison.Changes.TypeCheckTimeChange = @{
        Original = [math]::Round($origType, 2)
        Mathlib = [math]::Round($mathlibType, 2)
        Change = [math]::Round($typeChange, 2)
        PercentChange = [math]::Round($typePercentChange, 1)
        Severity = if ($typePercentChange -gt 100) { "High" } 
                   elseif ($typePercentChange -gt 40) { "Medium" } 
                   else { "Low" }
    }
    
    # Memory usage change (if available)
    if ($IncludeMemoryProfiling -and $OriginalMeasurement.AverageMetrics.MemoryUsage -gt 0) {
        $origMem = $OriginalMeasurement.AverageMetrics.MemoryUsage
        $mathlibMem = $MathlibMeasurement.AverageMetrics.MemoryUsage
        $memChange = $mathlibMem - $origMem
        $memPercentChange = if ($origMem -gt 0) { ($memChange / $origMem) * 100 } else { 0 }
        
        $comparison.Changes.MemoryUsageChange = @{
            Original = [math]::Round($origMem, 1)
            Mathlib = [math]::Round($mathlibMem, 1)
            Change = [math]::Round($memChange, 1)
            PercentChange = [math]::Round($memPercentChange, 1)
            Severity = if ($memPercentChange -gt $benchmarkConfig.AcceptableThresholds.MemoryIncrease) { "High" } 
                       elseif ($memPercentChange -gt 100) { "Medium" } 
                       else { "Low" }
        }
    }
    
    # Calculate overall performance score
    $performanceScore = 0
    $performanceScore -= $compilePercentChange * 0.4
    $performanceScore -= $importPercentChange * 0.25
    $performanceScore -= $typePercentChange * 0.2
    if ($comparison.Changes.MemoryUsageChange.PercentChange) {
        $performanceScore -= $comparison.Changes.MemoryUsageChange.PercentChange * 0.15
    }
    
    $comparison.Changes.OverallPerformanceScore = [math]::Round($performanceScore, 1)
    
    # Determine performance category
    $totalTime = $mathlibCompile + $mathlibImport + $mathlibType
    foreach ($catName in $benchmarkConfig.PerformanceCategories.Keys) {
        $catInfo = $benchmarkConfig.PerformanceCategories[$catName]
        if ($totalTime -ge $catInfo.Min -and $totalTime -lt $catInfo.Max) {
            $comparison.PerformanceCategory = $catName
            break
        }
    }
    
    # Generate insights
    if ($compilePercentChange -gt 100) {
        $comparison.PerformanceInsights += "Compilation time more than doubled (+$($compilePercentChange.ToString('F1'))%)"
    } elseif ($compilePercentChange -gt 50) {
        $comparison.PerformanceInsights += "Noticeable compilation slowdown (+$($compilePercentChange.ToString('F1'))%)"
    } elseif ($compilePercentChange -lt -20) {
        $comparison.PerformanceInsights += "Compilation became faster ($($compilePercentChange.ToString('F1'))%)"
    }
    
    if ($importPercentChange -gt 200) {
        $comparison.PerformanceInsights += "Import resolution significantly slower (+$($importPercentChange.ToString('F1'))%)"
    }
    
    if ($comparison.Changes.MemoryUsageChange.PercentChange -gt 200) {
        $comparison.PerformanceInsights += "Memory usage substantially increased (+$($comparison.Changes.MemoryUsageChange.PercentChange.ToString('F1'))%)"
    }
    
    # Generate recommendations
    if ($comparison.Changes.CompilationTimeChange.Severity -eq "High") {
        $comparison.Recommendations += "Consider optimizing imports or using more selective Mathlib modules"
    }
    
    if ($comparison.Changes.ImportTimeChange.Severity -eq "High") {
        $comparison.Recommendations += "Review import statements - remove unused imports and use specific modules"
    }
    
    if ($mathlibCompile -gt 10) {
        $comparison.Recommendations += "Consider using 'lake exe cache get' to speed up builds"
    }
    
    if ($comparison.Changes.OverallPerformanceScore -lt -100) {
        $comparison.Recommendations += "Performance impact is significant - evaluate if Mathlib benefits justify the cost"
    }
    
    return $comparison
}

function Format-PerformanceBenchmark {
    param([hashtable]$Comparison, [string]$Format)
    
    switch ($Format) {
        "Summary" {
            return Format-SummaryBenchmark $Comparison
        }
        "JSON" {
            return $Comparison | ConvertTo-Json -Depth 10
        }
        default {
            return Format-DetailedBenchmark $Comparison
        }
    }
}

function Format-DetailedBenchmark {
    param([hashtable]$Comparison)
    
    $report = @"
Performance Benchmark Comparison
===============================

Files Compared:
  Original: $($Comparison.Original.FileName)
  Mathlib:  $($Comparison.Mathlib.FileName)

Performance Summary:
  Overall performance score: $($Comparison.Changes.OverallPerformanceScore.ToString('+0.0;-0.0;0.0'))%
  Performance category: $($Comparison.PerformanceCategory)

Detailed Metrics:
"@

    $report += @"

Compilation Time:
  Original: $($Comparison.Changes.CompilationTimeChange.Original)s
  Mathlib:  $($Comparison.Changes.CompilationTimeChange.Mathlib)s  
  Change:   $($Comparison.Changes.CompilationTimeChange.Change.ToString('+0.00;-0.00;0.00'))s ($($Comparison.Changes.CompilationTimeChange.PercentChange.ToString('+0.0;-0.0;0.0'))%)
  Severity: $($Comparison.Changes.CompilationTimeChange.Severity)

Import Resolution:
  Original: $($Comparison.Changes.ImportTimeChange.Original)s
  Mathlib:  $($Comparison.Changes.ImportTimeChange.Mathlib)s
  Change:   $($Comparison.Changes.ImportTimeChange.Change.ToString('+0.00;-0.00;0.00'))s ($($Comparison.Changes.ImportTimeChange.PercentChange.ToString('+0.0;-0.0;0.0'))%)
  Severity: $($Comparison.Changes.ImportTimeChange.Severity)

Type Checking:
  Original: $($Comparison.Changes.TypeCheckTimeChange.Original)s
  Mathlib:  $($Comparison.Changes.TypeCheckTimeChange.Mathlib)s
  Change:   $($Comparison.Changes.TypeCheckTimeChange.Change.ToString('+0.00;-0.00;0.00'))s ($($Comparison.Changes.TypeCheckTimeChange.PercentChange.ToString('+0.0;-0.0;0.0'))%)
  Severity: $($Comparison.Changes.TypeCheckTimeChange.Severity)
"@

    if ($Comparison.Changes.MemoryUsageChange.Original) {
        $report += @"

Memory Usage:
  Original: $($Comparison.Changes.MemoryUsageChange.Original) MB
  Mathlib:  $($Comparison.Changes.MemoryUsageChange.Mathlib) MB
  Change:   $($Comparison.Changes.MemoryUsageChange.Change.ToString('+0.0;-0.0;0.0')) MB ($($Comparison.Changes.MemoryUsageChange.PercentChange.ToString('+0.0;-0.0;0.0'))%)
  Severity: $($Comparison.Changes.MemoryUsageChange.Severity)
"@
    }

    # Benchmark statistics
    $report += @"

Benchmark Statistics:
                    Original                Mathlib
Total Runs:         $($Comparison.Original.ProcessInfo.TotalRuns.ToString().PadLeft(8))              $($Comparison.Mathlib.ProcessInfo.TotalRuns.ToString().PadLeft(8))
Successful Runs:    $($Comparison.Original.ProcessInfo.SuccessfulRuns.ToString().PadLeft(8))              $($Comparison.Mathlib.ProcessInfo.SuccessfulRuns.ToString().PadLeft(8))
Failed Runs:        $($Comparison.Original.ProcessInfo.FailedRuns.ToString().PadLeft(8))              $($Comparison.Mathlib.ProcessInfo.FailedRuns.ToString().PadLeft(8))
"@

    if ($Comparison.PerformanceInsights.Count -gt 0) {
        $report += "`n`nPerformance Insights:"
        foreach ($insight in $Comparison.PerformanceInsights) {
            $report += "`n- $insight"
        }
    }
    
    if ($Comparison.Recommendations.Count -gt 0) {
        $report += "`n`nOptimization Recommendations:"
        foreach ($rec in $Comparison.Recommendations) {
            $report += "`n- $rec"
        }
    }
    
    return $report
}

function Format-SummaryBenchmark {
    param([hashtable]$Comparison)
    
    $report = @"
Performance Benchmark Summary
============================

Performance Impact: $($Comparison.Changes.OverallPerformanceScore.ToString('+0.0;-0.0;0.0'))% ($($Comparison.PerformanceCategory))

Key Changes:
- Compilation: $($Comparison.Changes.CompilationTimeChange.PercentChange.ToString('+0.0;-0.0;0.0'))% ($($Comparison.Changes.CompilationTimeChange.Severity) impact)
- Import Resolution: $($Comparison.Changes.ImportTimeChange.PercentChange.ToString('+0.0;-0.0;0.0'))% ($($Comparison.Changes.ImportTimeChange.Severity) impact)
- Type Checking: $($Comparison.Changes.TypeCheckTimeChange.PercentChange.ToString('+0.0;-0.0;0.0'))% ($($Comparison.Changes.TypeCheckTimeChange.Severity) impact)
"@

    if ($Comparison.Changes.MemoryUsageChange.PercentChange) {
        $report += "`n- Memory Usage: $($Comparison.Changes.MemoryUsageChange.PercentChange.ToString('+0.0;-0.0;0.0'))% ($($Comparison.Changes.MemoryUsageChange.Severity) impact)"
    }

    if ($Comparison.PerformanceInsights.Count -gt 0) {
        $report += "`n`nKey Insights:"
        foreach ($insight in $Comparison.PerformanceInsights) {
            $report += "`n- $insight"
        }
    }
    
    return $report
}

# Main execution
if ($OriginalFile -and $MathlibFile) {
    Write-Host "Running performance benchmark comparison..." -ForegroundColor Cyan
    
    try {
        $originalBenchmark = Measure-LeanCompilation $OriginalFile $BenchmarkRuns
        $mathlibBenchmark = Measure-LeanCompilation $MathlibFile $BenchmarkRuns
        
        $comparison = Compare-Performance $originalBenchmark $mathlibBenchmark
        $report = Format-PerformanceBenchmark $comparison $OutputFormat
        
        Write-Host $report
        
        # Save report if requested
        if ($IncludeMemoryProfiling) {
            $reportPath = "mathlib-comparison\performance_benchmark_$(Get-Date -Format 'yyyyMMdd_HHmmss').txt"
            $report | Out-File -FilePath $reportPath -Encoding UTF8
            Write-Host "`nBenchmark report saved to: $reportPath" -ForegroundColor Green
        }
        
    } catch {
        Write-Host "Error during performance benchmarking: $($_.Exception.Message)" -ForegroundColor Red
    }
} else {
    Write-Host @"
Performance Benchmarking System

Usage:
  .\PerformanceBenchmarker.ps1 -OriginalFile <path> -MathlibFile <path> [-BenchmarkRuns <num>] [-OutputFormat <format>] [-IncludeMemoryProfiling] [-Verbose]

Parameters:
  BenchmarkRuns      - Number of benchmark iterations (default: 3)
  OutputFormat       - Detailed, Summary, or JSON
  IncludeMemoryProfiling - Include memory usage measurements
  Verbose           - Show detailed progress

Examples:
  .\PerformanceBenchmarker.ps1 -OriginalFile "original.lean" -MathlibFile "migrated.lean"
  .\PerformanceBenchmarker.ps1 -OriginalFile "proof.lean" -MathlibFile "proof_mathlib.lean" -BenchmarkRuns 5 -IncludeMemoryProfiling
"@ -ForegroundColor Cyan
}

Export-ModuleMember -Function Measure-LeanCompilation, Compare-Performance, Format-PerformanceBenchmark