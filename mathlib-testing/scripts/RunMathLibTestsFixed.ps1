# Mathlib Import Testing System - Fixed Encoding
# Progressive import test + error analysis + auto-fix + result recording

param(
    [switch]$AutoFix,
    [switch]$Verbose,
    [switch]$SkipDependencyBuild
)

Write-Host "Mathlib Import Testing System" -ForegroundColor Cyan
Write-Host "Progressive import test + error analysis + auto-fix" -ForegroundColor Gray

$timestamp = Get-Date -Format "yyyy-MM-dd_HH-mm-ss"

# Step 1: Build dependencies if needed
if (-not $SkipDependencyBuild) {
    Write-Host "`nStep 1: Checking and building dependencies" -ForegroundColor Yellow
    
    Write-Host "Attempting cache download..." -ForegroundColor Gray
    try {
        $cacheOutput = & lake exe cache get 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-Host "Cache download completed" -ForegroundColor Green
        } else {
            Write-Host "Cache download failed, manual build required" -ForegroundColor Yellow
        }
    } catch {
        Write-Host "Cache download error: $_" -ForegroundColor Yellow
    }
}

# Step 2: Execute progressive import tests
Write-Host "`nStep 2: Execute progressive import tests" -ForegroundColor Yellow

$testParams = @()
if ($Verbose) { $testParams += "-Verbose" }

$testResult = & "mathlib-testing\scripts\MathLibImportTester.ps1" @testParams
$latestLogFile = Get-ChildItem "mathlib-testing\logs\import_test_*.json" | Sort-Object LastWriteTime -Descending | Select-Object -First 1

if ($latestLogFile) {
    Write-Host "Test completed, log file: $($latestLogFile.Name)" -ForegroundColor Green
    
    # Load log data
    $logData = Get-Content $latestLogFile.FullName | ConvertFrom-Json
    $failedTests = $logData.Results | Where-Object { -not $_.Success }
    
    if ($failedTests) {
        Write-Host "`nStep 3: Error analysis started" -ForegroundColor Yellow
        Write-Host "Failed tests: $($failedTests.Count)" -ForegroundColor Red
        
        # Execute error analysis
        $analyzerParams = @{
            ErrorLogFile = $latestLogFile.FullName
        }
        if ($AutoFix) { $analyzerParams.AutoFix = $true }
        
        & "mathlib-testing\scripts\ErrorAnalyzer.ps1" @analyzerParams
        
        # Re-test after auto-fix
        if ($AutoFix) {
            Write-Host "`nStep 4: Re-test after fixes" -ForegroundColor Yellow
            
            Start-Sleep -Seconds 2  # Wait for build completion
            & "mathlib-testing\scripts\MathLibImportTester.ps1" @testParams
            
            $retestLogFile = Get-ChildItem "mathlib-testing\logs\import_test_*.json" | Sort-Object LastWriteTime -Descending | Select-Object -First 1
            $retestData = Get-Content $retestLogFile.FullName | ConvertFrom-Json
            
            Write-Host "`nFix effectiveness:" -ForegroundColor Cyan
            Write-Host "Before fix success rate: $(($logData.TestSession.SuccessRate * 100).ToString('F1'))%" -ForegroundColor Gray
            Write-Host "After fix success rate: $(($retestData.TestSession.SuccessRate * 100).ToString('F1'))%" -ForegroundColor Green
        }
    } else {
        Write-Host "All tests passed successfully!" -ForegroundColor Green
    }
    
} else {
    Write-Host "Test log file not found" -ForegroundColor Red
    exit 1
}

# Step 5: Generate comprehensive report
Write-Host "`nStep 5: Generate comprehensive report" -ForegroundColor Yellow

$summaryFile = "mathlib-testing\logs\test_summary_$timestamp.md"
$summary = @"
# Mathlib Import Testing Summary

## Execution Information
- **Date**: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')
- **Auto-fix**: $(if ($AutoFix) { 'Enabled' } else { 'Disabled' })
- **Verbose output**: $(if ($Verbose) { 'Enabled' } else { 'Disabled' })

## Final Results
"@

# Get latest results
$latestResults = Get-ChildItem "mathlib-testing\logs\import_test_*.json" | Sort-Object LastWriteTime -Descending | Select-Object -First 1
if ($latestResults) {
    $finalData = Get-Content $latestResults.FullName | ConvertFrom-Json
    $summary += @"

- **Total tests**: $($finalData.TestSession.TotalTests)
- **Successful**: $($finalData.TestSession.SuccessCount)  
- **Success rate**: $(($finalData.TestSession.SuccessRate * 100).ToString('F1'))%
- **Highest level reached**: $(($finalData.Results | Where-Object { $_.Success } | Select-Object -Last 1).Level)

## Recommended Next Steps

"@

    if ($finalData.TestSession.SuccessRate -eq 1.0) {
        $summary += "**Complete Success**: All Mathlib imports are working!"
        $summary += "`n- square_even.lean and sqrt2_indep.lean can be improved"
        $summary += "`n- Advanced mathematical proofs can now be implemented"
    } elseif ($finalData.TestSession.SuccessRate -ge 0.6) {
        $summary += "**Partial Success**: Basic functionality works but needs improvement"
        $summary += "`n- Detailed investigation of failed levels required"
        $summary += "`n- Consider running 'lake build' for additional dependencies"
    } else {
        $summary += "**Needs Improvement**: Basic Mathlib imports have issues"
        $summary += "`n- Strongly recommend running 'lake exe cache get'"
        $summary += "`n- Environment configuration review may be needed"
    }
}

$summary += @"

## Generated Files

- Progressive test log: $($latestLogFile.Name)
- Error analysis report: error_analysis_*.md  
- Success pattern DB: database\success_patterns.json
- Error solution DB: database\error_solutions.json

---

*This report was automatically generated by the Mathlib Import Testing System*
"@

$summary | Out-File -FilePath $summaryFile -Encoding UTF8

Write-Host "Comprehensive report generated: $summaryFile" -ForegroundColor Green

# Final message
Write-Host "`nTesting completed!" -ForegroundColor Green
Write-Host "Check the generated report files for details." -ForegroundColor Gray

# Display simple summary
if ($latestLogFile) {
    $data = Get-Content $latestLogFile.FullName | ConvertFrom-Json
    Write-Host "`nFinal result: $($data.TestSession.SuccessCount)/$($data.TestSession.TotalTests) successful ($(($data.TestSession.SuccessRate * 100).ToString('F1'))%)" -ForegroundColor Cyan
}