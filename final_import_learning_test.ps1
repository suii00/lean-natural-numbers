# Final Import Learning System Test
# Fixed encoding issues - uses proper file writing without BOM

Write-Host "Final Import Learning System Test" -ForegroundColor Green

function Test-LeanImport {
    param([string]$ImportStatement, [string]$TestCode = "")
    
    $timestamp = Get-Date -Format "HHmmssff"
    $testFile = "temp_$timestamp.lean"
    
    $defaultTest = "theorem test_import : True := trivial"
    $fullTestCode = if ($TestCode) { $TestCode } else { $defaultTest }
    
    # Create file content
    if ($ImportStatement) {
        $content = "$ImportStatement`n`n$fullTestCode"
    } else {
        $content = $fullTestCode
    }
    
    try {
        Write-Host "Testing: $(if($ImportStatement) { $ImportStatement } else { '(no import)' })" -ForegroundColor Yellow
        
        # Write file WITHOUT BOM using [System.IO.File]::WriteAllText
        [System.IO.File]::WriteAllText("$(pwd)\$testFile", $content)
        
        # Test with lean
        $output = & lean $testFile 2>&1
        $leanSuccess = $LASTEXITCODE -eq 0
        
        $result = @{
            Import = $ImportStatement
            Success = $leanSuccess
            Errors = @()
            Output = $output -join "`n"
            TestCode = $fullTestCode
            Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        }
        
        if ($leanSuccess) {
            Write-Host "  ✅ SUCCESS" -ForegroundColor Green
        } else {
            Write-Host "  ❌ FAILED" -ForegroundColor Red
            
            # Extract meaningful errors
            $errors = $output | Where-Object { $_ -match "error:" -or $_ -match "not found" -or $_ -match "unknown" }
            $result.Errors = $errors
            
            $errors | Select-Object -First 2 | ForEach-Object {
                Write-Host "    $_" -ForegroundColor Red
            }
        }
        
        return $result
        
    } finally {
        Remove-Item $testFile -ErrorAction SilentlyContinue
    }
}

# Initialize learning database
$learningDatabase = @{
    Metadata = @{
        Version = "1.0"
        Created = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        TotalAttempts = 0
        SuccessRate = 0.0
    }
    SuccessfulPatterns = @()
    ErrorPatterns = @()
    ImportAttempts = @()
}

# Test cases for mathlib import learning
$testImports = @(
    "", # Baseline - no import
    "import Std",
    "import Mathlib.Tactic.Basic",
    "import Mathlib.Data.Nat.Basic",
    "import Mathlib.Data.Int.Basic",
    "import Mathlib.Tactic.Ring",
    "import Mathlib.Data.Nat.Parity",
    "import Mathlib.NonExistent"  # Intentional failure
)

$testCases = @{
    "" = "theorem baseline : True := trivial"
    "import Std" = "theorem test_std : True := trivial"
    "import Mathlib.Tactic.Basic" = "theorem test_basic : True := by trivial"
    "import Mathlib.Data.Nat.Basic" = "theorem test_nat (n : Nat) : n + 0 = n := by sorry"
    "import Mathlib.Data.Int.Basic" = "theorem test_int (n : Int) : n + 0 = n := by sorry"
    "import Mathlib.Tactic.Ring" = "theorem test_ring (a b : Nat) : (a + b) * (a + b) = a*a + 2*a*b + b*b := by sorry"  # ring tactic would need build
    "import Mathlib.Data.Nat.Parity" = "theorem test_parity : Even 4 := by sorry"  # Even would need build
    "import Mathlib.NonExistent" = "theorem test_fail : True := trivial"
}

Write-Host "Testing $($testImports.Count) import patterns..." -ForegroundColor Gray
Write-Host ""

# Test each import and record results
foreach ($import in $testImports) {
    $testCode = if ($testCases.ContainsKey($import)) { $testCases[$import] } else { "theorem test : True := trivial" }
    $result = Test-LeanImport $import $testCode
    
    # Add to database
    $learningDatabase.ImportAttempts += $result
    $learningDatabase.Metadata.TotalAttempts++
    
    if ($result.Success) {
        # Record successful pattern
        $successPattern = @{
            ImportStatement = $result.Import
            TestCode = $result.TestCode
            FirstSuccessDate = $result.Timestamp
            SuccessCount = 1
        }
        $learningDatabase.SuccessfulPatterns += $successPattern
    } else {
        # Analyze and record error pattern
        $errorPattern = @{
            ImportStatement = $result.Import
            ErrorMessages = $result.Errors
            Timestamp = $result.Timestamp
            ErrorType = "ImportFailure"
            SuggestedFixes = @()
        }
        
        # Analyze error and suggest fixes
        foreach ($error in $result.Errors) {
            if ($error -match "not found" -or $error -match "object file.*does not exist") {
                $errorPattern.ErrorType = "MissingDependency"
                $errorPattern.SuggestedFixes += "Run: lake build"
                $errorPattern.SuggestedFixes += "Run: lake exe cache get"
            } elseif ($error -match "unknown identifier") {
                $errorPattern.ErrorType = "UnknownIdentifier"
                $errorPattern.SuggestedFixes += "Check import statement"
                $errorPattern.SuggestedFixes += "Verify Mathlib build"
            } elseif ($error -match "module.*not found") {
                $errorPattern.ErrorType = "ModuleNotFound"
                $errorPattern.SuggestedFixes += "Check module name spelling"
                $errorPattern.SuggestedFixes += "Update Mathlib version"
            }
        }
        
        $learningDatabase.ErrorPatterns += $errorPattern
    }
}

# Calculate success rate
$successCount = $learningDatabase.SuccessfulPatterns.Count
$totalCount = $learningDatabase.Metadata.TotalAttempts
$learningDatabase.Metadata.SuccessRate = if ($totalCount -gt 0) { $successCount / $totalCount } else { 0 }

# Display comprehensive results
Write-Host ""
Write-Host "="*60 -ForegroundColor Cyan
Write-Host "IMPORT LEARNING RESULTS & ANALYSIS" -ForegroundColor Cyan
Write-Host "="*60 -ForegroundColor Cyan

Write-Host "`n📊 SUMMARY STATISTICS:" -ForegroundColor Yellow
Write-Host "  Total Tests: $totalCount" -ForegroundColor White
Write-Host "  Successful: $successCount" -ForegroundColor Green
Write-Host "  Failed: $($totalCount - $successCount)" -ForegroundColor Red
Write-Host "  Success Rate: $(($learningDatabase.Metadata.SuccessRate * 100).ToString('F1'))%" -ForegroundColor Green

if ($successCount -gt 0) {
    Write-Host "`n✅ SUCCESSFUL IMPORTS:" -ForegroundColor Green
    $learningDatabase.SuccessfulPatterns | ForEach-Object {
        $importText = if ($_.ImportStatement) { $_.ImportStatement } else { "(no import baseline)" }
        Write-Host "  $importText" -ForegroundColor White
    }
}

if ($learningDatabase.ErrorPatterns.Count -gt 0) {
    Write-Host "`n❌ FAILED IMPORTS & ANALYSIS:" -ForegroundColor Red
    $learningDatabase.ErrorPatterns | ForEach-Object {
        $importText = if ($_.ImportStatement) { $_.ImportStatement } else { "(no import baseline)" }
        Write-Host "  $importText" -ForegroundColor White
        Write-Host "    Error Type: $($_.ErrorType)" -ForegroundColor Yellow
        
        if ($_.SuggestedFixes.Count -gt 0) {
            Write-Host "    Suggested Fixes:" -ForegroundColor Cyan
            $_.SuggestedFixes | ForEach-Object {
                Write-Host "      - $_" -ForegroundColor Gray
            }
        }
        Write-Host ""
    }
}

# Generate insights and recommendations
$insights = @()

$noImportSuccess = $learningDatabase.SuccessfulPatterns | Where-Object { -not $_.ImportStatement }
if ($noImportSuccess) {
    $insights += "✅ Basic Lean syntax works without imports"
}

$stdSuccess = $learningDatabase.SuccessfulPatterns | Where-Object { $_.ImportStatement -eq "import Std" }
if ($stdSuccess) {
    $insights += "✅ Std library is available and working"
} else {
    $insights += "⚠️ Std library not working - may need setup"
}

$mathlibSuccesses = $learningDatabase.SuccessfulPatterns | Where-Object { $_.ImportStatement -match "Mathlib" }
$mathlibFailures = $learningDatabase.ErrorPatterns | Where-Object { $_.ImportStatement -match "Mathlib" }

if ($mathlibSuccesses.Count -gt 0) {
    $insights += "✅ Some Mathlib modules work: $($mathlibSuccesses.Count) successful"
} 

if ($mathlibFailures.Count -gt 0) {
    $insights += "❌ Mathlib issues detected: $($mathlibFailures.Count) failures"
    $insights += "💡 Most likely needs: lake build or lake exe cache get"
}

$dependencyErrors = $learningDatabase.ErrorPatterns | Where-Object { $_.ErrorType -eq "MissingDependency" }
if ($dependencyErrors.Count -gt 0) {
    $insights += "🔧 $($dependencyErrors.Count) dependency errors - Mathlib build required"
}

Write-Host "🧠 LEARNING INSIGHTS:" -ForegroundColor Cyan
$insights | ForEach-Object {
    Write-Host "  $_" -ForegroundColor White
}

# Save learning database to JSON
$databaseFile = "import_learning_database.json"
$learningDatabase | ConvertTo-Json -Depth 10 | Out-File -FilePath $databaseFile -Encoding UTF8

Write-Host "`n💾 Learning database saved to: $databaseFile" -ForegroundColor Green

# Generate markdown report
$reportFile = "import_learning_report.md"
$report = @"
# Mathlib Import Learning Report

Generated: $((Get-Date).ToString('yyyy-MM-dd HH:mm:ss'))

## Summary Statistics

- **Total Tests**: $totalCount
- **Successful**: $successCount  
- **Failed**: $($totalCount - $successCount)
- **Success Rate**: $(($learningDatabase.Metadata.SuccessRate * 100).ToString('F1'))%

## Successful Imports

"@

$learningDatabase.SuccessfulPatterns | ForEach-Object {
    $importText = if ($_.ImportStatement) { "`$($_.ImportStatement)`" } else { "(no import baseline)" }
    $report += "- $importText`n"
}

$report += "`n## Failed Imports & Solutions`n`n"

$learningDatabase.ErrorPatterns | ForEach-Object {
    $importText = if ($_.ImportStatement) { "`$($_.ImportStatement)`" } else { "(no import baseline)" }
    $report += "### $importText`n`n"
    $report += "**Error Type**: $($_.ErrorType)`n`n"
    
    if ($_.SuggestedFixes.Count -gt 0) {
        $report += "**Suggested Fixes**:`n"
        $_.SuggestedFixes | ForEach-Object {
            $report += "- $_`n"
        }
        $report += "`n"
    }
}

$report += "## Learning Insights`n`n"
$insights | ForEach-Object {
    $report += "- $_`n"
}

$report += "`n---`n*Generated by Import Learning System*"

[System.IO.File]::WriteAllText("$(pwd)\$reportFile", $report)

Write-Host "📄 Learning report saved to: $reportFile" -ForegroundColor Green
Write-Host ""
Write-Host "🎯 Import learning system test completed successfully!" -ForegroundColor Green
Write-Host "   Database: $databaseFile" -ForegroundColor Gray
Write-Host "   Report: $reportFile" -ForegroundColor Gray