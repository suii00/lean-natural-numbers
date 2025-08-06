# Working Import Learning Test

Write-Host "Import Learning System Test - Working Version" -ForegroundColor Green

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
    
    # Write file
    $content | Out-File -FilePath $testFile -Encoding UTF8
    
    try {
        Write-Host "Testing: $ImportStatement" -ForegroundColor Yellow
        
        # Try lean directly first
        $output = & lean $testFile 2>&1
        $leanSuccess = $LASTEXITCODE -eq 0
        
        $result = @{
            Import = $ImportStatement
            Success = $leanSuccess
            Method = "lean"
            Errors = @()
            Output = $output -join "`n"
        }
        
        if ($leanSuccess) {
            Write-Host "  SUCCESS with lean" -ForegroundColor Green
        } else {
            Write-Host "  FAILED with lean" -ForegroundColor Red
            
            # Extract meaningful errors
            $errors = $output | Where-Object { $_ -match "error:" -or $_ -match "not found" -or $_ -match "unknown" }
            $result.Errors = $errors
            
            $errors | ForEach-Object {
                Write-Host "    Error: $_" -ForegroundColor Red
            }
        }
        
        return $result
        
    } finally {
        Remove-Item $testFile -ErrorAction SilentlyContinue
    }
}

# Database for learning
$learningResults = @{
    Successful = @()
    Failed = @()
    Insights = @()
}

# Test cases
$testImports = @(
    "", # No import baseline
    "import Std",
    "import Mathlib.Tactic.Basic",
    "import Mathlib.Data.Nat.Basic",
    "import Mathlib.NonExistent"
)

$testCases = @{
    "" = "theorem baseline : True := trivial"
    "import Std" = "theorem test_std : True := trivial"
    "import Mathlib.Tactic.Basic" = "theorem test_tactic : True := by trivial"
    "import Mathlib.Data.Nat.Basic" = "theorem test_nat (n : Nat) : n + 0 = n := by sorry"
    "import Mathlib.NonExistent" = "theorem test_fail : True := trivial"
}

Write-Host "Testing $($testImports.Count) import patterns..." -ForegroundColor Gray

# Test each import
foreach ($import in $testImports) {
    $testCode = if ($testCases.ContainsKey($import)) { $testCases[$import] } else { "theorem test : True := trivial" }
    $result = Test-LeanImport $import $testCode
    
    if ($result.Success) {
        $learningResults.Successful += $result
    } else {
        $learningResults.Failed += $result
    }
}

# Analyze results
$successCount = $learningResults.Successful.Count
$failCount = $learningResults.Failed.Count
$totalCount = $successCount + $failCount

Write-Host "`n" + "="*50 -ForegroundColor Cyan
Write-Host "IMPORT LEARNING RESULTS" -ForegroundColor Cyan
Write-Host "="*50 -ForegroundColor Cyan

Write-Host "`nSUMMARY:" -ForegroundColor Yellow
Write-Host "  Total Tests: $totalCount" -ForegroundColor White
Write-Host "  Successful: $successCount" -ForegroundColor Green
Write-Host "  Failed: $failCount" -ForegroundColor Red
Write-Host "  Success Rate: $(if($totalCount -gt 0) { ($successCount / $totalCount * 100).ToString('F1') } else { '0' })%" -ForegroundColor Green

if ($successCount -gt 0) {
    Write-Host "`nSUCCESSFUL IMPORTS:" -ForegroundColor Green
    $learningResults.Successful | ForEach-Object {
        $importText = if ($_.Import) { $_.Import } else { "(no import)" }
        Write-Host "  ✅ $importText" -ForegroundColor White
    }
}

if ($failCount -gt 0) {
    Write-Host "`nFAILED IMPORTS:" -ForegroundColor Red
    $learningResults.Failed | ForEach-Object {
        $importText = if ($_.Import) { $_.Import } else { "(no import)" }
        Write-Host "  ❌ $importText" -ForegroundColor White
        
        if ($_.Errors.Count -gt 0) {
            $_.Errors | Select-Object -First 2 | ForEach-Object {
                Write-Host "     $_" -ForegroundColor Gray
            }
        }
    }
}

# Generate learning insights
$insights = @()

if ($successCount -gt 0) {
    $insights += "✅ Basic Lean syntax works without imports"
}

$stdResult = $learningResults.Successful | Where-Object { $_.Import -eq "import Std" }
if ($stdResult) {
    $insights += "✅ Std library imports are working"
}

$mathlibResults = $learningResults.Failed | Where-Object { $_.Import -match "Mathlib" }
if ($mathlibResults.Count -gt 0) {
    $insights += "❌ Mathlib imports are not working - dependency issues"
    $insights += "💡 Mathlib may need: lake build, cache get, or proper setup"
}

if ($insights.Count -gt 0) {
    Write-Host "`nLEARNING INSIGHTS:" -ForegroundColor Cyan
    $insights | ForEach-Object {
        Write-Host "  $_" -ForegroundColor White
    }
}

# Save results to simple database
$databaseFile = "import_learning_results.json"
$learningResults | ConvertTo-Json -Depth 5 | Out-File -FilePath $databaseFile -Encoding UTF8

Write-Host "`n💾 Results saved to: $databaseFile" -ForegroundColor Green
Write-Host "🎯 Import learning test completed!" -ForegroundColor Green