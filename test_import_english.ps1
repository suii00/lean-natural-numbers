# Simple Import Learning Test - English Version

Write-Host "Import Learning System Test" -ForegroundColor Green

# Test data
$testImports = @(
    "import Mathlib.Tactic.Basic",
    "import Mathlib.Data.Nat.Basic",
    "import Mathlib.NonExistent.Module"
)

$testCases = @{
    "import Mathlib.Tactic.Basic" = "theorem test_basic : True := by trivial"
    "import Mathlib.Data.Nat.Basic" = "theorem test_nat (n : Nat) : n + 0 = n := by sorry"
    "import Mathlib.NonExistent.Module" = "theorem test_fail : True := trivial"
}

Write-Host "Testing $($testImports.Count) imports..." -ForegroundColor Gray

# Create simplified test functions
function Test-SingleImport {
    param([string]$ImportStatement, [string]$TestCode = "")
    
    $timestamp = Get-Date -Format "HHmmss"
    $testFile = "temp_test_$timestamp.lean"
    
    $defaultTest = "theorem test_import : True := trivial"
    $fullTestCode = if ($TestCode) { $TestCode } else { $defaultTest }
    $fileContent = "$ImportStatement`n`n$fullTestCode"
    
    $fileContent | Out-File -FilePath $testFile -Encoding UTF8
    
    try {
        Write-Host "Testing: $ImportStatement" -ForegroundColor Yellow
        $output = & lake env lean $testFile 2>&1
        $success = $LASTEXITCODE -eq 0
        
        if ($success) {
            Write-Host "  SUCCESS" -ForegroundColor Green
        } else {
            Write-Host "  FAILED" -ForegroundColor Red
            $output | Where-Object { $_ -match "error:" } | ForEach-Object {
                Write-Host "  Error: $_" -ForegroundColor Red
            }
        }
        
        return @{
            Import = $ImportStatement
            Success = $success
            Errors = ($output | Where-Object { $_ -match "error:" })
            Output = $output -join "`n"
        }
        
    } finally {
        Remove-Item $testFile -ErrorAction SilentlyContinue
    }
}

# Test all imports
$results = @()
foreach ($import in $testImports) {
    $testCode = if ($testCases.ContainsKey($import)) { $testCases[$import] } else { "" }
    $result = Test-SingleImport $import $testCode
    $results += $result
}

# Summary
$successCount = ($results | Where-Object { $_.Success }).Count
$totalCount = $results.Count

Write-Host "`nSUMMARY:" -ForegroundColor Cyan
Write-Host "  Successful: $successCount / $totalCount" -ForegroundColor Green
Write-Host "  Success Rate: $(($successCount / $totalCount * 100).ToString('F1'))%" -ForegroundColor Green

Write-Host "`nSUCCESSFUL IMPORTS:" -ForegroundColor Green
$results | Where-Object { $_.Success } | ForEach-Object {
    Write-Host "  $($_.Import)" -ForegroundColor White
}

Write-Host "`nFAILED IMPORTS:" -ForegroundColor Red  
$results | Where-Object { -not $_.Success } | ForEach-Object {
    Write-Host "  $($_.Import)" -ForegroundColor White
    $_.Errors | ForEach-Object {
        Write-Host "    $_" -ForegroundColor Gray
    }
}

Write-Host "`nTest completed!" -ForegroundColor Green