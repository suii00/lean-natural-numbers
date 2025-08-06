# Simplified Import Learning Test - Fixed Encoding

Write-Host "Import Learning System Test" -ForegroundColor Green

function Test-Import {
    param([string]$Import, [string]$Code)
    
    $timestamp = Get-Date -Format "HHmmssff"
    $testFile = "temp_$timestamp.lean"
    
    $content = if ($Import) { "$Import`n`n$Code" } else { $Code }
    
    try {
        # Write file without BOM
        [System.IO.File]::WriteAllText("$(pwd)\$testFile", $content)
        
        $output = & lean $testFile 2>&1
        $success = $LASTEXITCODE -eq 0
        
        $importName = if ($Import) { $Import } else { "(baseline)" }
        if ($success) {
            Write-Host "SUCCESS: $importName" -ForegroundColor Green
        } else {
            Write-Host "FAILED:  $importName" -ForegroundColor Red
            $output | Where-Object { $_ -match "error:" } | Select-Object -First 1 | ForEach-Object {
                Write-Host "  Error: $_" -ForegroundColor Red
            }
        }
        
        return @{
            Import = $Import
            Success = $success
            Errors = ($output | Where-Object { $_ -match "error:" })
        }
        
    } finally {
        Remove-Item $testFile -ErrorAction SilentlyContinue
    }
}

# Test cases
$tests = @(
    @{ Import = ""; Code = "theorem baseline : True := trivial" },
    @{ Import = "import Std"; Code = "theorem test_std : True := trivial" },
    @{ Import = "import Mathlib.Tactic.Basic"; Code = "theorem test_basic : True := by trivial" },
    @{ Import = "import Mathlib.Data.Nat.Basic"; Code = "theorem test_nat (n : Nat) : n + 0 = n := by sorry" },
    @{ Import = "import Mathlib.Data.Int.Basic"; Code = "theorem test_int (n : Int) : n + 0 = n := by sorry" }
)

Write-Host "Testing $($tests.Count) imports...`n" -ForegroundColor Gray

# Run tests
$results = @()
foreach ($test in $tests) {
    $result = Test-Import $test.Import $test.Code
    $results += $result
}

# Summary
$successCount = ($results | Where-Object { $_.Success }).Count
$totalCount = $results.Count

Write-Host "`n" + "="*50
Write-Host "RESULTS SUMMARY"
Write-Host "="*50

Write-Host "Total Tests: $totalCount"
Write-Host "Successful: $successCount" -ForegroundColor Green
Write-Host "Failed: $($totalCount - $successCount)" -ForegroundColor Red
Write-Host "Success Rate: $(($successCount / $totalCount * 100).ToString('F1'))%"

Write-Host "`nSUCCESSFUL IMPORTS:" -ForegroundColor Green
$results | Where-Object { $_.Success } | ForEach-Object {
    $name = if ($_.Import) { $_.Import } else { "(no import)" }
    Write-Host "  $name" -ForegroundColor White
}

Write-Host "`nFAILED IMPORTS:" -ForegroundColor Red
$results | Where-Object { -not $_.Success } | ForEach-Object {
    $name = if ($_.Import) { $_.Import } else { "(no import)" }
    Write-Host "  $name" -ForegroundColor White
}

# Save results
$database = @{
    Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    TotalTests = $totalCount
    Successful = $successCount
    Results = $results
}

$database | ConvertTo-Json -Depth 5 | Out-File "import_test_results.json" -Encoding UTF8

Write-Host "`nResults saved to: import_test_results.json" -ForegroundColor Green
Write-Host "Import learning test completed!" -ForegroundColor Green