# Simple Mathlib Import Test System
param([switch]$Verbose)

$timestamp = Get-Date -Format "yyyy-MM-dd_HH-mm-ss"
Write-Host "Starting Mathlib Import Tests - $timestamp" -ForegroundColor Green

# Test levels with progressive imports
$tests = @(
    @{
        Name = "Level0_Basic"
        Code = "theorem test_basic : True := trivial"
        Imports = @()
    },
    @{
        Name = "Level1_Tactic"
        Code = @"
import Mathlib.Tactic.Basic
theorem test_tactic : True := by trivial
"@
        Imports = @("Mathlib.Tactic.Basic")
    },
    @{
        Name = "Level2_Nat"
        Code = @"
import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Basic
theorem test_nat (n : Nat) : n + 0 = n := Nat.add_zero n
"@
        Imports = @("Mathlib.Tactic.Basic", "Mathlib.Data.Nat.Basic")
    }
)

$results = @()

foreach ($test in $tests) {
    Write-Host "`nTesting $($test.Name)..." -ForegroundColor Yellow
    
    # Create test file
    $testFile = "mathlib-testing\tests\$($test.Name).lean"
    $test.Code | Out-File -FilePath $testFile -Encoding UTF8
    
    # Run test
    $start = Get-Date
    $output = & lake env lean $testFile 2>&1
    $success = $LASTEXITCODE -eq 0
    $duration = (Get-Date) - $start
    
    if ($success) {
        Write-Host "SUCCESS" -ForegroundColor Green
    } else {
        Write-Host "FAILED" -ForegroundColor Red
        if ($Verbose) {
            Write-Host "Error output:" -ForegroundColor Red
            $output | ForEach-Object { Write-Host "  $_" -ForegroundColor Red }
        }
    }
    
    $results += @{
        Name = $test.Name
        Success = $success
        Duration = $duration.TotalSeconds
        Output = $output -join "`n"
        ImportCount = $test.Imports.Count
    }
}

# Summary
$successCount = ($results | Where-Object Success).Count
$totalCount = $results.Count

Write-Host "`n=== SUMMARY ===" -ForegroundColor Cyan
Write-Host "Total: $totalCount, Success: $successCount" -ForegroundColor Cyan
Write-Host "Success Rate: $(($successCount/$totalCount*100).ToString('F1'))%" -ForegroundColor Cyan

# Save results
$logFile = "mathlib-testing\logs\simple_test_$timestamp.json"
$results | ConvertTo-Json | Out-File -FilePath $logFile -Encoding UTF8

Write-Host "Results saved to: $logFile" -ForegroundColor Gray