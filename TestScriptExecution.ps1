# Test PowerShell Script Execution
Write-Host "Testing PowerShell Script Tools" -ForegroundColor Cyan
Write-Host "=" * 60 -ForegroundColor Cyan

$scripts = @(
    @{Name="GenerateDashboardData.ps1"; Args="-ProjectPath . -OutputFile test.json"},
    @{Name="UpdateDashboard.ps1"; Args="-IntervalSeconds 30"},
    @{Name="TestPowerShellScripts.ps1"; Args=""},
    @{Name="LeanDailyReportSimple.ps1"; Args="-DryRun"},
    @{Name="TestMigration.ps1"; Args="-TestOnly"}
)

$results = @()

foreach ($script in $scripts) {
    Write-Host "`nTesting: $($script.Name)" -ForegroundColor Yellow
    
    $testResult = @{
        Script = $script.Name
        Status = "Unknown"
        Message = ""
    }
    
    # Check if file exists
    if (-not (Test-Path $script.Name)) {
        Write-Host "  [NOT FOUND] Script file does not exist" -ForegroundColor Red
        $testResult.Status = "NOT FOUND"
        $testResult.Message = "File does not exist"
        $results += $testResult
        continue
    }
    
    # Test syntax
    try {
        $errors = @()
        $content = Get-Content $script.Name -Raw
        $null = [System.Management.Automation.PSParser]::Tokenize($content, [ref]$errors)
        
        if ($errors.Count -gt 0) {
            Write-Host "  [SYNTAX ERROR] $($errors.Count) syntax errors found" -ForegroundColor Red
            $testResult.Status = "SYNTAX ERROR"
            $testResult.Message = "$($errors.Count) syntax errors"
        } else {
            Write-Host "  [OK] Syntax check passed" -ForegroundColor Green
            $testResult.Status = "OK"
            $testResult.Message = "Syntax valid"
        }
    } catch {
        Write-Host "  [ERROR] Failed to parse: $_" -ForegroundColor Red
        $testResult.Status = "ERROR"
        $testResult.Message = "Parse failed: $_"
    }
    
    $results += $testResult
}

# Summary
Write-Host "`n" + ("=" * 60) -ForegroundColor Cyan
Write-Host "Summary:" -ForegroundColor Cyan

$okCount = ($results | Where-Object { $_.Status -eq "OK" }).Count
$errorCount = ($results | Where-Object { $_.Status -ne "OK" }).Count

Write-Host "  Scripts OK: $okCount" -ForegroundColor Green
if ($errorCount -gt 0) {
    Write-Host "  Scripts with issues: $errorCount" -ForegroundColor Red
    Write-Host "`nProblematic scripts:" -ForegroundColor Yellow
    $results | Where-Object { $_.Status -ne "OK" } | ForEach-Object {
        Write-Host "  - $($_.Script): $($_.Status)" -ForegroundColor Yellow
    }
}

# Save results
$results | ConvertTo-Json -Depth 3 | Set-Content "script-test-results.json" -Encoding UTF8
Write-Host "`nResults saved to: script-test-results.json" -ForegroundColor Cyan