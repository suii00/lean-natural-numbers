# PowerShell Script Testing Tool
# Tests all PowerShell scripts in the project for syntax errors

Write-Host "=" * 60 -ForegroundColor Cyan
Write-Host "PowerShell Script Validation Tool" -ForegroundColor Cyan
Write-Host "=" * 60 -ForegroundColor Cyan
Write-Host ""

$allScripts = Get-ChildItem -Path . -Filter "*.ps1" -Recurse
$results = @()
$errorCount = 0
$successCount = 0

Write-Host "Found $($allScripts.Count) PowerShell scripts to test" -ForegroundColor Yellow
Write-Host ""

foreach ($script in $allScripts) {
    Write-Host "Testing: $($script.Name)" -ForegroundColor Cyan -NoNewline
    
    try {
        $content = Get-Content $script.FullName -Raw -ErrorAction Stop
        $errors = @()
        $tokens = [System.Management.Automation.PSParser]::Tokenize($content, [ref]$errors)
        
        if ($errors.Count -eq 0) {
            Write-Host " [OK]" -ForegroundColor Green
            $successCount++
            $results += @{
                Script = $script.Name
                Path = $script.DirectoryName
                Status = "OK"
                Errors = @()
            }
        } else {
            Write-Host " [ERRORS: $($errors.Count)]" -ForegroundColor Red
            $errorCount++
            $errorMessages = @()
            foreach ($err in $errors) {
                Write-Host "  - Line $($err.Token.StartLine): $($err.Message)" -ForegroundColor Yellow
                $errorMessages += "Line $($err.Token.StartLine): $($err.Message)"
            }
            $results += @{
                Script = $script.Name
                Path = $script.DirectoryName
                Status = "ERROR"
                Errors = $errorMessages
            }
        }
    } catch {
        Write-Host " [FAILED TO READ]" -ForegroundColor Red
        Write-Host "  - Error: $_" -ForegroundColor Yellow
        $errorCount++
        $results += @{
            Script = $script.Name
            Path = $script.DirectoryName
            Status = "FAILED"
            Errors = @("Failed to read file: $_")
        }
    }
}

Write-Host ""
Write-Host "=" * 60 -ForegroundColor Cyan
Write-Host "Summary:" -ForegroundColor Cyan
Write-Host "  Success: $successCount scripts" -ForegroundColor Green
Write-Host "  Errors: $errorCount scripts" -ForegroundColor $(if ($errorCount -gt 0) { "Red" } else { "Green" })
Write-Host "=" * 60 -ForegroundColor Cyan

# Generate report
$reportPath = "powershell-test-report.json"
$results | ConvertTo-Json -Depth 5 | Set-Content $reportPath -Encoding UTF8
Write-Host ""
Write-Host "Report saved to: $reportPath" -ForegroundColor Cyan

# Show problematic scripts
if ($errorCount -gt 0) {
    Write-Host ""
    Write-Host "Scripts with errors:" -ForegroundColor Red
    $results | Where-Object { $_.Status -ne "OK" } | ForEach-Object {
        Write-Host "  - $($_.Script)" -ForegroundColor Yellow
    }
}