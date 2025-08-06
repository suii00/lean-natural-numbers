# 簡単なLeanエラーロガー

param([switch]$AutoCommit)

Write-Host "Lean Error Logger" -ForegroundColor Cyan

$output = lake build 2>&1 | Out-String

if ($output -match "error:") {
    Write-Host "Errors found!" -ForegroundColor Red
    
    $errors = @()
    $lines = $output -split "`n"
    
    foreach ($line in $lines) {
        if ($line -match "(.+):(\d+):(\d+): error: (.+)") {
            $error = @{
                File = $matches[1]
                Line = $matches[2]  
                Message = $matches[4]
                Time = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
            }
            $errors += $error
        }
    }
    
    if ($errors.Count -gt 0) {
        # Create log directory
        if (!(Test-Path "error-logs")) {
            New-Item -ItemType Directory -Name "error-logs" | Out-Null
        }
        
        # Save as JSON
        $timestamp = Get-Date -Format "yyyy-MM-dd_HH-mm-ss"  
        $logFile = "error-logs/errors-$timestamp.json"
        $errors | ConvertTo-Json | Out-File -FilePath $logFile -Encoding UTF8
        
        # Create markdown report
        $reportFile = "error-logs/report-$timestamp.md"
        $md = "# Error Report - $(Get-Date)`n`n"
        $md += "Total Errors: $($errors.Count)`n`n"
        
        for ($i = 0; $i -lt $errors.Count; $i++) {
            $err = $errors[$i]
            $md += "## Error $($i + 1)`n"
            $md += "- File: $($err.File):$($err.Line)`n"
            $md += "- Message: $($err.Message)`n`n"
        }
        
        $md | Out-File -FilePath $reportFile -Encoding UTF8
        
        Write-Host "Log saved: $logFile" -ForegroundColor Green
        Write-Host "Report saved: $reportFile" -ForegroundColor Green
        
        # Git commit if requested
        if ($AutoCommit) {
            git add $logFile $reportFile 2>&1 | Out-Null
            git commit -m "Add error log with $($errors.Count) errors" 2>&1 | Out-Null
            
            if ($LASTEXITCODE -eq 0) {
                Write-Host "Committed to git" -ForegroundColor Green
            }
        }
        
        Write-Host "`nSummary: $($errors.Count) errors found" -ForegroundColor Yellow
    }
} else {
    Write-Host "Build successful!" -ForegroundColor Green
}