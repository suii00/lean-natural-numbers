# Dashboard Auto Update Script
# Periodically collects data and updates the dashboard

param(
    [int]$IntervalSeconds = 30,
    [switch]$Continuous = $false,
    [switch]$OpenBrowser = $false
)

Write-Host "Mathlib Migration Dashboard Update System" -ForegroundColor Cyan
Write-Host ("=" * 60) -ForegroundColor Cyan
Write-Host ""

# Initial execution
Write-Host "Generating dashboard data..." -ForegroundColor Yellow
& ".\GenerateDashboardData.ps1" -ProjectPath "." -OutputFile "dashboard-data.json"

# Open in browser
if ($OpenBrowser) {
    $dashboardPath = Join-Path $PSScriptRoot "mathlib-dashboard.html"
    if (Test-Path $dashboardPath) {
        Write-Host "Opening dashboard in browser..." -ForegroundColor Green
        Start-Process $dashboardPath
    }
}

# Continuous update mode
if ($Continuous) {
    Write-Host ""
    Write-Host "Continuous update mode ($IntervalSeconds second intervals)" -ForegroundColor Cyan
    Write-Host "Press Ctrl+C to exit" -ForegroundColor Yellow
    Write-Host ""
    
    while ($true) {
        Start-Sleep -Seconds $IntervalSeconds
        
        $timestamp = Get-Date -Format "HH:mm:ss"
        Write-Host "[$timestamp] Updating data..." -ForegroundColor Gray
        
        # Generate data (silent mode)
        $output = & ".\GenerateDashboardData.ps1" -ProjectPath "." -OutputFile "dashboard-data.json" 2>&1
        
        Write-Host "[$timestamp] Update complete" -ForegroundColor Green
    }
}

Write-Host ""
Write-Host "Dashboard is ready!" -ForegroundColor Green
Write-Host "Open mathlib-dashboard.html in your browser" -ForegroundColor Cyan