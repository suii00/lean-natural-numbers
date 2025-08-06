# Simple Mathlib Converter - Fixed Encoding Version

param(
    [string]$InputFile,
    [string]$OutputFile = "",
    [switch]$DryRun,
    [switch]$Verbose
)

function Convert-LeanToMathlib {
    param([string]$FilePath)
    
    Write-Host "Converting Lean file to Mathlib format: $FilePath" -ForegroundColor Green
    
    if (-not (Test-Path $FilePath)) {
        Write-Error "File not found: $FilePath"
        return
    }
    
    $lines = Get-Content $FilePath -Encoding UTF8
    $convertedLines = @()
    $changesApplied = 0
    
    foreach ($line in $lines) {
        $originalLine = $line
        $convertedLine = $line
        
        # Import conversions
        if ($line -match "^-- Basic.*without.*imports") {
            $convertedLine = "import Mathlib.Tactic.Basic"
            $changesApplied++
            if ($Verbose) { Write-Host "Added basic import" -ForegroundColor Yellow }
        }
        
        # Theorem name conversions
        $convertedLine = $convertedLine -replace "Nat\.add_zero", "add_zero"
        $convertedLine = $convertedLine -replace "Nat\.zero_add", "zero_add"
        $convertedLine = $convertedLine -replace "Nat\.add_comm", "add_comm"
        
        # Type conversions
        $convertedLine = $convertedLine -replace "\bNat\b", "N"  # Using N instead of unicode
        $convertedLine = $convertedLine -replace "\bInt\b", "Z"  # Using Z instead of unicode
        
        # Tactic conversions
        $convertedLine = $convertedLine -replace "exact <([^>]*)>", "use $1"
        
        if ($convertedLine -ne $originalLine) {
            $changesApplied++
            if ($Verbose) {
                Write-Host "Converted: '$originalLine' -> '$convertedLine'" -ForegroundColor Cyan
            }
        }
        
        $convertedLines += $convertedLine
    }
    
    # Add basic import if none exists
    if (-not ($convertedLines | Where-Object { $_ -match "^import" })) {
        $convertedLines = @("import Mathlib.Tactic.Basic", "") + $convertedLines
        $changesApplied++
        if ($Verbose) { Write-Host "Added Mathlib.Tactic.Basic import" -ForegroundColor Green }
    }
    
    # Output handling
    $outputPath = if ($OutputFile) { 
        $OutputFile 
    } else { 
        $FilePath -replace "\.lean$", "_mathlib.lean" 
    }
    
    if ($DryRun) {
        Write-Host "DRY RUN - Preview of changes:" -ForegroundColor Cyan
        Write-Host "Changes applied: $changesApplied" -ForegroundColor Gray
        Write-Host "Output would be: $outputPath" -ForegroundColor Gray
        Write-Host "First 5 lines:" -ForegroundColor Gray
        $convertedLines | Select-Object -First 5 | ForEach-Object { Write-Host "  $_" -ForegroundColor White }
        return
    }
    
    # Save converted file
    $convertedLines | Out-File -FilePath $outputPath -Encoding UTF8
    
    Write-Host "Conversion completed!" -ForegroundColor Green
    Write-Host "Changes applied: $changesApplied" -ForegroundColor Gray
    Write-Host "Output file: $outputPath" -ForegroundColor Gray
    
    return $outputPath
}

# Test the converted file
function Test-ConvertedFile {
    param([string]$FilePath)
    
    Write-Host "Testing converted file..." -ForegroundColor Yellow
    
    $output = & lake env lean $FilePath 2>&1
    $success = $LASTEXITCODE -eq 0
    
    if ($success) {
        Write-Host "SUCCESS: File compiles without errors" -ForegroundColor Green
    } else {
        Write-Host "ERRORS DETECTED:" -ForegroundColor Red
        $errors = $output | Where-Object { $_ -match "error:" }
        $errors | ForEach-Object { Write-Host "  $_" -ForegroundColor Red }
    }
    
    return $success
}

# Main execution
if ($InputFile) {
    $convertedFile = Convert-LeanToMathlib $InputFile
    
    if ($convertedFile -and -not $DryRun) {
        Write-Host "`nTesting conversion result..." -ForegroundColor Cyan
        Test-ConvertedFile $convertedFile
    }
} else {
    Write-Host "Usage:"
    Write-Host "  .\SimpleMathLibConverter.ps1 -InputFile 'file.lean' [-OutputFile 'output.lean'] [-DryRun] [-Verbose]"
}