# Debug Import Test

Write-Host "Debug Import Test" -ForegroundColor Green

# Test simple import with basic syntax
$testFile = "debug_test.lean"

# Try different import variations
$importTests = @(
    "import Mathlib.Tactic.Basic",
    "import Std",
    ""  # No import
)

foreach ($import in $importTests) {
    Write-Host "`nTesting: '$import'" -ForegroundColor Yellow
    
    $content = if ($import) {
        @"
$import

theorem test : True := trivial
"@
    } else {
        "theorem test : True := trivial"
    }
    
    Write-Host "File content:" -ForegroundColor Gray
    $content.Split("`n") | ForEach-Object { Write-Host "  $_" -ForegroundColor White }
    
    $content | Out-File -FilePath $testFile -Encoding UTF8
    
    Write-Host "Running lean check..." -ForegroundColor Gray
    $output = & lake env lean $testFile 2>&1
    $success = $LASTEXITCODE -eq 0
    
    if ($success) {
        Write-Host "SUCCESS" -ForegroundColor Green
    } else {
        Write-Host "FAILED" -ForegroundColor Red
        $output | ForEach-Object {
            Write-Host "  $_" -ForegroundColor Red
        }
    }
    
    Remove-Item $testFile -ErrorAction SilentlyContinue
}

Write-Host "`nDebug complete!" -ForegroundColor Green