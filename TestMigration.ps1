# Quick Migration Test

Write-Host "Testing Mathlib Migration System" -ForegroundColor Cyan

# Check if we have any simple Lean files to test with
$testFiles = Get-ChildItem -Path "MyProject" -Filter "*.lean" -Recurse -ErrorAction SilentlyContinue

if ($testFiles.Count -eq 0) {
    Write-Host "No test files found in MyProject directory" -ForegroundColor Yellow
    return
}

$testFile = $testFiles[0]
Write-Host "Testing with file: $($testFile.Name)" -ForegroundColor Gray

# Create a simple migration test
$scriptPath = "mathlib-migration"
$migratorPath = "$scriptPath\ProofMigrator.ps1"

if (Test-Path $migratorPath) {
    Write-Host "Running migration test..." -ForegroundColor Yellow
    
    try {
        & powershell.exe -ExecutionPolicy Bypass -File $migratorPath -SourceFile $testFile.FullName -MigrationLevel "Basic" -DryRun -Verbose
        Write-Host "Migration test completed!" -ForegroundColor Green
    } catch {
        Write-Host "Migration test failed: $_" -ForegroundColor Red
    }
} else {
    Write-Host "Migration tools not found at: $migratorPath" -ForegroundColor Red
}

Write-Host "`nMigration system is ready to use!" -ForegroundColor Green
Write-Host "To start migration:" -ForegroundColor Cyan
Write-Host "  .\mathlib-migration\MigrationOrchestrator.ps1 -Action Menu" -ForegroundColor White