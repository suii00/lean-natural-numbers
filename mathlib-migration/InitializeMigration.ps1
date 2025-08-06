# Simple Migration Initialization
# Initialize the migration tracking without Unicode issues

Write-Host "Initializing Mathlib Migration System" -ForegroundColor Cyan

# Create migration directory structure
if (!(Test-Path "mathlib-migration")) {
    New-Item -ItemType Directory -Path "mathlib-migration" -Force | Out-Null
}

if (!(Test-Path "mathlib-migration\migrated")) {
    New-Item -ItemType Directory -Path "mathlib-migration\migrated" -Force | Out-Null
}

# Create basic tracking file
$migrationStatus = @{
    Metadata = @{
        Version = "1.0"
        StartDate = Get-Date -Format "yyyy-MM-dd"
        LastUpdate = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        TotalFiles = 0
        MigratedFiles = 0
        ProgressPercentage = 0.0
    }
    Files = @()
    SuccessfulMigrations = @()
    FailedAttempts = @()
}

# Find Lean files in project
$leanFiles = Get-ChildItem -Path "." -Filter "*.lean" -Recurse | Where-Object {
    $_.FullName -notmatch "\.lake|build|mathlib-migration|temp_|test_"
}

Write-Host "Found $($leanFiles.Count) Lean files to track" -ForegroundColor Gray

# Add files to tracking
foreach ($file in $leanFiles) {
    $relativePath = $file.FullName.Replace("$((Get-Location).Path)\", "").Replace("\", "/")
    
    $fileEntry = @{
        Path = $relativePath
        Name = $file.Name
        Status = "NotStarted"
        OriginalImports = @()
        MathlibImports = @()
        MigrationDate = $null
        Issues = @()
        Notes = ""
    }
    
    # Check current imports
    $content = Get-Content $file.FullName -ErrorAction SilentlyContinue
    if ($content) {
        $imports = $content | Where-Object { $_ -match '^import\s+' }
        $fileEntry.OriginalImports = $imports
        
        if ($imports -match 'Mathlib') {
            $fileEntry.Status = "PartiallyMigrated" 
            $fileEntry.MathlibImports = $imports | Where-Object { $_ -match 'Mathlib' }
        }
    }
    
    $migrationStatus.Files += $fileEntry
}

# Update metadata
$migrationStatus.Metadata.TotalFiles = $migrationStatus.Files.Count
$migrationStatus.Metadata.MigratedFiles = ($migrationStatus.Files | Where-Object { 
    $_.Status -in @("Migrated", "Verified") 
}).Count

if ($migrationStatus.Metadata.TotalFiles -gt 0) {
    $migrationStatus.Metadata.ProgressPercentage = ($migrationStatus.Metadata.MigratedFiles / $migrationStatus.Metadata.TotalFiles) * 100
}

# Save tracking file
$trackingFile = "mathlib-migration\migration_status.json"
$migrationStatus | ConvertTo-Json -Depth 10 | Out-File -FilePath $trackingFile -Encoding UTF8

Write-Host "Migration tracking initialized!" -ForegroundColor Green
Write-Host "  Total files: $($migrationStatus.Metadata.TotalFiles)" -ForegroundColor White
Write-Host "  Already migrated: $($migrationStatus.Metadata.MigratedFiles)" -ForegroundColor White
Write-Host "  Progress: $($migrationStatus.Metadata.ProgressPercentage.ToString('F1'))%" -ForegroundColor White
Write-Host "  Tracking file: $trackingFile" -ForegroundColor Gray

# Show file status breakdown
$statusGroups = $migrationStatus.Files | Group-Object Status
Write-Host "`nFile Status:" -ForegroundColor Yellow
foreach ($group in $statusGroups) {
    Write-Host "  $($group.Name): $($group.Count)" -ForegroundColor White
}

Write-Host "`nNext steps:" -ForegroundColor Cyan
Write-Host "1. Run: .\mathlib-migration\MigrationOrchestrator.ps1 -Action Menu" -ForegroundColor White
Write-Host "2. Select 'Migrate Next File' to start migration" -ForegroundColor White