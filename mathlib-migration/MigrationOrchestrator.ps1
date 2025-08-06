# Mathlib Migration Orchestrator
# Main control system for the gradual migration workflow

param(
    [string]$Action = "Status", # Status, Initialize, Migrate, Verify, Merge
    [string]$Strategy = "Progressive", # Simple, Progressive, Advanced
    [switch]$Interactive,
    [switch]$DryRun,
    [switch]$Verbose
)

# Import all migration modules
$scriptPath = Split-Path -Parent $MyInvocation.MyCommand.Definition
. "$scriptPath\MigrationTracker.ps1"
. "$scriptPath\ProofMigrator.ps1"
. "$scriptPath\MigrationVerifier.ps1"
. "$scriptPath\SelectiveMerger.ps1"

function Show-MigrationMenu {
    Clear-Host
    Write-Host @"
🔄 Mathlib Gradual Migration System 🔄
=====================================

Current Branch: $(& git rev-parse --abbrev-ref HEAD 2>$null)
Current Time: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')

"@ -ForegroundColor Cyan

    # Quick status check
    $tracking = Initialize-MigrationTracking
    Write-Host "Migration Progress: $($tracking.Metadata.ProgressPercentage.ToString('F1'))% complete" -ForegroundColor $(
        if ($tracking.Metadata.ProgressPercentage -ge 75) { 'Green' }
        elseif ($tracking.Metadata.ProgressPercentage -ge 50) { 'Yellow' }
        else { 'Red' }
    )
    Write-Host "Files: $($tracking.Metadata.MigratedFiles)/$($tracking.Metadata.TotalFiles) migrated" -ForegroundColor Gray

    Write-Host "`nSelect an action:" -ForegroundColor Yellow
    Write-Host "1. 📊 Show Migration Status" -ForegroundColor White
    Write-Host "2. 🎯 Migrate Next File" -ForegroundColor Green
    Write-Host "3. 📁 Migrate Specific File" -ForegroundColor Cyan
    Write-Host "4. 🔍 Verify Migrated Files" -ForegroundColor Blue
    Write-Host "5. 🔀 Merge Ready Files" -ForegroundColor Magenta
    Write-Host "6. 📈 Generate Progress Report" -ForegroundColor Yellow
    Write-Host "7. 🔧 Advanced Options" -ForegroundColor Gray
    Write-Host "8. 🚪 Exit" -ForegroundColor Red

    Write-Host "`nChoice (1-8): " -ForegroundColor Yellow -NoNewline
    return Read-Host
}

function Show-MigrationStatus {
    Write-Host "`n📊 MIGRATION STATUS" -ForegroundColor Cyan
    Write-Host "===================" -ForegroundColor Cyan
    
    $tracking = Initialize-MigrationTracking
    Get-MigrationStatus $tracking
    
    Write-Host "`nPress Enter to continue..." -ForegroundColor Gray
    Read-Host
}

function Migrate-NextFile {
    param([string]$Strategy)
    
    Write-Host "`n🎯 MIGRATE NEXT FILE" -ForegroundColor Green
    Write-Host "===================" -ForegroundColor Green
    
    $tracking = Initialize-MigrationTracking
    $nextFile = Get-NextMigrationTarget $tracking $Strategy
    
    if (!$nextFile) {
        Write-Host "🎉 No more files to migrate! All files are complete." -ForegroundColor Green
        return
    }
    
    Write-Host "Next migration target:" -ForegroundColor Yellow
    Write-Host "  File: $($nextFile.Name)" -ForegroundColor White
    Write-Host "  Status: $($nextFile.Status)" -ForegroundColor Gray
    Write-Host "  Imports: $($nextFile.OriginalImports.Count)" -ForegroundColor Gray
    
    if ($Interactive) {
        Write-Host "`nProceed with migration? (y/n): " -ForegroundColor Yellow -NoNewline
        $proceed = Read-Host
        if ($proceed -ne 'y' -and $proceed -ne 'Y') {
            return
        }
        
        Write-Host "Select migration level:" -ForegroundColor Yellow
        Write-Host "  1. Basic - Add basic Mathlib imports only" -ForegroundColor White
        Write-Host "  2. Standard - Add imports and convert types" -ForegroundColor White
        Write-Host "  3. Advanced - Full migration with tactics" -ForegroundColor White
        Write-Host "Choice (1-3): " -ForegroundColor Yellow -NoNewline
        $levelChoice = Read-Host
        
        $migrationLevel = switch ($levelChoice) {
            "1" { "Basic" }
            "2" { "Standard" }
            "3" { "Advanced" }
            default { "Standard" }
        }
    } else {
        $migrationLevel = "Standard"
    }
    
    # Perform migration
    $originalFile = $nextFile.Path
    if (!(Test-Path $originalFile)) {
        Write-Host "❌ Original file not found: $originalFile" -ForegroundColor Red
        return
    }
    
    Write-Host "`nMigrating file with $migrationLevel level..." -ForegroundColor Cyan
    
    $migrationResult = Migrate-SingleFile $originalFile "" $migrationLevel
    
    if ($migrationResult.Success) {
        Write-Host "✅ Migration completed" -ForegroundColor Green
        
        # Update tracking
        Update-FileMigrationStatus $tracking $nextFile.Path "Migrated" "Migrated with $migrationLevel level"
        
        # Auto-verify if not dry run
        if (!$DryRun -and $migrationResult.OutputFile) {
            Write-Host "`n🔍 Auto-verifying migrated file..." -ForegroundColor Cyan
            $verificationResult = Run-VerificationSuite $migrationResult.OutputFile "Standard"
            
            if ($verificationResult.OverallSuccess) {
                Update-FileMigrationStatus $tracking $nextFile.Path "Verified" "Migration verified successfully"
                Write-Host "✅ File verified and ready for merge" -ForegroundColor Green
            } else {
                Write-Host "⚠️ File migrated but verification failed" -ForegroundColor Yellow
            }
        }
    } else {
        Write-Host "❌ Migration failed" -ForegroundColor Red
        Update-FileMigrationStatus $tracking $nextFile.Path "Failed" "Migration failed"
    }
    
    Write-Host "`nPress Enter to continue..." -ForegroundColor Gray
    Read-Host
}

function Migrate-SpecificFile {
    Write-Host "`n📁 MIGRATE SPECIFIC FILE" -ForegroundColor Cyan
    Write-Host "========================" -ForegroundColor Cyan
    
    $tracking = Initialize-MigrationTracking
    
    # Show available files
    $availableFiles = $tracking.Files | Where-Object { $_.Status -in @("NotStarted", "PartiallyMigrated", "Failed") }
    
    if ($availableFiles.Count -eq 0) {
        Write-Host "No files available for migration" -ForegroundColor Yellow
        return
    }
    
    Write-Host "Available files:" -ForegroundColor Yellow
    for ($i = 0; $i -lt $availableFiles.Count; $i++) {
        $file = $availableFiles[$i]
        Write-Host "  $($i+1). $($file.Name) ($($file.Status))" -ForegroundColor White
    }
    
    Write-Host "`nSelect file number: " -ForegroundColor Yellow -NoNewline
    $selection = Read-Host
    
    $index = [int]$selection - 1
    if ($index -lt 0 -or $index -ge $availableFiles.Count) {
        Write-Host "Invalid selection" -ForegroundColor Red
        return
    }
    
    $selectedFile = $availableFiles[$index]
    
    # Proceed with migration (similar to Migrate-NextFile)
    $migrationResult = Migrate-SingleFile $selectedFile.Path "" "Standard"
    
    if ($migrationResult.Success) {
        Update-FileMigrationStatus $tracking $selectedFile.Path "Migrated" "User-selected migration"
        Write-Host "✅ Migration completed for $($selectedFile.Name)" -ForegroundColor Green
    } else {
        Update-FileMigrationStatus $tracking $selectedFile.Path "Failed" "Migration failed"
        Write-Host "❌ Migration failed for $($selectedFile.Name)" -ForegroundColor Red
    }
    
    Write-Host "`nPress Enter to continue..." -ForegroundColor Gray
    Read-Host
}

function Verify-MigratedFiles {
    Write-Host "`n🔍 VERIFY MIGRATED FILES" -ForegroundColor Blue
    Write-Host "========================" -ForegroundColor Blue
    
    # Run verification on all migrated files
    & powershell.exe -ExecutionPolicy Bypass -File "$scriptPath\MigrationVerifier.ps1" -RunAllTests -Verbose:$Verbose
    
    Write-Host "`nPress Enter to continue..." -ForegroundColor Gray
    Read-Host
}

function Merge-ReadyFiles {
    Write-Host "`n🔀 MERGE READY FILES" -ForegroundColor Magenta
    Write-Host "===================" -ForegroundColor Magenta
    
    # Run selective merger
    if ($Interactive) {
        & powershell.exe -ExecutionPolicy Bypass -File "$scriptPath\SelectiveMerger.ps1" -MergeMode "Interactive" -Verbose:$Verbose
    } else {
        & powershell.exe -ExecutionPolicy Bypass -File "$scriptPath\SelectiveMerger.ps1" -MergeMode "Automatic" -DryRun:$DryRun -Verbose:$Verbose
    }
    
    Write-Host "`nPress Enter to continue..." -ForegroundColor Gray
    Read-Host
}

function Generate-ProgressReport {
    Write-Host "`n📈 PROGRESS REPORT" -ForegroundColor Yellow
    Write-Host "==================" -ForegroundColor Yellow
    
    $tracking = Initialize-MigrationTracking
    $reportPath = Generate-MigrationReport $tracking
    
    Write-Host "Report generated: $reportPath" -ForegroundColor Green
    
    # Show quick summary
    Write-Host "`nQuick Summary:" -ForegroundColor Cyan
    Write-Host "  Progress: $($tracking.Metadata.ProgressPercentage.ToString('F1'))%" -ForegroundColor White
    Write-Host "  Migrated: $($tracking.Metadata.MigratedFiles)/$($tracking.Metadata.TotalFiles)" -ForegroundColor White
    Write-Host "  Successful migrations: $($tracking.SuccessfulMigrations.Count)" -ForegroundColor Green
    Write-Host "  Failed attempts: $($tracking.FailedAttempts.Count)" -ForegroundColor Red
    
    Write-Host "`nPress Enter to continue..." -ForegroundColor Gray
    Read-Host
}

function Show-AdvancedOptions {
    Write-Host "`n🔧 ADVANCED OPTIONS" -ForegroundColor Gray
    Write-Host "===================" -ForegroundColor Gray
    
    Write-Host "1. Reset migration status for a file" -ForegroundColor White
    Write-Host "2. Bulk migrate multiple files" -ForegroundColor White
    Write-Host "3. Export migration data" -ForegroundColor White
    Write-Host "4. Clean up temporary files" -ForegroundColor White
    Write-Host "5. Return to main menu" -ForegroundColor White
    
    Write-Host "`nChoice (1-5): " -ForegroundColor Yellow -NoNewline
    $choice = Read-Host
    
    switch ($choice) {
        "1" {
            Write-Host "Feature not yet implemented" -ForegroundColor Yellow
        }
        "2" {
            Write-Host "Feature not yet implemented" -ForegroundColor Yellow
        }
        "3" {
            $tracking = Initialize-MigrationTracking
            $tracking | ConvertTo-Json -Depth 10 | Out-File "migration_export_$(Get-Date -Format 'yyyyMMdd_HHmmss').json"
            Write-Host "Migration data exported" -ForegroundColor Green
        }
        "4" {
            Get-ChildItem -Path "temp_*" -ErrorAction SilentlyContinue | Remove-Item -Force
            Write-Host "Temporary files cleaned" -ForegroundColor Green
        }
        "5" {
            return
        }
    }
    
    Write-Host "`nPress Enter to continue..." -ForegroundColor Gray
    Read-Host
}

# Main execution logic
switch ($Action.ToLower()) {
    "status" {
        Show-MigrationStatus
    }
    
    "initialize" {
        Write-Host "Initializing migration system..." -ForegroundColor Cyan
        $tracking = Initialize-MigrationTracking
        Write-Host "✅ Migration system initialized" -ForegroundColor Green
    }
    
    "migrate" {
        if ($Interactive) {
            Migrate-NextFile $Strategy
        } else {
            Write-Host "Non-interactive migration - specify file with -SpecificFile parameter" -ForegroundColor Yellow
        }
    }
    
    "verify" {
        Verify-MigratedFiles
    }
    
    "merge" {
        Merge-ReadyFiles
    }
    
    "menu" {
        do {
            $choice = Show-MigrationMenu
            
            switch ($choice) {
                "1" { Show-MigrationStatus }
                "2" { Migrate-NextFile $Strategy }
                "3" { Migrate-SpecificFile }
                "4" { Verify-MigratedFiles }
                "5" { Merge-ReadyFiles }
                "6" { Generate-ProgressReport }
                "7" { Show-AdvancedOptions }
                "8" { 
                    Write-Host "👋 Migration system stopped" -ForegroundColor Green
                    return
                }
                default {
                    Write-Host "❌ Invalid choice. Please select 1-8." -ForegroundColor Red
                    Start-Sleep -Seconds 2
                }
            }
        } while ($true)
    }
    
    default {
        Write-Host @"
Mathlib Migration Orchestrator

Usage:
  .\MigrationOrchestrator.ps1 [-Action <action>] [-Strategy <strategy>] [-Interactive] [-DryRun] [-Verbose]

Actions:
  Status      - Show current migration status
  Initialize  - Initialize migration tracking
  Migrate     - Migrate next file or show menu
  Verify      - Verify all migrated files
  Merge       - Merge verified files to main
  Menu        - Show interactive menu (default)

Strategies:
  Simple      - Migrate simplest files first
  Progressive - Migrate by complexity (recommended)
  Advanced    - Migrate using advanced features

Examples:
  .\MigrationOrchestrator.ps1 -Action Menu
  .\MigrationOrchestrator.ps1 -Action Status
  .\MigrationOrchestrator.ps1 -Action Migrate -Strategy Progressive -Interactive
"@ -ForegroundColor Cyan
    }
}