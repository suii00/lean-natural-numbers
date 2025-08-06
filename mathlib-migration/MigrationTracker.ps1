# Mathlib Migration Tracking System
# Tracks progress of gradual migration from standard Lean to Mathlib

param(
    [string]$ProjectPath = ".",
    [string]$TrackingFile = "mathlib-migration\migration_status.json",
    [switch]$UpdateStatus,
    [switch]$GenerateReport
)

# Migration status structure
$migrationSchema = @{
    Metadata = @{
        Version = "1.0"
        StartDate = Get-Date -Format "yyyy-MM-dd"
        LastUpdate = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        TotalFiles = 0
        MigratedFiles = 0
        ProgressPercentage = 0.0
    }
    
    Files = @()  # Array of file migration status
    
    MigrationPhases = @{
        "Phase1_BasicSetup" = @{
            Description = "Initial Mathlib setup and configuration"
            Status = "InProgress"
            Tasks = @(
                @{ Name = "Update lakefile.lean"; Completed = $true },
                @{ Name = "Configure Mathlib dependency"; Completed = $true },
                @{ Name = "Build Mathlib cache"; Completed = $false },
                @{ Name = "Verify basic imports"; Completed = $false }
            )
        }
        "Phase2_CoreProofs" = @{
            Description = "Migrate core proof files"
            Status = "Pending"
            Tasks = @()
        }
        "Phase3_AdvancedFeatures" = @{
            Description = "Migrate advanced features using Mathlib tactics"
            Status = "Pending"
            Tasks = @()
        }
        "Phase4_Integration" = @{
            Description = "Full integration and optimization"
            Status = "Pending"  
            Tasks = @()
        }
    }
    
    SuccessfulMigrations = @()
    FailedAttempts = @()
    PendingFiles = @()
}

function Initialize-MigrationTracking {
    Write-Host "Initializing migration tracking system..." -ForegroundColor Cyan
    
    # Create migration directory
    if (!(Test-Path "mathlib-migration")) {
        New-Item -ItemType Directory -Path "mathlib-migration" -Force | Out-Null
    }
    
    # Load or create tracking file
    if (Test-Path $TrackingFile) {
        $tracking = Get-Content $TrackingFile | ConvertFrom-Json -AsHashtable
        Write-Host "Loaded existing migration tracking data" -ForegroundColor Green
    } else {
        $tracking = $migrationSchema.Clone()
        Write-Host "Created new migration tracking database" -ForegroundColor Yellow
    }
    
    # Scan project for Lean files
    $leanFiles = Get-ChildItem -Path $ProjectPath -Filter "*.lean" -Recurse | Where-Object {
        $_.FullName -notmatch "\.lake|build|mathlib-migration|temp_|test_"
    }
    
    Write-Host "Found $($leanFiles.Count) Lean files in project" -ForegroundColor Gray
    
    # Update file list
    foreach ($file in $leanFiles) {
        $relativePath = $file.FullName.Replace("$ProjectPath\", "").Replace("\", "/")
        
        # Check if file already tracked
        $existingEntry = $tracking.Files | Where-Object { $_.Path -eq $relativePath }
        
        if (!$existingEntry) {
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
            
            # Analyze file for imports
            $content = Get-Content $file.FullName -ErrorAction SilentlyContinue
            if ($content) {
                $imports = $content | Where-Object { $_ -match '^import\s+' }
                $fileEntry.OriginalImports = $imports
                
                # Check if already using Mathlib
                if ($imports -match 'Mathlib') {
                    $fileEntry.Status = "PartiallyMigrated"
                    $fileEntry.MathlibImports = $imports | Where-Object { $_ -match 'Mathlib' }
                }
            }
            
            $tracking.Files += $fileEntry
        }
    }
    
    # Update metadata
    $tracking.Metadata.TotalFiles = $tracking.Files.Count
    $tracking.Metadata.MigratedFiles = ($tracking.Files | Where-Object { 
        $_.Status -in @("Migrated", "Verified") 
    }).Count
    $tracking.Metadata.ProgressPercentage = if ($tracking.Metadata.TotalFiles -gt 0) {
        ($tracking.Metadata.MigratedFiles / $tracking.Metadata.TotalFiles) * 100
    } else { 0 }
    
    $tracking.Metadata.LastUpdate = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    
    # Save tracking data
    $tracking | ConvertTo-Json -Depth 10 | Out-File -FilePath $TrackingFile -Encoding UTF8
    
    return $tracking
}

function Get-MigrationStatus {
    param([hashtable]$Tracking)
    
    Write-Host "`nMigration Status Overview" -ForegroundColor Cyan
    Write-Host "=========================" -ForegroundColor Cyan
    
    # Overall progress
    Write-Host "`nOverall Progress:" -ForegroundColor Yellow
    Write-Host "  Total Files: $($Tracking.Metadata.TotalFiles)" -ForegroundColor White
    Write-Host "  Migrated: $($Tracking.Metadata.MigratedFiles)" -ForegroundColor Green
    Write-Host "  Progress: $($Tracking.Metadata.ProgressPercentage.ToString('F1'))%" -ForegroundColor $(
        if ($Tracking.Metadata.ProgressPercentage -ge 75) { 'Green' }
        elseif ($Tracking.Metadata.ProgressPercentage -ge 50) { 'Yellow' }
        else { 'Red' }
    )
    
    # File status breakdown
    $statusGroups = $Tracking.Files | Group-Object Status
    Write-Host "`nFile Status Breakdown:" -ForegroundColor Yellow
    foreach ($group in $statusGroups) {
        $color = switch ($group.Name) {
            "Migrated" { "Green" }
            "Verified" { "Green" }
            "PartiallyMigrated" { "Yellow" }
            "InProgress" { "Cyan" }
            "Failed" { "Red" }
            default { "Gray" }
        }
        Write-Host "  $($group.Name): $($group.Count)" -ForegroundColor $color
    }
    
    # Phase status
    Write-Host "`nMigration Phases:" -ForegroundColor Yellow
    foreach ($phaseName in $Tracking.MigrationPhases.Keys) {
        $phase = $Tracking.MigrationPhases[$phaseName]
        $completedTasks = ($phase.Tasks | Where-Object { $_.Completed }).Count
        $totalTasks = $phase.Tasks.Count
        
        $statusColor = switch ($phase.Status) {
            "Completed" { "Green" }
            "InProgress" { "Cyan" }
            "Failed" { "Red" }
            default { "Gray" }
        }
        
        Write-Host "  $phaseName`: $($phase.Status)" -ForegroundColor $statusColor
        if ($totalTasks -gt 0) {
            Write-Host "    Tasks: $completedTasks/$totalTasks completed" -ForegroundColor Gray
        }
    }
    
    # Recent activity
    if ($Tracking.SuccessfulMigrations.Count -gt 0) {
        Write-Host "`nRecent Successful Migrations:" -ForegroundColor Green
        $Tracking.SuccessfulMigrations | Select-Object -Last 3 | ForEach-Object {
            Write-Host "  - $($_.FileName) ($($_.MigrationDate))" -ForegroundColor White
        }
    }
    
    if ($Tracking.FailedAttempts.Count -gt 0) {
        Write-Host "`nRecent Failed Attempts:" -ForegroundColor Red
        $Tracking.FailedAttempts | Select-Object -Last 3 | ForEach-Object {
            Write-Host "  - $($_.FileName): $($_.Reason)" -ForegroundColor Red
        }
    }
}

function Update-FileMigrationStatus {
    param(
        [hashtable]$Tracking,
        [string]$FilePath,
        [string]$NewStatus,
        [string]$Notes = ""
    )
    
    $fileEntry = $Tracking.Files | Where-Object { $_.Path -eq $FilePath }
    
    if ($fileEntry) {
        $oldStatus = $fileEntry.Status
        $fileEntry.Status = $NewStatus
        $fileEntry.Notes = $Notes
        
        if ($NewStatus -in @("Migrated", "Verified")) {
            $fileEntry.MigrationDate = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
            
            # Add to successful migrations
            $Tracking.SuccessfulMigrations += @{
                FileName = $fileEntry.Name
                FilePath = $fileEntry.Path
                MigrationDate = $fileEntry.MigrationDate
                OldStatus = $oldStatus
            }
        } elseif ($NewStatus -eq "Failed") {
            # Add to failed attempts
            $Tracking.FailedAttempts += @{
                FileName = $fileEntry.Name
                FilePath = $fileEntry.Path
                AttemptDate = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
                Reason = $Notes
            }
        }
        
        # Update metadata
        $Tracking.Metadata.MigratedFiles = ($Tracking.Files | Where-Object { 
            $_.Status -in @("Migrated", "Verified") 
        }).Count
        $Tracking.Metadata.ProgressPercentage = if ($Tracking.Metadata.TotalFiles -gt 0) {
            ($Tracking.Metadata.MigratedFiles / $Tracking.Metadata.TotalFiles) * 100
        } else { 0 }
        
        Write-Host "Updated $($fileEntry.Name): $oldStatus -> $NewStatus" -ForegroundColor Green
        
        return $true
    } else {
        Write-Host "File not found in tracking: $FilePath" -ForegroundColor Red
        return $false
    }
}

function Get-NextMigrationTarget {
    param([hashtable]$Tracking, [string]$Strategy = "Simple")
    
    $candidates = $Tracking.Files | Where-Object { 
        $_.Status -in @("NotStarted", "PartiallyMigrated") 
    }
    
    if ($candidates.Count -eq 0) {
        Write-Host "No more files to migrate!" -ForegroundColor Green
        return $null
    }
    
    switch ($Strategy) {
        "Simple" {
            # Pick files with no imports first
            $simpleFiles = $candidates | Where-Object { $_.OriginalImports.Count -eq 0 }
            if ($simpleFiles) {
                return $simpleFiles[0]
            }
        }
        
        "Progressive" {
            # Pick files with fewest imports
            $sorted = $candidates | Sort-Object { $_.OriginalImports.Count }
            return $sorted[0]
        }
        
        "Priority" {
            # Pick partially migrated files first
            $partial = $candidates | Where-Object { $_.Status -eq "PartiallyMigrated" }
            if ($partial) {
                return $partial[0]
            }
        }
    }
    
    # Default: return first candidate
    return $candidates[0]
}

function Generate-MigrationReport {
    param([hashtable]$Tracking)
    
    $reportPath = "mathlib-migration\migration_report_$(Get-Date -Format 'yyyyMMdd_HHmmss').md"
    
    $report = @"
# Mathlib Migration Progress Report

**Generated**: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')
**Branch**: mathlib-migration

## Summary

- **Start Date**: $($Tracking.Metadata.StartDate)
- **Total Files**: $($Tracking.Metadata.TotalFiles)
- **Migrated Files**: $($Tracking.Metadata.MigratedFiles)
- **Progress**: $($Tracking.Metadata.ProgressPercentage.ToString('F1'))%

## File Status

| Status | Count | Percentage |
|--------|-------|------------|
"@

    $statusGroups = $Tracking.Files | Group-Object Status
    foreach ($group in $statusGroups) {
        $percentage = ($group.Count / $Tracking.Metadata.TotalFiles * 100).ToString('F1')
        $report += "`n| $($group.Name) | $($group.Count) | $percentage% |"
    }
    
    $report += @"

## Migration Phases

"@

    foreach ($phaseName in $Tracking.MigrationPhases.Keys) {
        $phase = $Tracking.MigrationPhases[$phaseName]
        $completedTasks = ($phase.Tasks | Where-Object { $_.Completed }).Count
        $totalTasks = $phase.Tasks.Count
        
        $report += @"

### $phaseName
- **Status**: $($phase.Status)
- **Description**: $($phase.Description)
"@
        if ($totalTasks -gt 0) {
            $report += "`n- **Progress**: $completedTasks/$totalTasks tasks completed`n"
            
            foreach ($task in $phase.Tasks) {
                $status = if ($task.Completed) { "✅" } else { "⬜" }
                $report += "`n  - $status $($task.Name)"
            }
        }
    }
    
    if ($Tracking.SuccessfulMigrations.Count -gt 0) {
        $report += @"

## Successfully Migrated Files

| File | Migration Date |
|------|---------------|
"@
        $Tracking.SuccessfulMigrations | ForEach-Object {
            $report += "`n| $($_.FileName) | $($_.MigrationDate) |"
        }
    }
    
    if ($Tracking.FailedAttempts.Count -gt 0) {
        $report += @"

## Failed Migration Attempts

| File | Attempt Date | Reason |
|------|--------------|--------|
"@
        $Tracking.FailedAttempts | ForEach-Object {
            $report += "`n| $($_.FileName) | $($_.AttemptDate) | $($_.Reason) |"
        }
    }
    
    $report += @"

## Next Steps

1. Review failed migrations and address issues
2. Continue with pending files
3. Verify migrated files compile correctly
4. Run comprehensive tests
5. Merge successful migrations to main branch

---
*Report generated by Mathlib Migration Tracker*
"@

    [System.IO.File]::WriteAllText($reportPath, $report)
    Write-Host "Report generated: $reportPath" -ForegroundColor Green
    
    return $reportPath
}

# Main execution
$tracking = Initialize-MigrationTracking

if ($UpdateStatus) {
    Get-MigrationStatus $tracking
}

if ($GenerateReport) {
    $reportPath = Generate-MigrationReport $tracking
    Write-Host "`nMigration report saved to: $reportPath" -ForegroundColor Green
}

# Export functions for use by other scripts
Export-ModuleMember -Function Initialize-MigrationTracking, Get-MigrationStatus, Update-FileMigrationStatus, Get-NextMigrationTarget, Generate-MigrationReport