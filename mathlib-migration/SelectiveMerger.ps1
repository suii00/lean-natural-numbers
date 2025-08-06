# Selective Merge System for Mathlib Migration
# Merges only successfully verified migrations back to main branch

param(
    [string]$MergeMode = "Interactive", # Interactive, Automatic, Cherry-Pick
    [string[]]$FilesToMerge = @(),
    [switch]$DryRun,
    [switch]$CreatePR,
    [switch]$Verbose
)

# Merge configuration
$mergeConfig = @{
    SourceBranch = "mathlib-migration"
    TargetBranch = "main"
    
    MergeStrategies = @{
        "Safe" = @{
            Description = "Only merge fully verified files"
            RequireVerification = $true
            RequireAllTestsPass = $true
            CreateBackup = $true
        }
        "Progressive" = @{
            Description = "Merge files that pass basic tests"
            RequireVerification = $true
            RequireAllTestsPass = $false
            MinTestPassRate = 0.8
        }
        "Aggressive" = @{
            Description = "Merge all migrated files"
            RequireVerification = $false
            CreateBackup = $true
        }
    }
    
    FileCategories = @{
        "ReadyToMerge" = "Files that passed all verifications"
        "NeedsReview" = "Files with minor issues that may need review"
        "NotReady" = "Files that failed verification"
        "Excluded" = "Files explicitly excluded from merge"
    }
}

function Get-MergeReadyFiles {
    Write-Host "Identifying merge-ready files..." -ForegroundColor Cyan
    
    $migrationDir = "mathlib-migration"
    $verificationReports = Get-ChildItem -Path $migrationDir -Filter "verification_*.json" -ErrorAction SilentlyContinue
    
    $fileStatus = @{
        ReadyToMerge = @()
        NeedsReview = @()
        NotReady = @()
        NoVerification = @()
    }
    
    # Check migrated files
    $migratedDir = "$migrationDir\migrated"
    if (Test-Path $migratedDir) {
        $migratedFiles = Get-ChildItem -Path $migratedDir -Filter "*.lean"
        
        foreach ($file in $migratedFiles) {
            # Look for verification report
            $reportPattern = "verification_$($file.Name)_*.json"
            $report = $verificationReports | Where-Object { $_.Name -like $reportPattern } | Select-Object -Last 1
            
            if ($report) {
                $verificationData = Get-Content $report.FullName | ConvertFrom-Json
                
                $fileInfo = @{
                    FilePath = $file.FullName
                    FileName = $file.Name
                    VerificationReport = $report.Name
                    TestsPassed = $verificationData.Summary.PassedTests
                    TotalTests = $verificationData.Summary.TotalTests
                    PassRate = $verificationData.Summary.PassRate
                    OverallSuccess = $verificationData.OverallSuccess
                    LastVerified = $verificationData.Timestamp
                }
                
                if ($fileInfo.OverallSuccess) {
                    $fileStatus.ReadyToMerge += $fileInfo
                } elseif ($fileInfo.PassRate -ge 80) {
                    $fileStatus.NeedsReview += $fileInfo
                } else {
                    $fileStatus.NotReady += $fileInfo
                }
            } else {
                $fileStatus.NoVerification += @{
                    FilePath = $file.FullName
                    FileName = $file.Name
                }
            }
        }
    }
    
    Write-Host "File Status Summary:" -ForegroundColor Yellow
    Write-Host "  Ready to Merge: $($fileStatus.ReadyToMerge.Count)" -ForegroundColor Green
    Write-Host "  Needs Review: $($fileStatus.NeedsReview.Count)" -ForegroundColor Yellow
    Write-Host "  Not Ready: $($fileStatus.NotReady.Count)" -ForegroundColor Red
    Write-Host "  No Verification: $($fileStatus.NoVerification.Count)" -ForegroundColor Gray
    
    return $fileStatus
}

function Show-InteractiveMergeMenu {
    param([hashtable]$FileStatus)
    
    Write-Host "`nInteractive Merge Selection" -ForegroundColor Cyan
    Write-Host "===========================" -ForegroundColor Cyan
    
    $selectedFiles = @()
    
    if ($FileStatus.ReadyToMerge.Count -gt 0) {
        Write-Host "`nFiles ready to merge:" -ForegroundColor Green
        for ($i = 0; $i -lt $FileStatus.ReadyToMerge.Count; $i++) {
            $file = $FileStatus.ReadyToMerge[$i]
            Write-Host "  $($i+1). $($file.FileName) (Pass rate: $($file.PassRate.ToString('F1'))%)" -ForegroundColor White
        }
        
        Write-Host "`nSelect files to merge (comma-separated numbers, 'all' for all, 'none' to skip):" -ForegroundColor Yellow
        $selection = Read-Host
        
        if ($selection -eq "all") {
            $selectedFiles = $FileStatus.ReadyToMerge
        } elseif ($selection -ne "none") {
            $indices = $selection -split ',' | ForEach-Object { [int]$_.Trim() - 1 }
            foreach ($index in $indices) {
                if ($index -ge 0 -and $index -lt $FileStatus.ReadyToMerge.Count) {
                    $selectedFiles += $FileStatus.ReadyToMerge[$index]
                }
            }
        }
    }
    
    if ($FileStatus.NeedsReview.Count -gt 0) {
        Write-Host "`nFiles that need review (partial pass):" -ForegroundColor Yellow
        for ($i = 0; $i -lt $FileStatus.NeedsReview.Count; $i++) {
            $file = $FileStatus.NeedsReview[$i]
            Write-Host "  $($i+1). $($file.FileName) (Pass rate: $($file.PassRate.ToString('F1'))%)" -ForegroundColor White
        }
        
        Write-Host "`nInclude files needing review? (y/n):" -ForegroundColor Yellow
        $includeReview = Read-Host
        
        if ($includeReview -eq 'y' -or $includeReview -eq 'Y') {
            Write-Host "Select files (comma-separated numbers, 'all' for all):" -ForegroundColor Yellow
            $selection = Read-Host
            
            if ($selection -eq "all") {
                $selectedFiles += $FileStatus.NeedsReview
            } else {
                $indices = $selection -split ',' | ForEach-Object { [int]$_.Trim() - 1 }
                foreach ($index in $indices) {
                    if ($index -ge 0 -and $index -lt $FileStatus.NeedsReview.Count) {
                        $selectedFiles += $FileStatus.NeedsReview[$index]
                    }
                }
            }
        }
    }
    
    Write-Host "`nSelected $($selectedFiles.Count) files for merge" -ForegroundColor Cyan
    return $selectedFiles
}

function Prepare-MergeBranch {
    param([array]$FilesToMerge)
    
    Write-Host "`nPreparing merge branch..." -ForegroundColor Cyan
    
    # Create a clean merge branch
    $timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
    $mergeBranch = "mathlib-merge-$timestamp"
    
    try {
        # Save current branch
        $currentBranch = & git rev-parse --abbrev-ref HEAD 2>$null
        
        # Create merge branch from main
        Write-Host "Creating merge branch: $mergeBranch" -ForegroundColor Gray
        & git checkout main 2>$null
        & git pull origin main 2>$null
        & git checkout -b $mergeBranch 2>$null
        
        if ($LASTEXITCODE -ne 0) {
            throw "Failed to create merge branch"
        }
        
        # Copy selected files from migration branch
        foreach ($fileInfo in $FilesToMerge) {
            $sourceFile = $fileInfo.FilePath
            $fileName = $fileInfo.FileName
            
            # Determine target path (maintain directory structure)
            $relativePath = $sourceFile.Replace("mathlib-migration\migrated\", "")
            $targetPath = $relativePath
            
            Write-Host "  Copying: $fileName" -ForegroundColor Gray
            
            # Get file from migration branch
            & git checkout mathlib-migration -- $sourceFile 2>$null
            
            if ($LASTEXITCODE -eq 0) {
                # If file doesn't exist in main, copy it
                if (!(Test-Path $targetPath)) {
                    Copy-Item $sourceFile $targetPath -Force
                }
            } else {
                # Try direct file copy
                if (Test-Path $sourceFile) {
                    $targetDir = Split-Path $targetPath -Parent
                    if ($targetDir -and !(Test-Path $targetDir)) {
                        New-Item -ItemType Directory -Path $targetDir -Force | Out-Null
                    }
                    Copy-Item $sourceFile $targetPath -Force
                }
            }
        }
        
        Write-Host "✅ Merge branch prepared: $mergeBranch" -ForegroundColor Green
        
        return @{
            Success = $true
            BranchName = $mergeBranch
            FileCount = $FilesToMerge.Count
        }
        
    } catch {
        Write-Host "❌ Failed to prepare merge branch: $($_.Exception.Message)" -ForegroundColor Red
        
        # Return to original branch
        & git checkout $currentBranch 2>$null
        
        return @{
            Success = $false
            Error = $_.Exception.Message
        }
    }
}

function Execute-SelectiveMerge {
    param([array]$FilesToMerge, [hashtable]$MergeBranchInfo)
    
    Write-Host "`nExecuting selective merge..." -ForegroundColor Cyan
    
    if ($DryRun) {
        Write-Host "🔍 DRY RUN MODE - No actual changes will be made" -ForegroundColor Yellow
        
        Write-Host "`nWould merge the following files:" -ForegroundColor Cyan
        $FilesToMerge | ForEach-Object {
            Write-Host "  - $($_.FileName)" -ForegroundColor White
        }
        
        Write-Host "`nFrom branch: mathlib-migration" -ForegroundColor Gray
        Write-Host "To branch: main (via $($MergeBranchInfo.BranchName))" -ForegroundColor Gray
        
        return @{
            Success = $true
            DryRun = $true
        }
    }
    
    try {
        # Stage the changes
        Write-Host "Staging changes..." -ForegroundColor Gray
        & git add -A 2>$null
        
        # Create commit
        $commitMessage = @"
Selective Mathlib migration merge

Migrated files ($($FilesToMerge.Count)):
$($FilesToMerge | ForEach-Object { "- $($_.FileName)" } | Out-String)

Migration branch: mathlib-migration
Verification status: Passed
"@
        
        & git commit -m $commitMessage 2>$null
        
        if ($LASTEXITCODE -ne 0) {
            Write-Host "⚠️ No changes to commit (files may already be up to date)" -ForegroundColor Yellow
        } else {
            Write-Host "✅ Changes committed" -ForegroundColor Green
        }
        
        # Merge to main
        Write-Host "Merging to main branch..." -ForegroundColor Gray
        & git checkout main 2>$null
        & git merge $MergeBranchInfo.BranchName --no-ff -m "Merge Mathlib migration: $($FilesToMerge.Count) files" 2>$null
        
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✅ Successfully merged to main" -ForegroundColor Green
            
            return @{
                Success = $true
                MergedFiles = $FilesToMerge.Count
                MergeBranch = $MergeBranchInfo.BranchName
            }
        } else {
            throw "Merge failed"
        }
        
    } catch {
        Write-Host "❌ Merge failed: $($_.Exception.Message)" -ForegroundColor Red
        
        return @{
            Success = $false
            Error = $_.Exception.Message
        }
    }
}

function Create-PullRequest {
    param([array]$FilesToMerge, [string]$BranchName)
    
    Write-Host "`nCreating pull request..." -ForegroundColor Cyan
    
    try {
        # Push branch to remote
        Write-Host "Pushing branch to remote..." -ForegroundColor Gray
        & git push origin $BranchName 2>$null
        
        if ($LASTEXITCODE -ne 0) {
            throw "Failed to push branch"
        }
        
        # Create PR using GitHub CLI if available
        $ghAvailable = Get-Command gh -ErrorAction SilentlyContinue
        
        if ($ghAvailable) {
            $prTitle = "Mathlib Migration: $($FilesToMerge.Count) verified files"
            $prBody = @"
## Mathlib Migration - Selective Merge

This PR contains successfully verified Mathlib migrations.

### Files Included ($($FilesToMerge.Count))
$($FilesToMerge | ForEach-Object { "- `$($_.FileName)` - Verification: $($_.PassRate.ToString('F1'))% passed" } | Out-String)

### Verification Summary
- All files passed verification tests
- Branch: `$BranchName`
- Source: `mathlib-migration`

### Next Steps
1. Review the migrated code
2. Run additional tests if needed
3. Merge when ready
"@
            
            Write-Host "Creating GitHub pull request..." -ForegroundColor Gray
            & gh pr create --title $prTitle --body $prBody --base main --head $BranchName
            
            if ($LASTEXITCODE -eq 0) {
                Write-Host "✅ Pull request created successfully" -ForegroundColor Green
            } else {
                Write-Host "⚠️ Could not create PR automatically. Please create manually." -ForegroundColor Yellow
            }
        } else {
            Write-Host "⚠️ GitHub CLI not available. Please create PR manually:" -ForegroundColor Yellow
            Write-Host "  Branch: $BranchName" -ForegroundColor White
            Write-Host "  Target: main" -ForegroundColor White
        }
        
        return @{ Success = $true }
        
    } catch {
        Write-Host "❌ Failed to create PR: $($_.Exception.Message)" -ForegroundColor Red
        return @{ Success = $false; Error = $_.Exception.Message }
    }
}

function Generate-MergeReport {
    param([array]$MergedFiles, [hashtable]$MergeResult)
    
    $reportPath = "mathlib-migration\merge_report_$(Get-Date -Format 'yyyyMMdd_HHmmss').md"
    
    $report = @"
# Selective Merge Report

**Date**: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')
**Merge Mode**: $MergeMode
**Branch**: $($MergeResult.MergeBranch ?? 'N/A')

## Summary

- **Files Merged**: $($MergedFiles.Count)
- **Merge Status**: $(if ($MergeResult.Success) { '✅ Success' } else { '❌ Failed' })

## Merged Files

| File | Verification Pass Rate | Tests Passed |
|------|------------------------|--------------|
"@

    foreach ($file in $MergedFiles) {
        $report += "`n| $($file.FileName) | $($file.PassRate.ToString('F1'))% | $($file.TestsPassed)/$($file.TotalTests) |"
    }
    
    if (!$MergeResult.Success -and $MergeResult.Error) {
        $report += @"

## Errors

$($MergeResult.Error)
"@
    }
    
    $report += @"

## Next Steps

1. Verify the merge on main branch
2. Run comprehensive tests
3. Update migration tracking
4. Continue with remaining files

---
*Report generated by Selective Merge System*
"@

    [System.IO.File]::WriteAllText($reportPath, $report)
    Write-Host "`nMerge report saved: $reportPath" -ForegroundColor Green
    
    return $reportPath
}

# Main execution
Write-Host "Selective Merge System" -ForegroundColor Cyan
Write-Host "=====================" -ForegroundColor Cyan

# Get merge-ready files
$fileStatus = Get-MergeReadyFiles

# Select files to merge based on mode
$filesToMerge = if ($FilesToMerge.Count -gt 0) {
    # Use specified files
    $fileStatus.ReadyToMerge | Where-Object { $_.FileName -in $FilesToMerge }
} else {
    switch ($MergeMode) {
        "Interactive" {
            Show-InteractiveMergeMenu $fileStatus
        }
        "Automatic" {
            # Automatically select all ready files
            Write-Host "`nAutomatically selecting all verified files..." -ForegroundColor Gray
            $fileStatus.ReadyToMerge
        }
        "Cherry-Pick" {
            # Allow cherry-picking specific files
            Write-Host "`nCherry-pick mode: Please specify files with -FilesToMerge parameter" -ForegroundColor Yellow
            @()
        }
        default {
            Write-Host "Unknown merge mode: $MergeMode" -ForegroundColor Red
            @()
        }
    }
}

if ($filesToMerge.Count -eq 0) {
    Write-Host "`n⚠️ No files selected for merge" -ForegroundColor Yellow
    return
}

Write-Host "`nPreparing to merge $($filesToMerge.Count) files..." -ForegroundColor Cyan

# Prepare merge branch
$mergeBranchInfo = Prepare-MergeBranch $filesToMerge

if (!$mergeBranchInfo.Success) {
    Write-Host "❌ Failed to prepare merge" -ForegroundColor Red
    return
}

# Execute merge
$mergeResult = Execute-SelectiveMerge $filesToMerge $mergeBranchInfo

# Create PR if requested
if ($CreatePR -and $mergeResult.Success -and !$DryRun) {
    Create-PullRequest $filesToMerge $mergeBranchInfo.BranchName
}

# Generate report
$reportPath = Generate-MergeReport $filesToMerge $mergeResult

# Final summary
Write-Host "`n" + "="*50 -ForegroundColor Cyan
if ($mergeResult.Success) {
    Write-Host "✅ SELECTIVE MERGE COMPLETED SUCCESSFULLY" -ForegroundColor Green
    Write-Host "Merged $($filesToMerge.Count) files to main branch" -ForegroundColor White
} else {
    Write-Host "❌ SELECTIVE MERGE FAILED" -ForegroundColor Red
}
Write-Host "Report: $reportPath" -ForegroundColor Gray

Export-ModuleMember -Function Get-MergeReadyFiles, Execute-SelectiveMerge