# Branch Management System for Mathlib Migration Recovery
# Handles branch creation, isolation, merging, and cleanup for recovery operations

param(
    [string]$BaseBranch = "main",
    [string]$RecoveryNamespace = "recovery",
    [int]$MaxBranches = 20,
    [switch]$CleanupOldBranches,
    [switch]$Verbose
)

# Branch management configuration
$branchConfig = @{
    BranchTypes = @{
        "safety" = @{
            Prefix = "safety"
            Description = "Emergency backup branches before risky operations"
            Retention = 7  # days
            AutoCleanup = $false
        }
        "recovery" = @{
            Prefix = "recovery"
            Description = "Active recovery attempt branches"
            Retention = 3  # days
            AutoCleanup = $true
        }
        "isolation" = @{
            Prefix = "isolation"
            Description = "Branches with isolated problematic components"
            Retention = 5  # days
            AutoCleanup = $false
        }
        "test" = @{
            Prefix = "test"
            Description = "Temporary testing branches for validation"
            Retention = 1  # days
            AutoCleanup = $true
        }
        "milestone" = @{
            Prefix = "milestone"
            Description = "Stable milestone branches for progress tracking"
            Retention = 30  # days
            AutoCleanup = $false
        }
    }
    
    NamingConventions = @{
        DateFormat = "yyyyMMdd_HHmmss"
        MaxNameLength = 50
        InvalidCharacters = @(' ', '~', '^', ':', '?', '*', '[', '\')
        ReservedNames = @("HEAD", "master", "main", "develop")
    }
    
    MergeStrategies = @{
        "safe" = @{
            Strategy = "merge"
            Options = @("--no-ff", "--strategy=ours")
            RequireCleanWorkingTree = $true
        }
        "recovery" = @{
            Strategy = "merge"  
            Options = @("--no-ff")
            RequireCleanWorkingTree = $false
        }
        "squash" = @{
            Strategy = "merge"
            Options = @("--squash")
            RequireCleanWorkingTree = $true
        }
    }
}

function Get-GitRepositoryStatus {
    Write-Host "🔍 Checking Git repository status..." -ForegroundColor Cyan
    
    try {
        # Check if we're in a git repository
        $gitDir = & git rev-parse --git-dir 2>$null
        if ($LASTEXITCODE -ne 0) {
            throw "Not a git repository"
        }
        
        $status = @{
            IsGitRepo = $true
            CurrentBranch = & git rev-parse --abbrev-ref HEAD 2>$null
            CurrentCommit = & git rev-parse HEAD 2>$null
            HasUncommittedChanges = $false
            UntrackedFiles = @()
            ModifiedFiles = @()
            StagedFiles = @()
            RemoteTracking = $null
        }
        
        # Check working tree status
        $gitStatus = & git status --porcelain 2>$null
        if ($gitStatus) {
            $status.HasUncommittedChanges = $true
            
            foreach ($line in $gitStatus) {
                $statusCode = $line.Substring(0, 2)
                $fileName = $line.Substring(3)
                
                if ($statusCode -match '^\?\?') {
                    $status.UntrackedFiles += $fileName
                } elseif ($statusCode -match '^.[MD]') {
                    $status.ModifiedFiles += $fileName
                } elseif ($statusCode -match '^[AMD]') {
                    $status.StagedFiles += $fileName
                }
            }
        }
        
        # Check remote tracking
        try {
            $remoteRef = & git rev-parse --abbrev-ref "@{upstream}" 2>$null
            if ($LASTEXITCODE -eq 0) {
                $status.RemoteTracking = $remoteRef
            }
        } catch { }
        
        if ($Verbose) {
            Write-Host "📍 Current branch: $($status.CurrentBranch)" -ForegroundColor Gray
            Write-Host "📍 Current commit: $($status.CurrentCommit.Substring(0,8))" -ForegroundColor Gray
            Write-Host "📍 Uncommitted changes: $($status.HasUncommittedChanges)" -ForegroundColor $(if($status.HasUncommittedChanges) {'Yellow'} else {'Green'})
            Write-Host "📍 Remote tracking: $($status.RemoteTracking ?? 'None')" -ForegroundColor Gray
        }
        
        return $status
        
    } catch {
        return @{
            IsGitRepo = $false
            Error = $_.Exception.Message
        }
    }
}

function Generate-BranchName {
    param([string]$BranchType, [string]$Purpose = "", [string]$BaseName = "")
    
    $branchInfo = $branchConfig.BranchTypes[$BranchType]
    if (!$branchInfo) {
        throw "Unknown branch type: $BranchType"
    }
    
    $timestamp = Get-Date -Format $branchConfig.NamingConventions.DateFormat
    $prefix = $branchInfo.Prefix
    
    # Build branch name components
    $components = @($prefix)
    
    if ($BaseName) {
        # Clean base name
        $cleanBaseName = $BaseName
        foreach ($invalidChar in $branchConfig.NamingConventions.InvalidCharacters) {
            $cleanBaseName = $cleanBaseName -replace [regex]::Escape($invalidChar), '_'
        }
        $components += $cleanBaseName
    }
    
    if ($Purpose) {
        # Clean purpose
        $cleanPurpose = $Purpose -replace '\s+', '_' -replace '[^a-zA-Z0-9_-]', ''
        $components += $cleanPurpose
    }
    
    $components += $timestamp
    
    $branchName = $components -join '_'
    
    # Ensure length limits
    if ($branchName.Length -gt $branchConfig.NamingConventions.MaxNameLength) {
        $branchName = $branchName.Substring(0, $branchConfig.NamingConventions.MaxNameLength)
    }
    
    # Check for reserved names
    if ($branchName -in $branchConfig.NamingConventions.ReservedNames) {
        $branchName = "${branchName}_branch"
    }
    
    return $branchName
}

function Create-SafetyBranch {
    param([string]$Purpose, [string]$SourceBranch = "")
    
    Write-Host "🛡️ Creating safety branch..." -ForegroundColor Cyan
    
    $gitStatus = Get-GitRepositoryStatus
    if (!$gitStatus.IsGitRepo) {
        throw "Not in a git repository: $($gitStatus.Error)"
    }
    
    $sourceBranch = if ($SourceBranch) { $SourceBranch } else { $gitStatus.CurrentBranch }
    $branchName = Generate-BranchName "safety" $Purpose $sourceBranch
    
    try {
        # Commit any uncommitted changes first if needed
        if ($gitStatus.HasUncommittedChanges) {
            Write-Host "💾 Committing uncommitted changes before creating safety branch..." -ForegroundColor Yellow
            
            & git add -A 2>$null
            $commitMessage = "Safety commit before creating branch: $branchName"
            & git commit -m $commitMessage 2>$null
            
            if ($LASTEXITCODE -ne 0) {
                Write-Host "⚠️ Failed to commit changes, creating branch anyway" -ForegroundColor Yellow
            }
        }
        
        # Create the safety branch
        $output = & git checkout -b $branchName 2>&1
        if ($LASTEXITCODE -ne 0) {
            throw "Failed to create branch: $($output -join '; ')"
        }
        
        # Switch back to original branch
        & git checkout $sourceBranch 2>$null
        
        $branchInfo = @{
            Name = $branchName
            Type = "safety"
            Purpose = $Purpose
            SourceBranch = $sourceBranch
            SourceCommit = $gitStatus.CurrentCommit
            Created = Get-Date
            CreatedTimestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        }
        
        Write-Host "✅ Safety branch created: $branchName" -ForegroundColor Green
        return $branchInfo
        
    } catch {
        Write-Host "❌ Failed to create safety branch: $($_.Exception.Message)" -ForegroundColor Red
        throw
    }
}

function Create-RecoveryBranch {
    param([string]$RecoveryType, [string]$AttemptNumber = "1")
    
    Write-Host "🔄 Creating recovery branch..." -ForegroundColor Cyan
    
    $branchName = Generate-BranchName "recovery" $RecoveryType "attempt$AttemptNumber"
    
    try {
        $output = & git checkout -b $branchName 2>&1
        if ($LASTEXITCODE -ne 0) {
            throw "Failed to create recovery branch: $($output -join '; ')"
        }
        
        $branchInfo = @{
            Name = $branchName
            Type = "recovery"
            RecoveryType = $RecoveryType
            AttemptNumber = $AttemptNumber
            Created = Get-Date
            CreatedTimestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        }
        
        Write-Host "✅ Recovery branch created: $branchName" -ForegroundColor Green
        return $branchInfo
        
    } catch {
        Write-Host "❌ Failed to create recovery branch: $($_.Exception.Message)" -ForegroundColor Red
        throw
    }
}

function Create-IsolationBranch {
    param([string]$IsolationType, [array]$IsolatedComponents)
    
    Write-Host "🔬 Creating isolation branch..." -ForegroundColor Cyan
    
    $componentNames = ($IsolatedComponents | ForEach-Object { 
        if ($_.Name) { $_.Name } 
        elseif ($_.Path) { Split-Path $_.Path -Leaf } 
        else { "component" } 
    }) -join "_"
    
    $branchName = Generate-BranchName "isolation" $IsolationType $componentNames
    
    try {
        $output = & git checkout -b $branchName 2>&1
        if ($LASTEXITCODE -ne 0) {
            throw "Failed to create isolation branch: $($output -join '; ')"
        }
        
        $branchInfo = @{
            Name = $branchName
            Type = "isolation"
            IsolationType = $IsolationType
            IsolatedComponents = $IsolatedComponents
            ComponentCount = $IsolatedComponents.Count
            Created = Get-Date
            CreatedTimestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        }
        
        Write-Host "✅ Isolation branch created: $branchName" -ForegroundColor Green
        return $branchInfo
        
    } catch {
        Write-Host "❌ Failed to create isolation branch: $($_.Exception.Message)" -ForegroundColor Red
        throw
    }
}

function Create-MilestoneBranch {
    param([string]$MilestoneName, [string]$Description = "")
    
    Write-Host "🎯 Creating milestone branch..." -ForegroundColor Cyan
    
    $branchName = Generate-BranchName "milestone" $MilestoneName
    
    try {
        $gitStatus = Get-GitRepositoryStatus
        
        # Ensure clean working tree for milestones
        if ($gitStatus.HasUncommittedChanges) {
            Write-Host "💾 Committing changes before creating milestone..." -ForegroundColor Yellow
            
            & git add -A 2>$null
            $commitMessage = "Milestone commit: $MilestoneName"
            & git commit -m $commitMessage 2>$null
        }
        
        $output = & git checkout -b $branchName 2>&1
        if ($LASTEXITCODE -ne 0) {
            throw "Failed to create milestone branch: $($output -join '; ')"
        }
        
        # Add milestone tag
        $tagName = "milestone_$(Get-Date -Format 'yyyyMMdd_HHmmss')"
        & git tag -a $tagName -m "Milestone: $MilestoneName - $Description" 2>$null
        
        # Switch back to original branch
        & git checkout $gitStatus.CurrentBranch 2>$null
        
        $branchInfo = @{
            Name = $branchName
            Type = "milestone"
            MilestoneName = $MilestoneName
            Description = $Description
            TagName = $tagName
            Created = Get-Date
            CreatedTimestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        }
        
        Write-Host "✅ Milestone branch created: $branchName (tagged: $tagName)" -ForegroundColor Green
        return $branchInfo
        
    } catch {
        Write-Host "❌ Failed to create milestone branch: $($_.Exception.Message)" -ForegroundColor Red
        throw
    }
}

function Get-RecoveryBranches {
    param([string]$BranchType = "", [int]$MaxAge = 0)
    
    try {
        $allBranches = & git branch -a --format="%(refname:short) %(committerdate:iso8601)" 2>$null
        if ($LASTEXITCODE -ne 0) {
            return @()
        }
        
        $recoveryBranches = @()
        
        foreach ($branchLine in $allBranches) {
            $parts = $branchLine -split ' ', 2
            $branchName = $parts[0]
            $commitDate = if ($parts.Length -gt 1) { [DateTime]$parts[1] } else { Get-Date }
            
            # Filter by branch type
            $matchesType = if ($BranchType) {
                $branchName -match "^$($branchConfig.BranchTypes[$BranchType].Prefix)_"
            } else {
                $branchConfig.BranchTypes.Keys | ForEach-Object {
                    if ($branchName -match "^$($branchConfig.BranchTypes[$_].Prefix)_") {
                        return $true
                    }
                }
            }
            
            if ($matchesType) {
                $age = (Get-Date) - $commitDate
                
                # Filter by age if specified
                if ($MaxAge -eq 0 -or $age.TotalDays -le $MaxAge) {
                    $recoveryBranches += @{
                        Name = $branchName
                        CommitDate = $commitDate
                        Age = $age
                        AgeInDays = [math]::Round($age.TotalDays, 1)
                        Type = ($branchConfig.BranchTypes.Keys | Where-Object { 
                            $branchName -match "^$($branchConfig.BranchTypes[$_].Prefix)_" 
                        })[0]
                    }
                }
            }
        }
        
        return $recoveryBranches | Sort-Object CommitDate -Descending
        
    } catch {
        Write-Host "❌ Failed to get recovery branches: $($_.Exception.Message)" -ForegroundColor Red
        return @()
    }
}

function Merge-RecoveryBranch {
    param([string]$SourceBranch, [string]$TargetBranch = "", [string]$MergeStrategy = "safe")
    
    Write-Host "🔗 Merging recovery branch..." -ForegroundColor Cyan
    
    $gitStatus = Get-GitRepositoryStatus
    $targetBranch = if ($TargetBranch) { $TargetBranch } else { $gitStatus.CurrentBranch }
    
    $mergeConfig = $branchConfig.MergeStrategies[$MergeStrategy]
    if (!$mergeConfig) {
        throw "Unknown merge strategy: $MergeStrategy"
    }
    
    try {
        # Check merge requirements
        if ($mergeConfig.RequireCleanWorkingTree -and $gitStatus.HasUncommittedChanges) {
            Write-Host "💾 Committing changes before merge..." -ForegroundColor Yellow
            
            & git add -A 2>$null
            & git commit -m "Pre-merge commit: merging $SourceBranch into $targetBranch" 2>$null
        }
        
        # Switch to target branch
        Write-Host "🔄 Switching to target branch: $targetBranch" -ForegroundColor Gray
        & git checkout $targetBranch 2>$null
        if ($LASTEXITCODE -ne 0) {
            throw "Failed to checkout target branch: $targetBranch"
        }
        
        # Perform merge
        $mergeCommand = "git merge $($mergeConfig.Options -join ' ') $SourceBranch"
        Write-Host "⚡ Executing merge: $mergeCommand" -ForegroundColor Gray
        
        $mergeOutput = & git merge $mergeConfig.Options $SourceBranch 2>&1
        $mergeSuccess = $LASTEXITCODE -eq 0
        
        $mergeResult = @{
            Success = $mergeSuccess
            SourceBranch = $SourceBranch
            TargetBranch = $targetBranch
            Strategy = $MergeStrategy
            Output = $mergeOutput -join "`n"
            Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
            MergeCommit = if ($mergeSuccess) { & git rev-parse HEAD } else { "" }
        }
        
        if ($mergeSuccess) {
            Write-Host "✅ Successfully merged $SourceBranch into $targetBranch" -ForegroundColor Green
            
            # Add merge commit message if needed
            if ($mergeConfig.Strategy -eq "merge" -and "--no-ff" -in $mergeConfig.Options) {
                $mergeMessage = "Successful recovery merge: $SourceBranch -> $targetBranch"
                & git commit --amend -m $mergeMessage 2>$null
            }
        } else {
            Write-Host "❌ Merge failed: $($mergeOutput -join '; ')" -ForegroundColor Red
            
            # Check for conflicts
            $conflictFiles = & git diff --name-only --diff-filter=U 2>$null
            if ($conflictFiles) {
                $mergeResult.ConflictFiles = $conflictFiles
                Write-Host "⚠️ Merge conflicts in files:" -ForegroundColor Yellow
                $conflictFiles | ForEach-Object { Write-Host "   $_" -ForegroundColor Red }
            }
        }
        
        return $mergeResult
        
    } catch {
        Write-Host "❌ Failed to merge recovery branch: $($_.Exception.Message)" -ForegroundColor Red
        
        return @{
            Success = $false
            Error = $_.Exception.Message
            SourceBranch = $SourceBranch
            TargetBranch = $targetBranch
            Strategy = $MergeStrategy
            Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        }
    }
}

function Cleanup-OldBranches {
    param([string]$BranchType = "", [switch]$DryRun)
    
    Write-Host "🧹 Cleaning up old recovery branches..." -ForegroundColor Cyan
    
    $branchesToCleanup = @()
    
    # Get branches to consider for cleanup
    $typesToCheck = if ($BranchType) { @($BranchType) } else { $branchConfig.BranchTypes.Keys }
    
    foreach ($type in $typesToCheck) {
        $typeConfig = $branchConfig.BranchTypes[$type]
        
        if ($typeConfig.AutoCleanup) {
            $oldBranches = Get-RecoveryBranches -BranchType $type | 
                           Where-Object { $_.AgeInDays -gt $typeConfig.Retention }
            
            foreach ($branch in $oldBranches) {
                $branchesToCleanup += @{
                    Name = $branch.Name
                    Type = $type
                    Age = $branch.AgeInDays
                    Reason = "Exceeded retention period ($($typeConfig.Retention) days)"
                }
            }
        }
    }
    
    # Check for excess branches
    $allRecoveryBranches = Get-RecoveryBranches
    if ($allRecoveryBranches.Count -gt $MaxBranches) {
        $excessBranches = $allRecoveryBranches | 
                         Sort-Object CommitDate | 
                         Select-Object -First ($allRecoveryBranches.Count - $MaxBranches)
        
        foreach ($branch in $excessBranches) {
            if ($branch.Name -notin ($branchesToCleanup | ForEach-Object { $_.Name })) {
                $branchesToCleanup += @{
                    Name = $branch.Name
                    Type = $branch.Type
                    Age = $branch.AgeInDays
                    Reason = "Exceeds maximum branch limit ($MaxBranches)"
                }
            }
        }
    }
    
    Write-Host "📊 Found $($branchesToCleanup.Count) branches for cleanup" -ForegroundColor Yellow
    
    if ($DryRun) {
        Write-Host "🔍 DRY RUN - Would delete:" -ForegroundColor Cyan
        $branchesToCleanup | ForEach-Object {
            Write-Host "   $($_.Name) ($($_.Age.ToString('F1')) days old) - $($_.Reason)" -ForegroundColor Gray
        }
        return $branchesToCleanup
    }
    
    $cleanupResults = @{
        Deleted = @()
        Failed = @()
        Skipped = @()
    }
    
    foreach ($branch in $branchesToCleanup) {
        try {
            # Skip if it's the current branch
            $currentBranch = & git rev-parse --abbrev-ref HEAD 2>$null
            if ($branch.Name -eq $currentBranch) {
                Write-Host "⏭️ Skipping current branch: $($branch.Name)" -ForegroundColor Yellow
                $cleanupResults.Skipped += $branch
                continue
            }
            
            # Delete the branch
            $deleteOutput = & git branch -D $branch.Name 2>&1
            if ($LASTEXITCODE -eq 0) {
                Write-Host "🗑️ Deleted branch: $($branch.Name)" -ForegroundColor Green
                $cleanupResults.Deleted += $branch
            } else {
                Write-Host "❌ Failed to delete branch: $($branch.Name)" -ForegroundColor Red
                $cleanupResults.Failed += @{
                    Branch = $branch
                    Error = $deleteOutput -join '; '
                }
            }
            
        } catch {
            Write-Host "❌ Error deleting branch $($branch.Name): $($_.Exception.Message)" -ForegroundColor Red
            $cleanupResults.Failed += @{
                Branch = $branch
                Error = $_.Exception.Message
            }
        }
    }
    
    Write-Host "📊 Cleanup results:" -ForegroundColor Yellow
    Write-Host "   Deleted: $($cleanupResults.Deleted.Count)" -ForegroundColor Green
    Write-Host "   Failed: $($cleanupResults.Failed.Count)" -ForegroundColor Red
    Write-Host "   Skipped: $($cleanupResults.Skipped.Count)" -ForegroundColor Gray
    
    return $cleanupResults
}

function Get-BranchSummary {
    Write-Host "📊 Recovery Branch Summary" -ForegroundColor Cyan
    Write-Host "="*40 -ForegroundColor Cyan
    
    $summary = @{}
    
    foreach ($branchType in $branchConfig.BranchTypes.Keys) {
        $branches = Get-RecoveryBranches -BranchType $branchType
        $typeConfig = $branchConfig.BranchTypes[$branchType]
        
        $summary[$branchType] = @{
            Count = $branches.Count
            Branches = $branches
            OldestAge = if ($branches.Count -gt 0) { ($branches | Measure-Object AgeInDays -Maximum).Maximum } else { 0 }
            NewestAge = if ($branches.Count -gt 0) { ($branches | Measure-Object AgeInDays -Minimum).Minimum } else { 0 }
            Config = $typeConfig
        }
        
        Write-Host "`n$($branchType.ToUpper()) branches:" -ForegroundColor Yellow
        Write-Host "  Count: $($branches.Count)" -ForegroundColor White
        Write-Host "  Description: $($typeConfig.Description)" -ForegroundColor Gray
        Write-Host "  Auto-cleanup: $($typeConfig.AutoCleanup)" -ForegroundColor Gray
        Write-Host "  Retention: $($typeConfig.Retention) days" -ForegroundColor Gray
        
        if ($branches.Count -gt 0) {
            Write-Host "  Age range: $($summary[$branchType].NewestAge.ToString('F1')) - $($summary[$branchType].OldestAge.ToString('F1')) days" -ForegroundColor Gray
            
            if ($Verbose) {
                $branches | Select-Object -First 3 | ForEach-Object {
                    Write-Host "    - $($_.Name) ($($_.AgeInDays.ToString('F1')) days)" -ForegroundColor Gray
                }
                if ($branches.Count -gt 3) {
                    Write-Host "    ... and $($branches.Count - 3) more" -ForegroundColor Gray
                }
            }
        }
    }
    
    $totalBranches = ($summary.Values | Measure-Object -Property Count -Sum).Sum
    Write-Host "`nTotal recovery branches: $totalBranches" -ForegroundColor Cyan
    
    if ($totalBranches -gt $MaxBranches) {
        Write-Host "⚠️ Exceeds maximum branches ($MaxBranches) - cleanup recommended" -ForegroundColor Yellow
    }
    
    return $summary
}

# Cleanup old branches if requested
if ($CleanupOldBranches) {
    Cleanup-OldBranches -DryRun:(!$CleanupOldBranches)
}

Export-ModuleMember -Function Create-SafetyBranch, Create-RecoveryBranch, Create-IsolationBranch, Create-MilestoneBranch, Get-RecoveryBranches, Merge-RecoveryBranch, Cleanup-OldBranches, Get-BranchSummary, Get-GitRepositoryStatus