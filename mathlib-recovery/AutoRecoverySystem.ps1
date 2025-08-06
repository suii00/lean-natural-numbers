# Mathlib Migration Auto Recovery System
# Automatic rollback, problem isolation, staged retry with branch management

param(
    [string]$ProjectPath = ".",
    [string]$RecoveryLogPath = "mathlib-recovery\recovery_log.json",
    [int]$MaxRetryAttempts = 3,
    [switch]$DryRun,
    [switch]$Verbose
)

# Recovery system configuration
$recoveryConfig = @{
    SafeCommitInterval = 300  # seconds
    MaxRollbackDepth = 5      # number of commits
    IsolationStrategies = @("FileLevel", "ModuleLevel", "ImportLevel")
    RetryStrategies = @("Incremental", "Selective", "Minimal")
    BranchPrefix = "recovery"
    BackupBranchPrefix = "backup"
}

# Initialize recovery state
$recoveryState = @{
    CurrentBranch = ""
    SafeCommitHash = ""
    ErrorCount = 0
    RecoveryAttempts = 0
    IsolatedFiles = @()
    FailedOperations = @()
    SuccessfulRecoveries = @()
}

function Initialize-RecoverySystem {
    Write-Host "🚨 Initializing Mathlib Auto Recovery System" -ForegroundColor Yellow
    
    # Create recovery directory
    if (!(Test-Path "mathlib-recovery")) {
        New-Item -ItemType Directory -Path "mathlib-recovery" | Out-Null
    }
    
    # Initialize git repository state
    $currentBranch = & git rev-parse --abbrev-ref HEAD 2>$null
    $currentCommit = & git rev-parse HEAD 2>$null
    
    $recoveryState.CurrentBranch = $currentBranch
    $recoveryState.SafeCommitHash = $currentCommit
    
    Write-Host "📍 Current branch: $currentBranch" -ForegroundColor Gray
    Write-Host "📍 Safe commit: $($currentCommit.Substring(0,8))" -ForegroundColor Gray
    
    # Load previous recovery log if exists
    if (Test-Path $RecoveryLogPath) {
        $previousLog = Get-Content $RecoveryLogPath | ConvertFrom-Json
        Write-Host "📚 Loaded previous recovery history: $($previousLog.TotalRecoveries) recoveries" -ForegroundColor Gray
    }
    
    return $true
}

function Detect-MathlibError {
    param([string]$Operation, [string]$LogOutput)
    
    $errorPatterns = @{
        "BuildFailure" = @{
            Patterns = @(
                "object file.*does not exist",
                "lean.*failed with code",
                "lake build.*failed"
            )
            Severity = "High"
            RecoveryStrategy = "Rollback"
        }
        "ImportError" = @{
            Patterns = @(
                "unknown package",
                "module.*not found",
                "import.*failed"
            )
            Severity = "Medium" 
            RecoveryStrategy = "Isolate"
        }
        "DependencyError" = @{
            Patterns = @(
                "dependency.*not found",
                "version conflict",
                "cache.*failed"
            )
            Severity = "High"
            RecoveryStrategy = "Rollback"
        }
        "SyntaxError" = @{
            Patterns = @(
                "expected token",
                "unexpected.*token",
                "syntax error"
            )
            Severity = "Low"
            RecoveryStrategy = "Isolate"
        }
    }
    
    $detectedErrors = @()
    
    foreach ($errorType in $errorPatterns.Keys) {
        $patterns = $errorPatterns[$errorType].Patterns
        foreach ($pattern in $patterns) {
            if ($LogOutput -match $pattern) {
                $error = @{
                    Type = $errorType
                    Pattern = $pattern
                    MatchedText = $matches[0]
                    Severity = $errorPatterns[$errorType].Severity
                    Strategy = $errorPatterns[$errorType].RecoveryStrategy
                    Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
                    Operation = $Operation
                }
                $detectedErrors += $error
                
                Write-Host "🔍 Detected error: $errorType" -ForegroundColor Red
                Write-Host "   Pattern: $pattern" -ForegroundColor Gray
                Write-Host "   Severity: $($error.Severity)" -ForegroundColor Gray
                break
            }
        }
    }
    
    return $detectedErrors
}

function Create-SafetyBranch {
    param([string]$BranchName, [string]$Purpose)
    
    $timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
    $safeBranch = "$($recoveryConfig.BackupBranchPrefix)_${BranchName}_$timestamp"
    
    Write-Host "🛡️ Creating safety branch: $safeBranch" -ForegroundColor Cyan
    
    try {
        & git checkout -b $safeBranch 2>$null
        if ($LASTEXITCODE -eq 0) {
            & git checkout $recoveryState.CurrentBranch 2>$null
            
            $backupInfo = @{
                BranchName = $safeBranch
                Purpose = $Purpose
                SourceBranch = $recoveryState.CurrentBranch
                SourceCommit = $recoveryState.SafeCommitHash
                Created = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
            }
            
            Write-Host "✅ Safety branch created successfully" -ForegroundColor Green
            return $backupInfo
        }
    } catch {
        Write-Host "❌ Failed to create safety branch: $_" -ForegroundColor Red
        return $null
    }
}

function Rollback-ToSafeState {
    param([string]$Reason, [int]$StepsBack = 1)
    
    Write-Host "⏪ Initiating rollback: $Reason" -ForegroundColor Yellow
    
    # Create emergency backup before rollback
    $backup = Create-SafetyBranch "emergency" "Pre-rollback emergency backup"
    
    try {
        # Get commit history
        $commitHistory = & git log --oneline -n $recoveryConfig.MaxRollbackDepth
        Write-Host "📜 Available rollback points:" -ForegroundColor Gray
        $commitHistory | ForEach-Object { Write-Host "   $_" -ForegroundColor White }
        
        # Determine rollback target
        $rollbackTarget = if ($StepsBack -eq 1) {
            $recoveryState.SafeCommitHash
        } else {
            $commits = & git log --format="%H" -n $StepsBack
            $commits[$StepsBack - 1]
        }
        
        Write-Host "🎯 Rolling back to: $($rollbackTarget.Substring(0,8))" -ForegroundColor Yellow
        
        if (!$DryRun) {
            # Perform hard reset to safe state
            & git reset --hard $rollbackTarget
            
            if ($LASTEXITCODE -eq 0) {
                Write-Host "✅ Successfully rolled back to safe state" -ForegroundColor Green
                
                # Update recovery state
                $recoveryState.RecoveryAttempts++
                $recoveryState.SuccessfulRecoveries += @{
                    Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
                    Reason = $Reason
                    RollbackTarget = $rollbackTarget
                    BackupBranch = $backup.BranchName
                }
                
                return @{
                    Success = $true
                    RollbackTarget = $rollbackTarget
                    BackupBranch = $backup.BranchName
                }
            }
        } else {
            Write-Host "🔍 DRY RUN: Would rollback to $($rollbackTarget.Substring(0,8))" -ForegroundColor Cyan
            return @{
                Success = $true
                RollbackTarget = $rollbackTarget
                DryRun = $true
            }
        }
    } catch {
        Write-Host "❌ Rollback failed: $_" -ForegroundColor Red
        return @{
            Success = $false
            Error = $_.Exception.Message
        }
    }
}

function Isolate-ProblematicFiles {
    param([array]$ErrorInfo, [string]$Strategy = "FileLevel")
    
    Write-Host "🔬 Isolating problematic components: $Strategy" -ForegroundColor Cyan
    
    $isolatedItems = @()
    
    switch ($Strategy) {
        "FileLevel" {
            # Find files mentioned in error messages
            foreach ($error in $ErrorInfo) {
                $fileMatches = [regex]::Matches($error.MatchedText, '([^\\s]+\.lean)')
                foreach ($match in $fileMatches) {
                    $filename = $match.Groups[1].Value
                    if (Test-Path $filename) {
                        $isolatedItems += @{
                            Type = "File"
                            Path = $filename
                            Reason = $error.Type
                            BackupPath = "mathlib-recovery\isolated_$((Get-Date -Format 'HHmmss'))_$(Split-Path $filename -Leaf)"
                        }
                    }
                }
            }
        }
        
        "ModuleLevel" {
            # Isolate entire modules/directories
            foreach ($error in $ErrorInfo) {
                if ($error.MatchedText -match 'module ([^\\s]+)') {
                    $moduleName = $matches[1]
                    $isolatedItems += @{
                        Type = "Module"
                        Name = $moduleName
                        Reason = $error.Type
                    }
                }
            }
        }
        
        "ImportLevel" {
            # Isolate specific import statements
            foreach ($error in $ErrorInfo) {
                if ($error.MatchedText -match 'import ([^\\s]+)') {
                    $importStatement = $matches[1]
                    $isolatedItems += @{
                        Type = "Import"
                        Statement = $importStatement
                        Reason = $error.Type
                    }
                }
            }
        }
    }
    
    # Perform isolation
    foreach ($item in $isolatedItems) {
        Write-Host "🚧 Isolating: $($item.Type) - $($item.Path ?? $item.Name ?? $item.Statement)" -ForegroundColor Yellow
        
        if ($item.Type -eq "File" -and !$DryRun) {
            # Move problematic file to isolation directory
            Copy-Item $item.Path $item.BackupPath -ErrorAction SilentlyContinue
            $item.Path | Out-File -FilePath "$($item.Path).isolated" -Encoding UTF8
            Remove-Item $item.Path -ErrorAction SilentlyContinue
        }
    }
    
    $recoveryState.IsolatedFiles += $isolatedItems
    
    Write-Host "✅ Isolated $($isolatedItems.Count) problematic components" -ForegroundColor Green
    return $isolatedItems
}

function Execute-StagedRetry {
    param([string]$Operation, [array]$IsolatedItems, [string]$Strategy = "Incremental")
    
    Write-Host "🔄 Starting staged retry: $Strategy" -ForegroundColor Cyan
    
    $retryResults = @()
    $currentAttempt = 0
    
    while ($currentAttempt -lt $MaxRetryAttempts) {
        $currentAttempt++
        Write-Host "🎯 Retry attempt $currentAttempt of $MaxRetryAttempts" -ForegroundColor Yellow
        
        $retryBranch = "$($recoveryConfig.BranchPrefix)_attempt_$currentAttempt"
        
        # Create retry branch
        & git checkout -b $retryBranch 2>$null
        
        switch ($Strategy) {
            "Incremental" {
                # Gradually add back isolated components
                $componentsToRestore = [math]::Min($currentAttempt, $IsolatedItems.Count)
                Write-Host "📈 Restoring $componentsToRestore components incrementally" -ForegroundColor Gray
                
                for ($i = 0; $i -lt $componentsToRestore; $i++) {
                    $item = $IsolatedItems[$i]
                    if ($item.Type -eq "File" -and (Test-Path $item.BackupPath)) {
                        Copy-Item $item.BackupPath $item.Path -ErrorAction SilentlyContinue
                        Write-Host "   Restored: $($item.Path)" -ForegroundColor Green
                    }
                }
            }
            
            "Selective" {
                # Only restore items that are likely to work
                $lowRiskItems = $IsolatedItems | Where-Object { $_.Reason -eq "SyntaxError" }
                Write-Host "🎯 Selectively restoring $($lowRiskItems.Count) low-risk components" -ForegroundColor Gray
                
                foreach ($item in $lowRiskItems) {
                    if ($item.Type -eq "File" -and (Test-Path $item.BackupPath)) {
                        Copy-Item $item.BackupPath $item.Path -ErrorAction SilentlyContinue
                        Write-Host "   Restored: $($item.Path)" -ForegroundColor Green
                    }
                }
            }
            
            "Minimal" {
                # Restore only essential components
                Write-Host "🔻 Minimal restoration - essential components only" -ForegroundColor Gray
                # Logic for determining essential vs non-essential components
            }
        }
        
        # Test the retry
        $testResult = Test-MathlibOperation $Operation
        
        $retryResult = @{
            Attempt = $currentAttempt
            Strategy = $Strategy
            Branch = $retryBranch
            Success = $testResult.Success
            Errors = $testResult.Errors
            Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        }
        
        $retryResults += $retryResult
        
        if ($testResult.Success) {
            Write-Host "✅ Retry successful on attempt $currentAttempt" -ForegroundColor Green
            
            # Merge successful retry back to main branch
            & git checkout $recoveryState.CurrentBranch
            & git merge $retryBranch --no-ff -m "Successful recovery: $Operation (attempt $currentAttempt)"
            
            break
        } else {
            Write-Host "❌ Retry attempt $currentAttempt failed" -ForegroundColor Red
            $testResult.Errors | ForEach-Object {
                Write-Host "   Error: $_" -ForegroundColor Red
            }
            
            # Switch back to main branch for next attempt
            & git checkout $recoveryState.CurrentBranch
        }
    }
    
    return $retryResults
}

function Test-MathlibOperation {
    param([string]$Operation)
    
    Write-Host "🧪 Testing operation: $Operation" -ForegroundColor Gray
    
    $testOutput = ""
    $testSuccess = $false
    
    switch ($Operation.ToLower()) {
        "build" {
            $testOutput = & lake build 2>&1
            $testSuccess = $LASTEXITCODE -eq 0
        }
        "update" {
            $testOutput = & lake update 2>&1
            $testSuccess = $LASTEXITCODE -eq 0
        }
        "cache" {
            $testOutput = & lake exe cache get 2>&1
            $testSuccess = $LASTEXITCODE -eq 0
        }
        default {
            $testOutput = "Unknown operation: $Operation"
            $testSuccess = $false
        }
    }
    
    return @{
        Success = $testSuccess
        Output = $testOutput -join "`n"
        Errors = if (!$testSuccess) { $testOutput | Where-Object { $_ -match "error:" } } else { @() }
    }
}

function Save-RecoveryLog {
    param([hashtable]$RecoverySession)
    
    $logEntry = @{
        SessionId = [guid]::NewGuid().ToString()
        StartTime = $RecoverySession.StartTime
        EndTime = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        TotalErrors = $recoveryState.ErrorCount
        RecoveryAttempts = $recoveryState.RecoveryAttempts
        SuccessfulRecoveries = $recoveryState.SuccessfulRecoveries.Count
        IsolatedFiles = $recoveryState.IsolatedFiles
        FinalStatus = $RecoverySession.FinalStatus
        BranchesCreated = $RecoverySession.BranchesCreated
        Lessons = $RecoverySession.Lessons
    }
    
    # Load existing log or create new
    $existingLog = if (Test-Path $RecoveryLogPath) {
        Get-Content $RecoveryLogPath | ConvertFrom-Json
    } else {
        @{ Sessions = @(); TotalRecoveries = 0 }
    }
    
    $existingLog.Sessions += $logEntry
    $existingLog.TotalRecoveries = $existingLog.Sessions.Count
    $existingLog.LastUpdated = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    
    $existingLog | ConvertTo-Json -Depth 10 | Out-File -FilePath $RecoveryLogPath -Encoding UTF8
    
    Write-Host "💾 Recovery session saved to log: $RecoveryLogPath" -ForegroundColor Green
}

# Main recovery orchestration function
function Start-AutoRecovery {
    param([string]$Operation, [string]$ErrorOutput)
    
    $sessionStart = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    Write-Host "🚨 AUTO RECOVERY INITIATED" -ForegroundColor Red
    Write-Host "Operation: $Operation" -ForegroundColor Gray
    Write-Host "Time: $sessionStart" -ForegroundColor Gray
    Write-Host "=" * 60 -ForegroundColor Yellow
    
    # Initialize recovery system
    if (!(Initialize-RecoverySystem)) {
        Write-Host "❌ Failed to initialize recovery system" -ForegroundColor Red
        return $false
    }
    
    # Detect errors
    $detectedErrors = Detect-MathlibError $Operation $ErrorOutput
    $recoveryState.ErrorCount = $detectedErrors.Count
    
    if ($detectedErrors.Count -eq 0) {
        Write-Host "✅ No errors detected - recovery not needed" -ForegroundColor Green
        return $true
    }
    
    $recoverySession = @{
        StartTime = $sessionStart
        BranchesCreated = @()
        Lessons = @()
        FinalStatus = "Unknown"
    }
    
    # Determine recovery strategy based on error severity
    $highSeverityErrors = $detectedErrors | Where-Object { $_.Severity -eq "High" }
    $needsRollback = $highSeverityErrors.Count -gt 0
    
    if ($needsRollback) {
        Write-Host "⚠️ High severity errors detected - initiating rollback" -ForegroundColor Red
        
        $rollbackResult = Rollback-ToSafeState "High severity errors in $Operation" 1
        $recoverySession.BranchesCreated += $rollbackResult.BackupBranch
        
        if (!$rollbackResult.Success) {
            $recoverySession.FinalStatus = "RollbackFailed"
            Save-RecoveryLog $recoverySession
            return $false
        }
    }
    
    # Isolate problematic components
    $isolatedItems = Isolate-ProblematicFiles $detectedErrors "FileLevel"
    
    # Execute staged retry
    $retryResults = Execute-StagedRetry $Operation $isolatedItems "Incremental"
    $recoverySession.BranchesCreated += ($retryResults | ForEach-Object { $_.Branch })
    
    # Determine final status
    $successfulRetry = $retryResults | Where-Object { $_.Success }
    if ($successfulRetry) {
        $recoverySession.FinalStatus = "Recovered"
        $recoverySession.Lessons += "Successfully recovered using $($successfulRetry[0].Strategy) strategy"
        Write-Host "🎉 AUTO RECOVERY SUCCESSFUL" -ForegroundColor Green
        $finalResult = $true
    } else {
        $recoverySession.FinalStatus = "Failed"
        $recoverySession.Lessons += "All retry strategies failed - manual intervention required"
        Write-Host "❌ AUTO RECOVERY FAILED - Manual intervention required" -ForegroundColor Red
        $finalResult = $false
    }
    
    # Save recovery log
    Save-RecoveryLog $recoverySession
    
    # Cleanup temporary branches (keep backups)
    $retryResults | ForEach-Object {
        if (!$_.Success) {
            & git branch -D $_.Branch 2>$null
        }
    }
    
    Write-Host "=" * 60 -ForegroundColor Yellow
    Write-Host "🏁 AUTO RECOVERY COMPLETED" -ForegroundColor Cyan
    Write-Host "Status: $($recoverySession.FinalStatus)" -ForegroundColor $(if($finalResult) {"Green"} else {"Red"})
    
    return $finalResult
}

# Export main function for external use
Export-ModuleMember -Function Start-AutoRecovery