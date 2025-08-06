# Recovery Orchestration System for Mathlib Migration
# Master coordinator for all recovery operations: detection, rollback, isolation, retry, and branch management

param(
    [string]$Operation = "build",
    [string]$ErrorLog = "",
    [string]$RecoveryStrategy = "Smart", # Smart, Conservative, Aggressive
    [int]$MaxRecoveryAttempts = 3,
    [switch]$AutoMode,
    [switch]$DryRun,
    [switch]$Verbose
)

# Import all recovery modules
$scriptPath = Split-Path -Parent $MyInvocation.MyCommand.Definition
. "$scriptPath\AutoRecoverySystem.ps1"
. "$scriptPath\ProblemIsolation.ps1"
. "$scriptPath\StagedRetrySystem.ps1"
. "$scriptPath\BranchManager.ps1"

# Orchestration configuration
$orchestrationConfig = @{
    RecoveryStrategies = @{
        "Conservative" = @{
            Description = "Safe approach with minimal risk"
            RollbackOnHighSeverity = $true
            IsolationMode = "Conservative"
            RetryStrategy = "Conservative"
            MaxRetries = 2
            RequireManualConfirmation = $true
        }
        "Smart" = @{
            Description = "Balanced approach with intelligent decisions"
            RollbackOnHighSeverity = $true
            IsolationMode = "Smart"
            RetryStrategy = "Progressive"
            MaxRetries = 3
            RequireManualConfirmation = $false
        }
        "Aggressive" = @{
            Description = "Fast recovery with higher risk tolerance"
            RollbackOnHighSeverity = $false
            IsolationMode = "Aggressive"
            RetryStrategy = "Aggressive"
            MaxRetries = 5
            RequireManualConfirmation = $false
        }
    }
    
    CriticalErrorThreshold = 3
    PartialSuccessThreshold = 0.7
    
    RecoveryPhases = @(
        "Detection",
        "SafetyBackup",
        "Assessment",
        "Isolation",
        "Recovery",
        "Validation",
        "Consolidation"
    )
    
    NotificationLevels = @{
        "Info" = "Cyan"
        "Warning" = "Yellow"
        "Error" = "Red"
        "Success" = "Green"
        "Critical" = "Magenta"
    }
}

function Write-RecoveryNotification {
    param([string]$Message, [string]$Level = "Info", [string]$Phase = "")
    
    $color = $orchestrationConfig.NotificationLevels[$Level]
    $phasePrefix = if ($Phase) { "[$Phase] " } else { "" }
    $levelPrefix = switch ($Level) {
        "Info" { "ℹ️" }
        "Warning" { "⚠️" }
        "Error" { "❌" }
        "Success" { "✅" }
        "Critical" { "🚨" }
        default { "📝" }
    }
    
    Write-Host "$levelPrefix $phasePrefix$Message" -ForegroundColor $color
}

function Initialize-RecoverySession {
    param([string]$OperationType, [string]$Strategy)
    
    Write-RecoveryNotification "RECOVERY ORCHESTRATION INITIATED" "Critical"
    Write-RecoveryNotification "Operation: $OperationType | Strategy: $Strategy" "Info"
    Write-RecoveryNotification "="*60 "Info"
    
    $session = @{
        SessionId = [guid]::NewGuid().ToString().Substring(0,8)
        StartTime = Get-Date
        Operation = $OperationType
        Strategy = $Strategy
        Config = $orchestrationConfig.RecoveryStrategies[$Strategy]
        Phases = @{}
        Branches = @{}
        FinalStatus = "InProgress"
        ErrorHistory = @()
        RecoveryActions = @()
        Metrics = @{
            TotalPhases = $orchestrationConfig.RecoveryPhases.Count
            CompletedPhases = 0
            SuccessfulRetries = 0
            TotalRetries = 0
            IsolatedComponents = 0
            CreatedBranches = 0
        }
    }
    
    # Create session branch for tracking
    $sessionBranch = Create-SafetyBranch "orchestration_session_$($session.SessionId)" ""
    $session.Branches.Session = $sessionBranch
    $session.Metrics.CreatedBranches++
    
    Write-RecoveryNotification "Recovery session initialized: $($session.SessionId)" "Success"
    Write-RecoveryNotification "Session branch created: $($sessionBranch.Name)" "Info"
    
    return $session
}

function Execute-DetectionPhase {
    param([hashtable]$Session, [string]$ErrorInput)
    
    Write-RecoveryNotification "Starting error detection phase..." "Info" "Detection"
    
    $phaseResult = @{
        Phase = "Detection"
        StartTime = Get-Date
        Success = $false
        DetectedErrors = @()
        ErrorSeverity = "Unknown"
        RequiresRecovery = $false
    }
    
    try {
        # Detect errors from various sources
        if ($ErrorInput) {
            Write-RecoveryNotification "Analyzing provided error log..." "Info" "Detection"
            $detectedErrors = Detect-MathlibError $Session.Operation $ErrorInput
        } else {
            Write-RecoveryNotification "Running operation to detect errors..." "Info" "Detection"
            
            # Execute operation to capture errors
            $operationResult = Test-MathlibOperation $Session.Operation
            if (!$operationResult.Success) {
                $detectedErrors = Detect-MathlibError $Session.Operation $operationResult.Output
            } else {
                $detectedErrors = @()
            }
        }
        
        $phaseResult.DetectedErrors = $detectedErrors
        $phaseResult.Success = $true
        
        # Assess error severity
        $highSeverityCount = ($detectedErrors | Where-Object { $_.Severity -eq "High" }).Count
        $mediumSeverityCount = ($detectedErrors | Where-Object { $_.Severity -eq "Medium" }).Count
        $lowSeverityCount = ($detectedErrors | Where-Object { $_.Severity -eq "Low" }).Count
        
        $phaseResult.ErrorSeverity = if ($highSeverityCount -gt 0) { "High" }
                                    elseif ($mediumSeverityCount -gt 2) { "High" }
                                    elseif ($mediumSeverityCount -gt 0) { "Medium" }
                                    elseif ($lowSeverityCount -gt 0) { "Low" }
                                    else { "None" }
        
        $phaseResult.RequiresRecovery = $phaseResult.ErrorSeverity -ne "None"
        
        Write-RecoveryNotification "Detected $($detectedErrors.Count) errors (Severity: $($phaseResult.ErrorSeverity))" "Warning" "Detection"
        
        if (!$phaseResult.RequiresRecovery) {
            Write-RecoveryNotification "No recovery required - system is healthy" "Success" "Detection"
        }
        
    } catch {
        Write-RecoveryNotification "Detection phase failed: $($_.Exception.Message)" "Error" "Detection"
        $phaseResult.Error = $_.Exception.Message
    }
    
    $phaseResult.Duration = (Get-Date) - $phaseResult.StartTime
    $Session.Phases.Detection = $phaseResult
    $Session.Metrics.CompletedPhases++
    
    return $phaseResult
}

function Execute-SafetyBackupPhase {
    param([hashtable]$Session)
    
    Write-RecoveryNotification "Creating safety backups..." "Info" "SafetyBackup"
    
    $phaseResult = @{
        Phase = "SafetyBackup"
        StartTime = Get-Date
        Success = $false
        CreatedBranches = @()
        BackupStrategy = $Session.Config.IsolationMode
    }
    
    try {
        # Create comprehensive safety backup
        $safetyBranch = Create-SafetyBranch "pre_recovery_$($Session.SessionId)" "Full backup before recovery"
        $phaseResult.CreatedBranches += $safetyBranch
        $Session.Branches.Safety = $safetyBranch
        $Session.Metrics.CreatedBranches++
        
        # Create milestone if this is a significant point
        $gitStatus = Get-GitRepositoryStatus
        if (!$gitStatus.HasUncommittedChanges) {
            $milestoneBranch = Create-MilestoneBranch "recovery_start" "Stable state before recovery operations"
            $phaseResult.CreatedBranches += $milestoneBranch
            $Session.Branches.Milestone = $milestoneBranch
            $Session.Metrics.CreatedBranches++
        }
        
        $phaseResult.Success = $true
        Write-RecoveryNotification "Safety backups created successfully" "Success" "SafetyBackup"
        
    } catch {
        Write-RecoveryNotification "Safety backup phase failed: $($_.Exception.Message)" "Error" "SafetyBackup"
        $phaseResult.Error = $_.Exception.Message
    }
    
    $phaseResult.Duration = (Get-Date) - $phaseResult.StartTime
    $Session.Phases.SafetyBackup = $phaseResult
    $Session.Metrics.CompletedPhases++
    
    return $phaseResult
}

function Execute-AssessmentPhase {
    param([hashtable]$Session, [array]$DetectedErrors)
    
    Write-RecoveryNotification "Assessing recovery requirements..." "Info" "Assessment"
    
    $phaseResult = @{
        Phase = "Assessment"
        StartTime = Get-Date
        Success = $false
        RecoveryPlan = @{}
        RiskAssessment = @{}
        RequiredActions = @()
    }
    
    try {
        # Assess rollback requirements
        $needsRollback = $false
        if ($Session.Config.RollbackOnHighSeverity) {
            $highSeverityErrors = $DetectedErrors | Where-Object { $_.Severity -eq "High" }
            if ($highSeverityErrors.Count -gt 0) {
                $needsRollback = $true
                Write-RecoveryNotification "High severity errors detected - rollback required" "Warning" "Assessment"
            }
        }
        
        # Assess isolation requirements
        $isolationRequired = $DetectedErrors.Count -gt 0
        $isolationComplexity = switch ($DetectedErrors.Count) {
            { $_ -eq 0 } { "None" }
            { $_ -le 2 } { "Simple" }
            { $_ -le 5 } { "Moderate" }
            default { "Complex" }
        }
        
        # Create recovery plan
        $recoveryPlan = @{
            NeedsRollback = $needsRollback
            RollbackDepth = if ($needsRollback) { 1 } else { 0 }
            IsolationRequired = $isolationRequired
            IsolationComplexity = $isolationComplexity
            IsolationMode = $Session.Config.IsolationMode
            RetryStrategy = $Session.Config.RetryStrategy
            MaxRetries = $Session.Config.MaxRetries
            EstimatedDuration = [TimeSpan]::FromMinutes(15 * $DetectedErrors.Count)
        }
        
        # Risk assessment
        $riskFactors = @()
        if ($DetectedErrors.Count -gt $orchestrationConfig.CriticalErrorThreshold) {
            $riskFactors += "High error count"
        }
        if (($DetectedErrors | Where-Object { $_.Type -eq "DependencyError" }).Count -gt 0) {
            $riskFactors += "Dependency errors present"
        }
        
        $riskLevel = switch ($riskFactors.Count) {
            0 { "Low" }
            1 { "Medium" }
            default { "High" }
        }
        
        $riskAssessment = @{
            Level = $riskLevel
            Factors = $riskFactors
            Mitigation = @()
        }
        
        # Define required actions
        $requiredActions = @()
        if ($needsRollback) { $requiredActions += "Rollback" }
        if ($isolationRequired) { $requiredActions += "Isolation" }
        $requiredActions += "Retry"
        $requiredActions += "Validation"
        
        $phaseResult.RecoveryPlan = $recoveryPlan
        $phaseResult.RiskAssessment = $riskAssessment
        $phaseResult.RequiredActions = $requiredActions
        $phaseResult.Success = $true
        
        Write-RecoveryNotification "Recovery plan created: $($requiredActions -join ' -> ')" "Success" "Assessment"
        Write-RecoveryNotification "Risk level: $riskLevel | Estimated duration: $($recoveryPlan.EstimatedDuration.TotalMinutes.ToString('F0')) minutes" "Info" "Assessment"
        
    } catch {
        Write-RecoveryNotification "Assessment phase failed: $($_.Exception.Message)" "Error" "Assessment"
        $phaseResult.Error = $_.Exception.Message
    }
    
    $phaseResult.Duration = (Get-Date) - $phaseResult.StartTime
    $Session.Phases.Assessment = $phaseResult
    $Session.Metrics.CompletedPhases++
    
    return $phaseResult
}

function Execute-IsolationPhase {
    param([hashtable]$Session, [array]$DetectedErrors, [hashtable]$RecoveryPlan)
    
    if (!$RecoveryPlan.IsolationRequired) {
        Write-RecoveryNotification "Isolation phase skipped - not required" "Info" "Isolation"
        return @{ Phase = "Isolation"; Success = $true; Skipped = $true }
    }
    
    Write-RecoveryNotification "Starting problem isolation..." "Info" "Isolation"
    
    $phaseResult = @{
        Phase = "Isolation"
        StartTime = Get-Date
        Success = $false
        IsolationResults = @{}
        IsolatedComponents = @()
    }
    
    try {
        # Create isolation branch
        $isolationBranch = Create-IsolationBranch $RecoveryPlan.IsolationComplexity $DetectedErrors
        $Session.Branches.Isolation = $isolationBranch
        $Session.Metrics.CreatedBranches++
        
        # Execute problem isolation
        $isolationResults = Start-ProblemIsolation -ErrorLog $DetectedErrors -IsolationMode $RecoveryPlan.IsolationMode -Verbose:$Verbose
        
        $phaseResult.IsolationResults = $isolationResults
        $phaseResult.IsolatedComponents = $isolationResults.Results.Isolated
        $Session.Metrics.IsolatedComponents = $isolationResults.Results.Isolated.Count
        
        if ($isolationResults.Results.Isolated.Count -gt 0) {
            Write-RecoveryNotification "Successfully isolated $($isolationResults.Results.Isolated.Count) components" "Success" "Isolation"
            $phaseResult.Success = $true
        } else {
            Write-RecoveryNotification "No components were isolated" "Warning" "Isolation"
            $phaseResult.Success = $true  # Not necessarily a failure
        }
        
    } catch {
        Write-RecoveryNotification "Isolation phase failed: $($_.Exception.Message)" "Error" "Isolation"
        $phaseResult.Error = $_.Exception.Message
    }
    
    $phaseResult.Duration = (Get-Date) - $phaseResult.StartTime
    $Session.Phases.Isolation = $phaseResult
    $Session.Metrics.CompletedPhases++
    
    return $phaseResult
}

function Execute-RecoveryPhase {
    param([hashtable]$Session, [hashtable]$RecoveryPlan, [array]$IsolatedComponents)
    
    Write-RecoveryNotification "Starting recovery operations..." "Info" "Recovery"
    
    $phaseResult = @{
        Phase = "Recovery"
        StartTime = Get-Date
        Success = $false
        RollbackResult = @{}
        RetryResults = @{}
        RecoveryBranches = @()
    }
    
    try {
        # Execute rollback if required
        if ($RecoveryPlan.NeedsRollback) {
            Write-RecoveryNotification "Executing rollback..." "Warning" "Recovery"
            
            $rollbackResult = Rollback-ToSafeState "High severity errors in $($Session.Operation)" $RecoveryPlan.RollbackDepth
            $phaseResult.RollbackResult = $rollbackResult
            
            if (!$rollbackResult.Success) {
                throw "Rollback operation failed: $($rollbackResult.Error)"
            }
            
            Write-RecoveryNotification "Rollback completed successfully" "Success" "Recovery"
        }
        
        # Execute staged retry
        Write-RecoveryNotification "Starting staged retry process..." "Info" "Recovery"
        
        for ($attempt = 1; $attempt -le $RecoveryPlan.MaxRetries; $attempt++) {
            Write-RecoveryNotification "Recovery attempt $attempt of $($RecoveryPlan.MaxRetries)" "Info" "Recovery"
            
            # Create recovery branch for this attempt
            $recoveryBranch = Create-RecoveryBranch $Session.Operation $attempt.ToString()
            $phaseResult.RecoveryBranches += $recoveryBranch
            $Session.Metrics.CreatedBranches++
            $Session.Metrics.TotalRetries++
            
            # Execute staged retry
            $retryResult = Start-StagedRetry -TargetOperation $Session.Operation -RetryStrategyName $RecoveryPlan.RetryStrategy -MaxRetries 1
            
            if ($retryResult -and $retryResult.FinalResult.OverallSuccess) {
                Write-RecoveryNotification "Recovery attempt $attempt succeeded!" "Success" "Recovery"
                
                # Merge successful recovery
                $mergeResult = Merge-RecoveryBranch $recoveryBranch.Name -MergeStrategy "recovery"
                
                if ($mergeResult.Success) {
                    $phaseResult.Success = $true
                    $phaseResult.RetryResults = $retryResult
                    $Session.Metrics.SuccessfulRetries++
                    break
                } else {
                    Write-RecoveryNotification "Failed to merge recovery branch: $($mergeResult.Output)" "Warning" "Recovery"
                }
            } else {
                Write-RecoveryNotification "Recovery attempt $attempt failed" "Warning" "Recovery"
                
                if ($attempt -eq $RecoveryPlan.MaxRetries) {
                    throw "All recovery attempts exhausted"
                }
            }
        }
        
        if (!$phaseResult.Success) {
            throw "Recovery phase completed without success"
        }
        
    } catch {
        Write-RecoveryNotification "Recovery phase failed: $($_.Exception.Message)" "Error" "Recovery"
        $phaseResult.Error = $_.Exception.Message
    }
    
    $phaseResult.Duration = (Get-Date) - $phaseResult.StartTime
    $Session.Phases.Recovery = $phaseResult
    $Session.Metrics.CompletedPhases++
    
    return $phaseResult
}

function Execute-ValidationPhase {
    param([hashtable]$Session)
    
    Write-RecoveryNotification "Validating recovery results..." "Info" "Validation"
    
    $phaseResult = @{
        Phase = "Validation"
        StartTime = Get-Date
        Success = $false
        ValidationResults = @{}
        SystemHealth = @{}
    }
    
    try {
        # Test the original operation that failed
        Write-RecoveryNotification "Testing original operation..." "Info" "Validation"
        $operationTest = Test-MathlibOperation $Session.Operation
        
        $phaseResult.ValidationResults.OriginalOperation = $operationTest
        
        # Additional health checks
        $healthChecks = @{
            BasicCompilation = $false
            ImportFunctionality = $false
            DependencyIntegrity = $false
            BuildSystem = $false
        }
        
        # Basic compilation test
        try {
            $testContent = "theorem validation_test : True := trivial"
            [System.IO.File]::WriteAllText("temp_validation.lean", $testContent)
            $compileOutput = & lean temp_validation.lean 2>&1
            $healthChecks.BasicCompilation = $LASTEXITCODE -eq 0
            Remove-Item "temp_validation.lean" -ErrorAction SilentlyContinue
        } catch { }
        
        # Import functionality test
        try {
            $importTest = "import Std`ntheorem import_validation : True := trivial"
            [System.IO.File]::WriteAllText("temp_import_validation.lean", $importTest)
            $importOutput = & lean temp_import_validation.lean 2>&1
            $healthChecks.ImportFunctionality = $LASTEXITCODE -eq 0
            Remove-Item "temp_import_validation.lean" -ErrorAction SilentlyContinue
        } catch { }
        
        # Dependency integrity
        $healthChecks.DependencyIntegrity = Test-Path "lakefile.lean"
        
        # Build system test
        try {
            $buildOutput = & lake --version 2>&1
            $healthChecks.BuildSystem = $LASTEXITCODE -eq 0
        } catch { }
        
        $phaseResult.SystemHealth = $healthChecks
        
        # Calculate overall success
        $passedChecks = ($healthChecks.Values | Where-Object { $_ }).Count
        $totalChecks = $healthChecks.Count
        $successRate = $passedChecks / $totalChecks
        
        $phaseResult.Success = $operationTest.Success -and ($successRate -ge $orchestrationConfig.PartialSuccessThreshold)
        
        if ($phaseResult.Success) {
            Write-RecoveryNotification "Validation successful: $passedChecks/$totalChecks health checks passed" "Success" "Validation"
        } else {
            Write-RecoveryNotification "Validation failed: $passedChecks/$totalChecks health checks passed" "Warning" "Validation"
        }
        
    } catch {
        Write-RecoveryNotification "Validation phase failed: $($_.Exception.Message)" "Error" "Validation"
        $phaseResult.Error = $_.Exception.Message
    }
    
    $phaseResult.Duration = (Get-Date) - $phaseResult.StartTime
    $Session.Phases.Validation = $phaseResult
    $Session.Metrics.CompletedPhases++
    
    return $phaseResult
}

function Execute-ConsolidationPhase {
    param([hashtable]$Session, [boolean]$RecoverySuccessful)
    
    Write-RecoveryNotification "Consolidating recovery session..." "Info" "Consolidation"
    
    $phaseResult = @{
        Phase = "Consolidation"
        StartTime = Get-Date
        Success = $false
        BranchCleanup = @{}
        FinalState = @{}
        Documentation = @{}
    }
    
    try {
        # Determine final session status
        $Session.FinalStatus = if ($RecoverySuccessful) { "Success" } else { "Failed" }
        
        # Create final milestone if successful
        if ($RecoverySuccessful) {
            $finalMilestone = Create-MilestoneBranch "recovery_complete_$($Session.SessionId)" "Successful recovery completion"
            $Session.Branches.FinalMilestone = $finalMilestone
            $Session.Metrics.CreatedBranches++
        }
        
        # Clean up temporary branches
        $cleanupResults = @{
            Kept = @()
            Deleted = @()
        }
        
        foreach ($branchType in $Session.Branches.Keys) {
            $branch = $Session.Branches[$branchType]
            
            # Keep important branches, clean up temporary ones
            $shouldKeep = $branchType -in @("Safety", "FinalMilestone", "Milestone") -or 
                         ($branchType -eq "Recovery" -and $RecoverySuccessful)
            
            if ($shouldKeep) {
                $cleanupResults.Kept += $branch.Name
            } else {
                # Mark for cleanup but don't delete immediately
                $cleanupResults.Deleted += $branch.Name
            }
        }
        
        $phaseResult.BranchCleanup = $cleanupResults
        
        # Document final state
        $finalState = @{
            TotalDuration = (Get-Date) - $Session.StartTime
            CompletedPhases = $Session.Metrics.CompletedPhases
            TotalBranches = $Session.Metrics.CreatedBranches
            FinalBranchCount = (Get-RecoveryBranches).Count
            IsolatedComponents = $Session.Metrics.IsolatedComponents
            SuccessfulRetries = $Session.Metrics.SuccessfulRetries
            TotalRetries = $Session.Metrics.TotalRetries
        }
        
        $phaseResult.FinalState = $finalState
        $phaseResult.Success = $true
        
        # Generate recovery documentation
        $documentationPath = Generate-RecoveryDocumentation $Session
        $phaseResult.Documentation = @{ ReportPath = $documentationPath }
        
        Write-RecoveryNotification "Session consolidated - Duration: $($finalState.TotalDuration.TotalMinutes.ToString('F1')) minutes" "Success" "Consolidation"
        Write-RecoveryNotification "Documentation: $documentationPath" "Info" "Consolidation"
        
    } catch {
        Write-RecoveryNotification "Consolidation phase failed: $($_.Exception.Message)" "Error" "Consolidation"
        $phaseResult.Error = $_.Exception.Message
    }
    
    $phaseResult.Duration = (Get-Date) - $phaseResult.StartTime
    $Session.Phases.Consolidation = $phaseResult
    $Session.Metrics.CompletedPhases++
    
    return $phaseResult
}

function Generate-RecoveryDocumentation {
    param([hashtable]$Session)
    
    $reportPath = "mathlib-recovery\recovery_session_$($Session.SessionId).md"
    
    $report = @"
# Mathlib Migration Recovery Session Report

**Session ID**: $($Session.SessionId)
**Start Time**: $($Session.StartTime.ToString('yyyy-MM-dd HH:mm:ss'))
**End Time**: $((Get-Date).ToString('yyyy-MM-dd HH:mm:ss'))
**Total Duration**: $((Get-Date - $Session.StartTime).TotalMinutes.ToString('F1')) minutes
**Operation**: $($Session.Operation)
**Strategy**: $($Session.Strategy)
**Final Status**: $($Session.FinalStatus)

## Session Metrics

- **Phases Completed**: $($Session.Metrics.CompletedPhases)/$($orchestrationConfig.RecoveryPhases.Count)
- **Branches Created**: $($Session.Metrics.CreatedBranches)
- **Components Isolated**: $($Session.Metrics.IsolatedComponents)
- **Recovery Attempts**: $($Session.Metrics.TotalRetries)
- **Successful Recoveries**: $($Session.Metrics.SuccessfulRetries)

## Phase Results

"@

    foreach ($phaseName in $orchestrationConfig.RecoveryPhases) {
        $phase = $Session.Phases[$phaseName]
        if ($phase) {
            $report += @"

### $phaseName Phase
- **Status**: $(if($phase.Success) {'✅ Success'} else {'❌ Failed'})
- **Duration**: $($phase.Duration.TotalSeconds.ToString('F1')) seconds
"@
            if ($phase.Error) {
                $report += "- **Error**: $($phase.Error)`n"
            }
        }
    }
    
    $report += @"

## Created Branches

"@

    foreach ($branchType in $Session.Branches.Keys) {
        $branch = $Session.Branches[$branchType]
        $report += "- **$branchType**: $($branch.Name)`n"
    }
    
    if ($Session.Phases.Detection -and $Session.Phases.Detection.DetectedErrors) {
        $report += @"

## Detected Errors

"@
        $Session.Phases.Detection.DetectedErrors | ForEach-Object {
            $report += "- **Type**: $($_.Type) | **Severity**: $($_.Severity) | **Pattern**: $($_.Pattern)`n"
        }
    }
    
    $report += @"

## Lessons Learned

"@

    # Generate lessons based on session results
    $lessons = @()
    
    if ($Session.FinalStatus -eq "Success") {
        $lessons += "Recovery strategy '$($Session.Strategy)' was effective for this operation"
        
        if ($Session.Metrics.TotalRetries -eq 1) {
            $lessons += "Single retry attempt was sufficient - consider more aggressive initial approach"
        } elseif ($Session.Metrics.TotalRetries -gt 3) {
            $lessons += "Multiple retry attempts needed - consider more conservative initial approach"
        }
    } else {
        $lessons += "Recovery strategy '$($Session.Strategy)' was not effective for this operation"
        $lessons += "Consider manual intervention or different recovery strategy"
    }
    
    if ($Session.Metrics.IsolatedComponents -gt 0) {
        $lessons += "Component isolation was necessary - review isolated components for permanent fixes"
    }
    
    $lessons | ForEach-Object {
        $report += "- $_`n"
    }
    
    $report += @"

## Recommendations

"@

    # Generate recommendations based on session results
    $recommendations = @()
    
    if ($Session.FinalStatus -eq "Success") {
        $recommendations += "Monitor system for 24-48 hours to ensure stability"
        $recommendations += "Consider integrating successful patterns into automated recovery"
    } else {
        $recommendations += "Manual investigation required for unresolved issues"
        $recommendations += "Review error patterns for potential systematic fixes"
    }
    
    if ($Session.Metrics.CreatedBranches -gt 5) {
        $recommendations += "High number of branches created - schedule cleanup of temporary branches"
    }
    
    $recommendations | ForEach-Object {
        $report += "- $_`n"
    }
    
    $report += @"

---
*Report generated by Recovery Orchestration System*
*Generated at: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')*
"@

    [System.IO.File]::WriteAllText($reportPath, $report)
    return $reportPath
}

# Main orchestration function
function Start-RecoveryOrchestration {
    param([string]$TargetOperation = $Operation, [string]$Strategy = $RecoveryStrategy, [string]$ErrorInput = $ErrorLog)
    
    $session = Initialize-RecoverySession $TargetOperation $Strategy
    
    try {
        # Phase 1: Error Detection
        $detectionResult = Execute-DetectionPhase $session $ErrorInput
        
        if (!$detectionResult.RequiresRecovery) {
            Write-RecoveryNotification "No recovery needed - system is healthy" "Success"
            $session.FinalStatus = "NotRequired"
            return $session
        }
        
        # Phase 2: Safety Backup
        $backupResult = Execute-SafetyBackupPhase $session
        if (!$backupResult.Success) {
            throw "Failed to create safety backups"
        }
        
        # Phase 3: Assessment
        $assessmentResult = Execute-AssessmentPhase $session $detectionResult.DetectedErrors
        if (!$assessmentResult.Success) {
            throw "Failed to assess recovery requirements"
        }
        
        # Phase 4: Isolation
        $isolationResult = Execute-IsolationPhase $session $detectionResult.DetectedErrors $assessmentResult.RecoveryPlan
        
        # Phase 5: Recovery
        $recoveryResult = Execute-RecoveryPhase $session $assessmentResult.RecoveryPlan $isolationResult.IsolatedComponents
        
        # Phase 6: Validation
        $validationResult = Execute-ValidationPhase $session
        
        # Phase 7: Consolidation
        $consolidationResult = Execute-ConsolidationPhase $session $validationResult.Success
        
        # Final status determination
        $overallSuccess = $recoveryResult.Success -and $validationResult.Success -and $consolidationResult.Success
        $session.FinalStatus = if ($overallSuccess) { "Success" } else { "Failed" }
        
        # Final notification
        if ($overallSuccess) {
            Write-RecoveryNotification "RECOVERY ORCHESTRATION COMPLETED SUCCESSFULLY" "Success"
            Write-RecoveryNotification "All systems recovered and validated" "Success"
        } else {
            Write-RecoveryNotification "RECOVERY ORCHESTRATION FAILED" "Critical"
            Write-RecoveryNotification "Manual intervention may be required" "Warning"
        }
        
    } catch {
        Write-RecoveryNotification "CRITICAL ERROR: $($_.Exception.Message)" "Critical"
        $session.FinalStatus = "CriticalError"
        $session.ErrorHistory += @{
            Timestamp = Get-Date
            Error = $_.Exception.Message
            Phase = "Orchestration"
        }
    }
    
    Write-RecoveryNotification "="*60 "Info"
    Write-RecoveryNotification "Session ID: $($session.SessionId) | Status: $($session.FinalStatus)" "Info"
    Write-RecoveryNotification "Duration: $((Get-Date - $session.StartTime).TotalMinutes.ToString('F1')) minutes" "Info"
    
    return $session
}

# Main entry point
if ($AutoMode) {
    Write-RecoveryNotification "Auto mode enabled - starting orchestration" "Info"
    Start-RecoveryOrchestration
}

Export-ModuleMember -Function Start-RecoveryOrchestration