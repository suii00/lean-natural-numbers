# Staged Retry System for Mathlib Migration
# Implements intelligent retry strategies with progressive complexity

param(
    [string]$Operation = "build",
    [int]$MaxRetries = 5,
    [string]$RetryStrategy = "Progressive", # Progressive, Conservative, Aggressive
    [switch]$ContinueOnPartialSuccess,
    [switch]$Verbose
)

# Retry configuration
$retryConfig = @{
    BaseDelaySeconds = 30
    MaxDelaySeconds = 300
    BackoffMultiplier = 1.5
    PartialSuccessThreshold = 0.6
    
    RetryStrategies = @{
        "Progressive" = @{
            Description = "Start minimal, gradually add complexity"
            Stages = @("Minimal", "Basic", "Standard", "Full", "Complete")
        }
        "Conservative" = @{
            Description = "Safe approach with maximum compatibility"
            Stages = @("Safe", "Tested", "Stable", "Extended")
        }
        "Aggressive" = @{
            Description = "Fast approach with higher risk tolerance"
            Stages = @("Fast", "Parallel", "Full", "Override")
        }
    }
    
    OperationProfiles = @{
        "build" = @{
            MinimalCommand = "lake build MyProject"
            BasicCommand = "lake build"
            StandardCommand = "lake build && lake test"
            FullCommand = "lake build && lake exe cache get && lake test"
            CompleteCommand = "lake clean && lake build && lake exe cache get && lake test"
        }
        "update" = @{
            MinimalCommand = "lake update mathlib"
            BasicCommand = "lake update"
            StandardCommand = "lake update && lake build"
            FullCommand = "lake clean && lake update && lake exe cache get && lake build"
            CompleteCommand = "lake clean && rm -rf .lake && lake update && lake exe cache get && lake build"
        }
        "cache" = @{
            MinimalCommand = "lake exe cache get --lean-only"
            BasicCommand = "lake exe cache get"
            StandardCommand = "lake exe cache get && lake build"
            FullCommand = "lake clean && lake exe cache get && lake build"
            CompleteCommand = "lake clean && rm -rf .lake && lake update && lake exe cache get && lake build"
        }
    }
}

function Get-RetryStageConfiguration {
    param([string]$Strategy, [string]$Stage, [string]$Operation)
    
    $operationProfile = $retryConfig.OperationProfiles[$Operation]
    if (!$operationProfile) {
        Write-Host "⚠️ Unknown operation: $Operation, using default" -ForegroundColor Yellow
        $operationProfile = $retryConfig.OperationProfiles["build"]
    }
    
    $stageConfig = switch ($Stage) {
        "Minimal" { 
            @{
                Command = $operationProfile.MinimalCommand
                Timeout = 300
                Environment = @{ "LEAN_PATH" = "." }
                PreConditions = @()
                PostValidation = @("Check basic compilation")
                ExpectedSuccessRate = 0.9
            }
        }
        "Basic" { 
            @{
                Command = $operationProfile.BasicCommand
                Timeout = 600
                Environment = @{ "LEAN_PATH" = "." }
                PreConditions = @("Verify lakefile.lean exists")
                PostValidation = @("Check compilation", "Verify output files")
                ExpectedSuccessRate = 0.8
            }
        }
        "Standard" { 
            @{
                Command = $operationProfile.StandardCommand
                Timeout = 900
                Environment = @{}
                PreConditions = @("Verify dependencies", "Check network connectivity")
                PostValidation = @("Full compilation test", "Import validation")
                ExpectedSuccessRate = 0.7
            }
        }
        "Full" { 
            @{
                Command = $operationProfile.FullCommand
                Timeout = 1800
                Environment = @{}
                PreConditions = @("Clean build environment", "Verify cache connectivity")
                PostValidation = @("Complete build test", "All imports test")
                ExpectedSuccessRate = 0.6
            }
        }
        "Complete" { 
            @{
                Command = $operationProfile.CompleteCommand
                Timeout = 3600
                Environment = @{}
                PreConditions = @("Full cleanup", "Network verification", "Dependency refresh")
                PostValidation = @("Full system test", "Performance validation")
                ExpectedSuccessRate = 0.5
            }
        }
        default {
            Write-Host "⚠️ Unknown stage: $Stage, using Basic" -ForegroundColor Yellow
            Get-RetryStageConfiguration $Strategy "Basic" $Operation
        }
    }
    
    return $stageConfig
}

function Execute-PreConditions {
    param([array]$PreConditions)
    
    $results = @()
    
    foreach ($condition in $PreConditions) {
        Write-Host "🔍 Checking precondition: $condition" -ForegroundColor Gray
        
        $result = @{
            Condition = $condition
            Success = $false
            Message = ""
        }
        
        switch ($condition) {
            "Verify lakefile.lean exists" {
                $result.Success = Test-Path "lakefile.lean"
                $result.Message = if ($result.Success) { "lakefile.lean found" } else { "lakefile.lean missing" }
            }
            
            "Verify dependencies" {
                # Check if .lake directory exists and has content
                $lakeDir = Test-Path ".lake"
                $hasManifest = Test-Path "lake-manifest.json"
                $result.Success = $lakeDir -or $hasManifest
                $result.Message = if ($result.Success) { "Dependencies verified" } else { "Dependencies need initialization" }
            }
            
            "Check network connectivity" {
                try {
                    $ping = Test-NetConnection -ComputerName "github.com" -Port 443 -InformationLevel Quiet
                    $result.Success = $ping
                    $result.Message = if ($result.Success) { "Network connectivity OK" } else { "Network connectivity issues" }
                } catch {
                    $result.Success = $false
                    $result.Message = "Network check failed: $($_.Exception.Message)"
                }
            }
            
            "Clean build environment" {
                try {
                    if (Test-Path ".lake/build") {
                        Remove-Item ".lake/build" -Recurse -Force -ErrorAction SilentlyContinue
                    }
                    $result.Success = $true
                    $result.Message = "Build environment cleaned"
                } catch {
                    $result.Success = $false
                    $result.Message = "Cleanup failed: $($_.Exception.Message)"
                }
            }
            
            "Verify cache connectivity" {
                try {
                    $cacheTest = & lake exe cache get --help 2>&1
                    $result.Success = $LASTEXITCODE -eq 0
                    $result.Message = if ($result.Success) { "Cache system available" } else { "Cache system unavailable" }
                } catch {
                    $result.Success = $false
                    $result.Message = "Cache check failed: $($_.Exception.Message)"
                }
            }
            
            "Full cleanup" {
                try {
                    if (Test-Path ".lake") {
                        Remove-Item ".lake" -Recurse -Force -ErrorAction SilentlyContinue
                    }
                    if (Test-Path "lake-manifest.json") {
                        Remove-Item "lake-manifest.json" -Force -ErrorAction SilentlyContinue
                    }
                    $result.Success = $true
                    $result.Message = "Full cleanup completed"
                } catch {
                    $result.Success = $false
                    $result.Message = "Full cleanup failed: $($_.Exception.Message)"
                }
            }
            
            "Network verification" {
                # Comprehensive network check
                $checks = @("github.com", "leanprover-community.github.io")
                $passedChecks = 0
                foreach ($host in $checks) {
                    try {
                        $test = Test-NetConnection -ComputerName $host -Port 443 -InformationLevel Quiet
                        if ($test) { $passedChecks++ }
                    } catch { }
                }
                $result.Success = $passedChecks -eq $checks.Count
                $result.Message = "Network check: $passedChecks/$($checks.Count) hosts reachable"
            }
            
            "Dependency refresh" {
                try {
                    $output = & lake update 2>&1
                    $result.Success = $LASTEXITCODE -eq 0
                    $result.Message = if ($result.Success) { "Dependencies refreshed" } else { "Dependency refresh failed" }
                } catch {
                    $result.Success = $false
                    $result.Message = "Dependency refresh error: $($_.Exception.Message)"
                }
            }
            
            default {
                $result.Success = $true
                $result.Message = "Unknown precondition - skipping"
            }
        }
        
        if ($result.Success) {
            Write-Host "   ✅ $($result.Message)" -ForegroundColor Green
        } else {
            Write-Host "   ❌ $($result.Message)" -ForegroundColor Red
        }
        
        $results += $result
    }
    
    $overallSuccess = ($results | Where-Object { $_.Success }).Count -eq $results.Count
    return @{
        OverallSuccess = $overallSuccess
        Results = $results
        FailedConditions = $results | Where-Object { !$_.Success }
    }
}

function Execute-StageCommand {
    param([hashtable]$StageConfig, [int]$AttemptNumber)
    
    $startTime = Get-Date
    Write-Host "⚡ Executing stage command: $($StageConfig.Command)" -ForegroundColor Yellow
    Write-Host "   Timeout: $($StageConfig.Timeout)s | Attempt: $AttemptNumber" -ForegroundColor Gray
    
    # Set environment variables
    foreach ($envVar in $StageConfig.Environment.GetEnumerator()) {
        [Environment]::SetEnvironmentVariable($envVar.Key, $envVar.Value, "Process")
    }
    
    try {
        # Execute command with timeout
        $job = Start-Job -ScriptBlock {
            param($Command)
            Invoke-Expression $Command 2>&1
        } -ArgumentList $StageConfig.Command
        
        $completed = Wait-Job $job -Timeout $StageConfig.Timeout
        
        if ($completed) {
            $output = Receive-Job $job
            $exitCode = if ($job.State -eq "Completed") { 0 } else { 1 }
            Remove-Job $job -Force
        } else {
            Write-Host "⏰ Command timed out after $($StageConfig.Timeout) seconds" -ForegroundColor Red
            Stop-Job $job -ErrorAction SilentlyContinue
            Remove-Job $job -Force -ErrorAction SilentlyContinue
            $output = @("Command timed out")
            $exitCode = 124  # Timeout exit code
        }
        
        $duration = (Get-Date) - $startTime
        $success = $exitCode -eq 0
        
        $result = @{
            Success = $success
            ExitCode = $exitCode
            Output = $output -join "`n"
            Duration = $duration
            Command = $StageConfig.Command
            TimedOut = !$completed
        }
        
        if ($success) {
            Write-Host "   ✅ Command completed successfully in $($duration.TotalSeconds.ToString('F1'))s" -ForegroundColor Green
        } else {
            Write-Host "   ❌ Command failed with exit code $exitCode" -ForegroundColor Red
            if ($Verbose) {
                $output | Select-Object -First 5 | ForEach-Object {
                    Write-Host "      $_" -ForegroundColor Red
                }
            }
        }
        
        return $result
        
    } catch {
        $duration = (Get-Date) - $startTime
        Write-Host "   ❌ Command execution failed: $($_.Exception.Message)" -ForegroundColor Red
        
        return @{
            Success = $false
            ExitCode = -1
            Output = $_.Exception.Message
            Duration = $duration
            Command = $StageConfig.Command
            Error = $_.Exception.Message
        }
    }
}

function Execute-PostValidation {
    param([array]$ValidationChecks, [hashtable]$CommandResult)
    
    $results = @()
    
    foreach ($check in $ValidationChecks) {
        Write-Host "🔬 Running validation: $check" -ForegroundColor Gray
        
        $result = @{
            Check = $check
            Success = $false
            Message = ""
            Details = @{}
        }
        
        switch ($check) {
            "Check basic compilation" {
                # Test if we can compile a simple theorem
                $testContent = "theorem test_compilation : True := trivial"
                $testFile = "temp_validation_test.lean"
                
                try {
                    [System.IO.File]::WriteAllText($testFile, $testContent)
                    $compileOutput = & lean $testFile 2>&1
                    $result.Success = $LASTEXITCODE -eq 0
                    $result.Message = if ($result.Success) { "Basic compilation works" } else { "Basic compilation failed" }
                    Remove-Item $testFile -ErrorAction SilentlyContinue
                } catch {
                    $result.Success = $false
                    $result.Message = "Compilation test error: $($_.Exception.Message)"
                }
            }
            
            "Check compilation" {
                # More comprehensive compilation check
                $result.Success = $CommandResult.Success -and ($CommandResult.Output -notmatch "error:")
                $errorCount = ($CommandResult.Output -split "`n" | Where-Object { $_ -match "error:" }).Count
                $result.Message = "Compilation check: $errorCount errors found"
                $result.Details = @{ ErrorCount = $errorCount }
            }
            
            "Verify output files" {
                # Check if expected output files were created
                $expectedFiles = @(".lake/build")
                $foundFiles = $expectedFiles | Where-Object { Test-Path $_ }
                $result.Success = $foundFiles.Count -eq $expectedFiles.Count
                $result.Message = "Output files: $($foundFiles.Count)/$($expectedFiles.Count) found"
                $result.Details = @{ ExpectedFiles = $expectedFiles; FoundFiles = $foundFiles }
            }
            
            "Full compilation test" {
                # Test full project compilation
                try {
                    $testOutput = & lake build 2>&1
                    $errorLines = $testOutput | Where-Object { $_ -match "error:" }
                    $warningLines = $testOutput | Where-Object { $_ -match "warning:" }
                    
                    $result.Success = $LASTEXITCODE -eq 0 -and $errorLines.Count -eq 0
                    $result.Message = "Full compilation: $($errorLines.Count) errors, $($warningLines.Count) warnings"
                    $result.Details = @{ 
                        Errors = $errorLines.Count
                        Warnings = $warningLines.Count
                        ExitCode = $LASTEXITCODE
                    }
                } catch {
                    $result.Success = $false
                    $result.Message = "Full compilation test failed: $($_.Exception.Message)"
                }
            }
            
            "Import validation" {
                # Test if imports work correctly
                $importTest = @"
import Std
import Mathlib.Tactic.Basic

theorem import_test : True := by trivial
"@
                $importFile = "temp_import_validation.lean"
                
                try {
                    [System.IO.File]::WriteAllText($importFile, $importTest)
                    $importOutput = & lean $importFile 2>&1
                    $result.Success = $LASTEXITCODE -eq 0
                    $result.Message = if ($result.Success) { "Import validation passed" } else { "Import validation failed" }
                    Remove-Item $importFile -ErrorAction SilentlyContinue
                } catch {
                    $result.Success = $false
                    $result.Message = "Import validation error: $($_.Exception.Message)"
                }
            }
            
            "All imports test" {
                # Test various import combinations
                $importCombos = @(
                    "import Std",
                    "import Mathlib.Tactic.Basic",
                    "import Mathlib.Data.Nat.Basic"
                )
                
                $passedTests = 0
                foreach ($import in $importCombos) {
                    $testContent = "$import`n`ntheorem test_$($passedTests) : True := trivial"
                    $testFile = "temp_import_test_$passedTests.lean"
                    
                    try {
                        [System.IO.File]::WriteAllText($testFile, $testContent)
                        $testOutput = & lean $testFile 2>&1
                        if ($LASTEXITCODE -eq 0) { $passedTests++ }
                        Remove-Item $testFile -ErrorAction SilentlyContinue
                    } catch { }
                }
                
                $result.Success = $passedTests -eq $importCombos.Count
                $result.Message = "Import tests: $passedTests/$($importCombos.Count) passed"
                $result.Details = @{ PassedTests = $passedTests; TotalTests = $importCombos.Count }
            }
            
            "Complete build test" {
                # Comprehensive build validation
                try {
                    $buildOutput = & lake build 2>&1
                    $cleanOutput = & lake clean 2>&1
                    $rebuildOutput = & lake build 2>&1
                    
                    $buildSuccess = $LASTEXITCODE -eq 0
                    $hasErrors = ($rebuildOutput | Where-Object { $_ -match "error:" }).Count -gt 0
                    
                    $result.Success = $buildSuccess -and !$hasErrors
                    $result.Message = "Complete build test: $(if($result.Success) {'passed'} else {'failed'})"
                    $result.Details = @{ 
                        BuildSuccess = $buildSuccess
                        HasErrors = $hasErrors
                        RebuildExitCode = $LASTEXITCODE
                    }
                } catch {
                    $result.Success = $false
                    $result.Message = "Complete build test error: $($_.Exception.Message)"
                }
            }
            
            "Performance validation" {
                # Check if build performance is acceptable
                $buildTime = $CommandResult.Duration.TotalSeconds
                $acceptableTime = $StageConfig.Timeout * 0.8  # 80% of timeout is acceptable
                
                $result.Success = $buildTime -lt $acceptableTime
                $result.Message = "Build time: $($buildTime.ToString('F1'))s (limit: $($acceptableTime.ToString('F1'))s)"
                $result.Details = @{ 
                    BuildTime = $buildTime
                    TimeLimit = $acceptableTime
                    PerformanceRatio = $buildTime / $acceptableTime
                }
            }
            
            "Full system test" {
                # Ultimate validation - everything should work
                $systemTests = @(
                    @{ Name = "Lean compilation"; Command = "lean --version" },
                    @{ Name = "Lake functionality"; Command = "lake --version" },
                    @{ Name = "Project build"; Command = "lake build" },
                    @{ Name = "Import test"; Command = "echo 'import Std' | lake env lean" }
                )
                
                $passedTests = 0
                $totalTests = $systemTests.Count
                
                foreach ($test in $systemTests) {
                    try {
                        $testOutput = Invoke-Expression $test.Command 2>&1
                        if ($LASTEXITCODE -eq 0) { $passedTests++ }
                    } catch { }
                }
                
                $result.Success = $passedTests -eq $totalTests
                $result.Message = "System tests: $passedTests/$totalTests passed"
                $result.Details = @{ PassedTests = $passedTests; TotalTests = $totalTests }
            }
            
            default {
                $result.Success = $true
                $result.Message = "Unknown validation check - skipping"
            }
        }
        
        if ($result.Success) {
            Write-Host "   ✅ $($result.Message)" -ForegroundColor Green
        } else {
            Write-Host "   ❌ $($result.Message)" -ForegroundColor Red
        }
        
        $results += $result
    }
    
    $overallSuccess = ($results | Where-Object { $_.Success }).Count / $results.Count
    return @{
        OverallSuccess = $overallSuccess -ge $retryConfig.PartialSuccessThreshold
        SuccessRate = $overallSuccess
        Results = $results
        FailedChecks = $results | Where-Object { !$_.Success }
    }
}

function Calculate-RetryDelay {
    param([int]$AttemptNumber, [hashtable]$PreviousResult)
    
    $baseDelay = $retryConfig.BaseDelaySeconds
    $backoffDelay = $baseDelay * [math]::Pow($retryConfig.BackoffMultiplier, $AttemptNumber - 1)
    $maxDelay = $retryConfig.MaxDelaySeconds
    
    # Add jitter to prevent thundering herd
    $jitter = Get-Random -Minimum 0.8 -Maximum 1.2
    $finalDelay = [math]::Min($backoffDelay * $jitter, $maxDelay)
    
    # Adjust based on previous result
    if ($PreviousResult -and $PreviousResult.Duration) {
        $durationMinutes = $PreviousResult.Duration.TotalMinutes
        if ($durationMinutes -gt 10) {
            # If previous attempt took very long, wait longer
            $finalDelay = $finalDelay * 1.5
        }
    }
    
    return [int]$finalDelay
}

function Execute-StagedRetry {
    param([string]$Operation, [string]$Strategy)
    
    Write-Host "🔄 STAGED RETRY SYSTEM INITIATED" -ForegroundColor Cyan
    Write-Host "Operation: $Operation | Strategy: $Strategy | Max Retries: $MaxRetries" -ForegroundColor Gray
    Write-Host "="*60 -ForegroundColor Cyan
    
    $retrySession = @{
        StartTime = Get-Date
        Operation = $Operation
        Strategy = $Strategy
        Attempts = @()
        FinalResult = @{}
        TotalDuration = $null
    }
    
    $stages = $retryConfig.RetryStrategies[$Strategy].Stages
    $currentAttempt = 0
    $lastResult = $null
    
    foreach ($stage in $stages) {
        $currentAttempt++
        
        if ($currentAttempt -gt $MaxRetries) {
            Write-Host "⏰ Maximum retry attempts reached ($MaxRetries)" -ForegroundColor Red
            break
        }
        
        Write-Host "`n🎯 ATTEMPT $currentAttempt/$MaxRetries - Stage: $stage" -ForegroundColor Yellow
        Write-Host "-"*40 -ForegroundColor Yellow
        
        # Calculate retry delay
        if ($currentAttempt -gt 1) {
            $delay = Calculate-RetryDelay $currentAttempt $lastResult
            Write-Host "⏱️ Waiting $delay seconds before retry..." -ForegroundColor Gray
            Start-Sleep -Seconds $delay
        }
        
        $attemptStart = Get-Date
        $stageConfig = Get-RetryStageConfiguration $Strategy $stage $Operation
        
        $attemptResult = @{
            AttemptNumber = $currentAttempt
            Stage = $stage
            StartTime = $attemptStart
            StageConfig = $stageConfig
            PreConditionsResult = @{}
            CommandResult = @{}
            ValidationResult = @{}
            OverallSuccess = $false
            Duration = $null
        }
        
        # Execute pre-conditions
        Write-Host "📋 Checking preconditions..." -ForegroundColor Cyan
        $attemptResult.PreConditionsResult = Execute-PreConditions $stageConfig.PreConditions
        
        if (!$attemptResult.PreConditionsResult.OverallSuccess) {
            Write-Host "❌ Preconditions failed - skipping stage" -ForegroundColor Red
            $attemptResult.OverallSuccess = $false
        } else {
            # Execute main command
            Write-Host "⚡ Executing main operation..." -ForegroundColor Cyan
            $attemptResult.CommandResult = Execute-StageCommand $stageConfig $currentAttempt
            
            if ($attemptResult.CommandResult.Success) {
                # Execute post-validation
                Write-Host "🔬 Running validation checks..." -ForegroundColor Cyan
                $attemptResult.ValidationResult = Execute-PostValidation $stageConfig.PostValidation $attemptResult.CommandResult
                
                $attemptResult.OverallSuccess = $attemptResult.ValidationResult.OverallSuccess
                
                if ($attemptResult.OverallSuccess) {
                    Write-Host "🎉 STAGE COMPLETED SUCCESSFULLY!" -ForegroundColor Green
                    $retrySession.FinalResult = $attemptResult
                    break
                } elseif ($ContinueOnPartialSuccess -and $attemptResult.ValidationResult.SuccessRate -gt 0.5) {
                    Write-Host "⚠️ Partial success detected - continuing to next stage" -ForegroundColor Yellow
                }
            } else {
                $attemptResult.OverallSuccess = $false
                Write-Host "❌ Command execution failed" -ForegroundColor Red
            }
        }
        
        $attemptResult.Duration = (Get-Date) - $attemptStart
        $retrySession.Attempts += $attemptResult
        $lastResult = $attemptResult
        
        Write-Host "📊 Attempt $currentAttempt result: $(if($attemptResult.OverallSuccess) {'SUCCESS'} else {'FAILED'})" -ForegroundColor $(if($attemptResult.OverallSuccess) {'Green'} else {'Red'})
    }
    
    $retrySession.TotalDuration = (Get-Date) - $retrySession.StartTime
    
    # Generate session summary
    Write-Host "`n"+"="*60 -ForegroundColor Cyan
    Write-Host "🏁 STAGED RETRY SESSION COMPLETED" -ForegroundColor Cyan
    Write-Host "="*60 -ForegroundColor Cyan
    
    $successfulAttempts = $retrySession.Attempts | Where-Object { $_.OverallSuccess }
    $hasSuccessfulResult = $successfulAttempts.Count -gt 0
    
    Write-Host "📊 SESSION SUMMARY:" -ForegroundColor Yellow
    Write-Host "   Total Attempts: $($retrySession.Attempts.Count)" -ForegroundColor White
    Write-Host "   Successful: $($successfulAttempts.Count)" -ForegroundColor Green
    Write-Host "   Failed: $($retrySession.Attempts.Count - $successfulAttempts.Count)" -ForegroundColor Red
    Write-Host "   Total Duration: $($retrySession.TotalDuration.TotalMinutes.ToString('F1')) minutes" -ForegroundColor White
    Write-Host "   Final Status: $(if($hasSuccessfulResult) {'SUCCESS'} else {'FAILED'})" -ForegroundColor $(if($hasSuccessfulResult) {'Green'} else {'Red'})
    
    if ($hasSuccessfulResult) {
        $successfulStage = $successfulAttempts[0].Stage
        Write-Host "   Successful Stage: $successfulStage" -ForegroundColor Green
        Write-Host "   Success Rate: $($successfulAttempts[0].ValidationResult.SuccessRate.ToString('P1'))" -ForegroundColor Green
    }
    
    return $retrySession
}

# Main entry point
function Start-StagedRetry {
    param([string]$TargetOperation = $Operation, [string]$RetryStrategyName = $RetryStrategy)
    
    return Execute-StagedRetry $TargetOperation $RetryStrategyName
}

Export-ModuleMember -Function Start-StagedRetry