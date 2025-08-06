# Mathlib Recovery System - Quick Start Script
# Easy access point for common recovery operations

param(
    [string]$Action = "Menu",
    [string]$Operation = "build",
    [string]$Strategy = "Smart",
    [switch]$Help
)

if ($Help) {
    Write-Host @"
🚨 Mathlib Auto Recovery System - Quick Start

USAGE:
  .\QuickStart.ps1 [options]

ACTIONS:
  -Action Menu        Show interactive menu (default)
  -Action Recover     Start automatic recovery
  -Action Status      Show system status
  -Action Cleanup     Clean up old branches
  -Action Test        Run system test
  -Action Help        Show this help

EXAMPLES:
  .\QuickStart.ps1                                    # Interactive menu
  .\QuickStart.ps1 -Action Recover -Strategy Smart    # Quick recovery
  .\QuickStart.ps1 -Action Status                     # Show status
  .\QuickStart.ps1 -Action Cleanup                    # Clean old branches

RECOVERY STRATEGIES:
  Conservative - Safe approach, minimal changes
  Smart        - Balanced approach (recommended)
  Aggressive   - Fast approach, higher risk

"@ -ForegroundColor Cyan
    return
}

function Show-MainMenu {
    Clear-Host
    Write-Host @"
🚨 Mathlib Auto Recovery System 🚨
================================

Current Directory: $(Get-Location)
Current Time: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')

"@ -ForegroundColor Cyan

    # Check git repository status
    try {
        $currentBranch = & git rev-parse --abbrev-ref HEAD 2>$null
        $hasChanges = (& git status --porcelain 2>$null).Count -gt 0
        
        Write-Host "Git Status:" -ForegroundColor Yellow
        Write-Host "  Current Branch: $currentBranch" -ForegroundColor White
        Write-Host "  Uncommitted Changes: $(if($hasChanges) {'Yes'} else {'No'})" -ForegroundColor $(if($hasChanges) {'Red'} else {'Green'})
    } catch {
        Write-Host "⚠️ Not a git repository" -ForegroundColor Red
    }

    Write-Host "`nSelect an option:" -ForegroundColor Yellow
    Write-Host "1. 🔄 Start Automatic Recovery (Smart Strategy)" -ForegroundColor Green
    Write-Host "2. 🛡️ Start Conservative Recovery" -ForegroundColor Cyan
    Write-Host "3. ⚡ Start Aggressive Recovery" -ForegroundColor Magenta
    Write-Host "4. 📊 Show System Status" -ForegroundColor White
    Write-Host "5. 🧹 Clean Up Old Branches" -ForegroundColor Yellow
    Write-Host "6. 🧪 Run System Test" -ForegroundColor Blue
    Write-Host "7. 📚 Show Documentation" -ForegroundColor Gray
    Write-Host "8. 🚪 Exit" -ForegroundColor Red
    
    Write-Host "`nChoice (1-8): " -ForegroundColor Yellow -NoNewline
    $choice = Read-Host
    
    return $choice
}

function Execute-Recovery {
    param([string]$RecoveryStrategy)
    
    Write-Host "🚨 Starting Recovery with $RecoveryStrategy strategy..." -ForegroundColor Yellow
    
    try {
        $scriptPath = Split-Path -Parent $MyInvocation.MyCommand.Definition
        $orchestratorPath = "$scriptPath\RecoveryOrchestrator.ps1"
        
        if (!(Test-Path $orchestratorPath)) {
            throw "Recovery orchestrator not found: $orchestratorPath"
        }
        
        & powershell.exe -ExecutionPolicy Bypass -File $orchestratorPath -Operation $Operation -RecoveryStrategy $RecoveryStrategy -AutoMode -Verbose
        
    } catch {
        Write-Host "❌ Recovery failed: $($_.Exception.Message)" -ForegroundColor Red
    }
    
    Write-Host "`nPress Enter to continue..." -ForegroundColor Gray
    Read-Host
}

function Show-SystemStatus {
    Write-Host "📊 System Status Check" -ForegroundColor Cyan
    Write-Host "=====================" -ForegroundColor Cyan
    
    # Git repository status
    try {
        $gitStatus = & git status --porcelain 2>$null
        $currentBranch = & git rev-parse --abbrev-ref HEAD 2>$null
        $currentCommit = (& git rev-parse HEAD 2>$null).Substring(0,8)
        
        Write-Host "`n🔧 Git Repository:" -ForegroundColor Yellow
        Write-Host "  Current Branch: $currentBranch" -ForegroundColor White
        Write-Host "  Current Commit: $currentCommit" -ForegroundColor White
        Write-Host "  Working Tree: $(if($gitStatus) {'Has changes'} else {'Clean'})" -ForegroundColor $(if($gitStatus) {'Yellow'} else {'Green'})
    } catch {
        Write-Host "❌ Git not available or not a repository" -ForegroundColor Red
    }
    
    # Lean/Lake status
    try {
        $leanVersion = & lean --version 2>$null
        Write-Host "`n🔧 Lean Environment:" -ForegroundColor Yellow
        Write-Host "  Lean Version: $leanVersion" -ForegroundColor White
        
        $lakeVersion = & lake --version 2>$null
        Write-Host "  Lake Version: $lakeVersion" -ForegroundColor White
        
        $lakefile = Test-Path "lakefile.lean"
        Write-Host "  Lakefile Present: $(if($lakefile) {'Yes'} else {'No'})" -ForegroundColor $(if($lakefile) {'Green'} else {'Red'})
        
    } catch {
        Write-Host "❌ Lean/Lake not available" -ForegroundColor Red
    }
    
    # Recovery system status
    Write-Host "`n🚨 Recovery System:" -ForegroundColor Yellow
    $scriptPath = Split-Path -Parent $MyInvocation.MyCommand.Definition
    $modules = @(
        "AutoRecoverySystem.ps1",
        "ProblemIsolation.ps1", 
        "StagedRetrySystem.ps1",
        "BranchManager.ps1",
        "RecoveryOrchestrator.ps1"
    )
    
    foreach ($module in $modules) {
        $modulePath = "$scriptPath\$module"
        $exists = Test-Path $modulePath
        Write-Host "  $module`: $(if($exists) {'✅ Available'} else {'❌ Missing'})" -ForegroundColor $(if($exists) {'Green'} else {'Red'})
    }
    
    # Recovery branches
    try {
        $recoveryBranches = & git branch | Where-Object { $_ -match "recovery|safety|isolation|milestone" }
        Write-Host "`n🌿 Recovery Branches: $($recoveryBranches.Count)" -ForegroundColor Yellow
        
        if ($recoveryBranches.Count -gt 0) {
            $recoveryBranches | Select-Object -First 5 | ForEach-Object {
                Write-Host "  $($_.Trim())" -ForegroundColor White
            }
            if ($recoveryBranches.Count -gt 5) {
                Write-Host "  ... and $($recoveryBranches.Count - 5) more" -ForegroundColor Gray
            }
        }
    } catch { }
    
    Write-Host "`nPress Enter to continue..." -ForegroundColor Gray
    Read-Host
}

function Execute-Cleanup {
    Write-Host "🧹 Cleaning Up Old Branches..." -ForegroundColor Yellow
    
    try {
        $scriptPath = Split-Path -Parent $MyInvocation.MyCommand.Definition
        $branchManagerPath = "$scriptPath\BranchManager.ps1"
        
        if (!(Test-Path $branchManagerPath)) {
            throw "Branch manager not found: $branchManagerPath"
        }
        
        & powershell.exe -ExecutionPolicy Bypass -File $branchManagerPath -CleanupOldBranches -Verbose
        
    } catch {
        Write-Host "❌ Cleanup failed: $($_.Exception.Message)" -ForegroundColor Red
    }
    
    Write-Host "`nPress Enter to continue..." -ForegroundColor Gray
    Read-Host
}

function Execute-SystemTest {
    Write-Host "🧪 Running System Test..." -ForegroundColor Blue
    
    $testResults = @{
        GitRepository = $false
        LeanAvailable = $false
        LakeAvailable = $false
        RecoveryModules = $false
        BasicCompilation = $false
    }
    
    # Test Git repository
    try {
        & git status 2>$null | Out-Null
        $testResults.GitRepository = $LASTEXITCODE -eq 0
    } catch { }
    
    # Test Lean
    try {
        & lean --version 2>$null | Out-Null
        $testResults.LeanAvailable = $LASTEXITCODE -eq 0
    } catch { }
    
    # Test Lake
    try {
        & lake --version 2>$null | Out-Null
        $testResults.LakeAvailable = $LASTEXITCODE -eq 0
    } catch { }
    
    # Test recovery modules
    $scriptPath = Split-Path -Parent $MyInvocation.MyCommand.Definition
    $requiredModules = @(
        "AutoRecoverySystem.ps1",
        "ProblemIsolation.ps1",
        "StagedRetrySystem.ps1", 
        "BranchManager.ps1",
        "RecoveryOrchestrator.ps1"
    )
    
    $moduleCount = 0
    foreach ($module in $requiredModules) {
        if (Test-Path "$scriptPath\$module") {
            $moduleCount++
        }
    }
    $testResults.RecoveryModules = $moduleCount -eq $requiredModules.Count
    
    # Test basic compilation
    try {
        $testContent = "theorem quick_test : True := trivial"
        [System.IO.File]::WriteAllText("quick_test.lean", $testContent)
        & lean quick_test.lean 2>$null | Out-Null
        $testResults.BasicCompilation = $LASTEXITCODE -eq 0
        Remove-Item "quick_test.lean" -ErrorAction SilentlyContinue
    } catch { }
    
    # Display results
    Write-Host "`n📋 Test Results:" -ForegroundColor Yellow
    foreach ($test in $testResults.GetEnumerator()) {
        $status = if ($test.Value) { "✅ PASS" } else { "❌ FAIL" }
        $color = if ($test.Value) { "Green" } else { "Red" }
        Write-Host "  $($test.Key): $status" -ForegroundColor $color
    }
    
    $passedTests = ($testResults.Values | Where-Object { $_ }).Count
    $totalTests = $testResults.Count
    
    Write-Host "`n📊 Overall: $passedTests/$totalTests tests passed" -ForegroundColor $(if($passedTests -eq $totalTests) {'Green'} else {'Yellow'})
    
    if ($passedTests -eq $totalTests) {
        Write-Host "🎉 System is ready for recovery operations!" -ForegroundColor Green
    } else {
        Write-Host "⚠️ Some components need attention before using recovery system" -ForegroundColor Yellow
    }
    
    Write-Host "`nPress Enter to continue..." -ForegroundColor Gray
    Read-Host
}

function Show-Documentation {
    Write-Host "📚 Recovery System Documentation" -ForegroundColor Cyan
    Write-Host "===============================" -ForegroundColor Cyan
    
    $scriptPath = Split-Path -Parent $MyInvocation.MyCommand.Definition
    $readmePath = "$scriptPath\README.md"
    
    if (Test-Path $readmePath) {
        Write-Host "`n📄 Full documentation available at:" -ForegroundColor Yellow
        Write-Host "   $readmePath" -ForegroundColor White
        Write-Host "`nWould you like to open the documentation? (y/n): " -ForegroundColor Yellow -NoNewline
        $openDoc = Read-Host
        
        if ($openDoc -eq 'y' -or $openDoc -eq 'Y') {
            try {
                Start-Process $readmePath
            } catch {
                Write-Host "❌ Could not open documentation automatically" -ForegroundColor Red
                Write-Host "Please open manually: $readmePath" -ForegroundColor Yellow
            }
        }
    } else {
        Write-Host "❌ Documentation not found at $readmePath" -ForegroundColor Red
    }
    
    Write-Host "`n📖 Quick Reference:" -ForegroundColor Yellow
    Write-Host @"
Recovery Strategies:
  Conservative - Safe, minimal changes, manual confirmation
  Smart        - Balanced, automatic decisions (recommended)  
  Aggressive   - Fast, higher risk tolerance

Common Commands:
  .\QuickStart.ps1 -Action Recover -Strategy Smart
  .\QuickStart.ps1 -Action Status
  .\QuickStart.ps1 -Action Cleanup

Emergency Commands:
  git reset --hard HEAD~1        # Manual rollback
  git branch -D recovery_*       # Delete recovery branches
  .\RecoveryOrchestrator.ps1 -DryRun  # Test without changes
"@ -ForegroundColor White
    
    Write-Host "`nPress Enter to continue..." -ForegroundColor Gray
    Read-Host
}

# Main execution logic
switch ($Action) {
    "Recover" {
        Execute-Recovery $Strategy
    }
    
    "Status" {
        Show-SystemStatus
    }
    
    "Cleanup" {
        Execute-Cleanup
    }
    
    "Test" {
        Execute-SystemTest
    }
    
    "Menu" {
        do {
            $choice = Show-MainMenu
            
            switch ($choice) {
                "1" { Execute-Recovery "Smart" }
                "2" { Execute-Recovery "Conservative" }
                "3" { Execute-Recovery "Aggressive" }
                "4" { Show-SystemStatus }
                "5" { Execute-Cleanup }
                "6" { Execute-SystemTest }
                "7" { Show-Documentation }
                "8" { 
                    Write-Host "👋 Goodbye!" -ForegroundColor Green
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
        Write-Host "❌ Unknown action: $Action" -ForegroundColor Red
        Write-Host "Use -Help to see available options" -ForegroundColor Yellow
    }
}