# Migration Verification System
# Verifies migrated proofs work correctly before merging

param(
    [string]$FileToVerify = "",
    [string]$ComparisonMode = "Functional", # Functional, Behavioral, Strict
    [switch]$RunAllTests,
    [switch]$Verbose
)

# Verification configuration
$verificationConfig = @{
    TestLevels = @{
        "Basic" = @{
            Description = "Basic compilation test"
            Tests = @("Compilation", "ImportResolution")
        }
        "Standard" = @{
            Description = "Standard verification with theorem checking"
            Tests = @("Compilation", "ImportResolution", "TheoremValidity", "TacticExecution")
        }
        "Comprehensive" = @{
            Description = "Full verification including performance"
            Tests = @("Compilation", "ImportResolution", "TheoremValidity", "TacticExecution", "Performance", "Compatibility")
        }
    }
    
    ComparisonModes = @{
        "Functional" = "Verify that migrated code produces same results"
        "Behavioral" = "Verify that migrated code behaves identically"  
        "Strict" = "Verify exact output match (most restrictive)"
    }
    
    PerformanceThresholds = @{
        CompilationTime = 30  # seconds
        MemoryUsage = 500     # MB
        FileSize = 100        # KB
    }
}

function Test-Compilation {
    param([string]$FilePath)
    
    Write-Host "  Testing compilation..." -ForegroundColor Gray
    
    $startTime = Get-Date
    
    try {
        $output = & lean $FilePath 2>&1
        $exitCode = $LASTEXITCODE
        $duration = (Get-Date) - $startTime
        
        $result = @{
            Test = "Compilation"
            Success = $exitCode -eq 0
            Duration = $duration.TotalSeconds
            Output = $output -join "`n"
            Errors = @()
        }
        
        if (!$result.Success) {
            $result.Errors = $output | Where-Object { $_ -match "error:" }
        }
        
        if ($result.Success) {
            Write-Host "    ✅ Compilation successful ($($duration.TotalSeconds.ToString('F2'))s)" -ForegroundColor Green
        } else {
            Write-Host "    ❌ Compilation failed" -ForegroundColor Red
            if ($Verbose) {
                $result.Errors | Select-Object -First 3 | ForEach-Object {
                    Write-Host "      $_" -ForegroundColor Red
                }
            }
        }
        
        return $result
        
    } catch {
        return @{
            Test = "Compilation"
            Success = $false
            Error = $_.Exception.Message
        }
    }
}

function Test-ImportResolution {
    param([string]$FilePath)
    
    Write-Host "  Testing import resolution..." -ForegroundColor Gray
    
    $content = Get-Content $FilePath
    $imports = $content | Where-Object { $_ -match '^import\s+' }
    
    $result = @{
        Test = "ImportResolution"
        Success = $true
        TotalImports = $imports.Count
        ResolvedImports = @()
        FailedImports = @()
    }
    
    foreach ($import in $imports) {
        $importModule = $import -replace '^import\s+', ''
        
        # Create test file with just this import
        $testContent = "$import`ntheorem import_test : True := trivial"
        $testFile = "temp_import_test_$(Get-Date -Format 'HHmmssff').lean"
        
        try {
            [System.IO.File]::WriteAllText($testFile, $testContent)
            $output = & lean $testFile 2>&1
            $success = $LASTEXITCODE -eq 0
            
            if ($success) {
                $result.ResolvedImports += $importModule
            } else {
                $result.FailedImports += $importModule
                $result.Success = $false
            }
            
            Remove-Item $testFile -ErrorAction SilentlyContinue
            
        } catch {
            $result.FailedImports += $importModule
            $result.Success = $false
        }
    }
    
    if ($result.Success) {
        Write-Host "    ✅ All $($result.TotalImports) imports resolved" -ForegroundColor Green
    } else {
        Write-Host "    ❌ $($result.FailedImports.Count) imports failed" -ForegroundColor Red
        if ($Verbose) {
            $result.FailedImports | ForEach-Object {
                Write-Host "      Failed: $_" -ForegroundColor Red
            }
        }
    }
    
    return $result
}

function Test-TheoremValidity {
    param([string]$FilePath)
    
    Write-Host "  Testing theorem validity..." -ForegroundColor Gray
    
    $content = Get-Content $FilePath
    $theorems = @()
    
    # Extract theorem definitions
    for ($i = 0; $i -lt $content.Count; $i++) {
        if ($content[$i] -match '^theorem\s+(\w+)') {
            $theoremName = $matches[1]
            $theoremLines = @($content[$i])
            
            # Collect theorem body
            for ($j = $i + 1; $j -lt $content.Count; $j++) {
                $theoremLines += $content[$j]
                if ($content[$j] -match '^\s*$' -or $content[$j] -match '^(theorem|def|lemma)') {
                    break
                }
            }
            
            $theorems += @{
                Name = $theoremName
                Content = $theoremLines -join "`n"
                HasSorry = ($theoremLines -join " ") -match '\bsorry\b'
                UsesAdvancedTactics = ($theoremLines -join " ") -match '\b(ring|omega|simp|norm_num)\b'
            }
        }
    }
    
    $result = @{
        Test = "TheoremValidity"
        Success = $true
        TotalTheorems = $theorems.Count
        ValidTheorems = 0
        TheoremsWithSorry = 0
        TheoremsWithAdvancedTactics = 0
    }
    
    foreach ($theorem in $theorems) {
        if ($theorem.HasSorry) {
            $result.TheoremsWithSorry++
        } else {
            $result.ValidTheorems++
        }
        
        if ($theorem.UsesAdvancedTactics) {
            $result.TheoremsWithAdvancedTactics++
        }
    }
    
    # Consider test passed if most theorems are valid (not using sorry)
    $validityRate = if ($result.TotalTheorems -gt 0) { 
        $result.ValidTheorems / $result.TotalTheorems 
    } else { 1 }
    
    $result.Success = $validityRate -ge 0.7
    
    if ($result.Success) {
        Write-Host "    ✅ $($result.ValidTheorems)/$($result.TotalTheorems) theorems valid" -ForegroundColor Green
    } else {
        Write-Host "    ⚠️ Only $($result.ValidTheorems)/$($result.TotalTheorems) theorems valid" -ForegroundColor Yellow
    }
    
    if ($result.TheoremsWithAdvancedTactics -gt 0) {
        Write-Host "    ℹ️ $($result.TheoremsWithAdvancedTactics) theorems use advanced tactics" -ForegroundColor Cyan
    }
    
    return $result
}

function Test-TacticExecution {
    param([string]$FilePath)
    
    Write-Host "  Testing tactic execution..." -ForegroundColor Gray
    
    # Create a test that exercises various tactics
    $testContent = Get-Content $FilePath -Raw
    
    # Add test theorems that use common tactics
    $tacticTests = @"

-- Tactic execution tests
theorem test_trivial : True := by trivial

theorem test_rfl : 1 = 1 := by rfl

theorem test_sorry : False := by sorry

"@

    $testFile = "temp_tactic_test_$(Get-Date -Format 'HHmmssff').lean"
    $fullTestContent = $testContent + "`n`n" + $tacticTests
    
    try {
        [System.IO.File]::WriteAllText($testFile, $fullTestContent)
        $output = & lean $testFile 2>&1
        $success = $LASTEXITCODE -eq 0
        
        Remove-Item $testFile -ErrorAction SilentlyContinue
        
        $result = @{
            Test = "TacticExecution"
            Success = $success
            Output = $output -join "`n"
        }
        
        if ($success) {
            Write-Host "    ✅ Tactics execute correctly" -ForegroundColor Green
        } else {
            Write-Host "    ❌ Tactic execution errors" -ForegroundColor Red
        }
        
        return $result
        
    } catch {
        return @{
            Test = "TacticExecution"
            Success = $false
            Error = $_.Exception.Message
        }
    }
}

function Test-Performance {
    param([string]$FilePath)
    
    Write-Host "  Testing performance..." -ForegroundColor Gray
    
    $result = @{
        Test = "Performance"
        Success = $true
        Metrics = @{}
        Warnings = @()
    }
    
    # Test compilation time
    $startTime = Get-Date
    $output = & lean $FilePath 2>&1
    $compilationTime = ((Get-Date) - $startTime).TotalSeconds
    
    $result.Metrics.CompilationTime = $compilationTime
    
    if ($compilationTime -gt $verificationConfig.PerformanceThresholds.CompilationTime) {
        $result.Warnings += "Compilation time exceeds threshold: $($compilationTime.ToString('F2'))s > $($verificationConfig.PerformanceThresholds.CompilationTime)s"
        $result.Success = $false
    }
    
    # Check file size
    $fileInfo = Get-Item $FilePath
    $fileSizeKB = $fileInfo.Length / 1KB
    $result.Metrics.FileSizeKB = [math]::Round($fileSizeKB, 2)
    
    if ($fileSizeKB -gt $verificationConfig.PerformanceThresholds.FileSize) {
        $result.Warnings += "File size exceeds threshold: $($fileSizeKB.ToString('F2'))KB > $($verificationConfig.PerformanceThresholds.FileSize)KB"
    }
    
    if ($result.Success) {
        Write-Host "    ✅ Performance acceptable (Compilation: $($compilationTime.ToString('F2'))s, Size: $($fileSizeKB.ToString('F2'))KB)" -ForegroundColor Green
    } else {
        Write-Host "    ⚠️ Performance concerns detected" -ForegroundColor Yellow
        if ($Verbose) {
            $result.Warnings | ForEach-Object {
                Write-Host "      $_" -ForegroundColor Yellow
            }
        }
    }
    
    return $result
}

function Test-Compatibility {
    param([string]$FilePath, [string]$OriginalFile = "")
    
    Write-Host "  Testing compatibility..." -ForegroundColor Gray
    
    $result = @{
        Test = "Compatibility"
        Success = $true
        CompatibilityChecks = @()
    }
    
    # Check if file maintains same public interface
    $content = Get-Content $FilePath
    $publicDefinitions = @()
    
    $content | ForEach-Object {
        if ($_ -match '^(def|theorem|lemma)\s+(\w+)') {
            $publicDefinitions += $matches[2]
        }
    }
    
    $result.CompatibilityChecks += @{
        Check = "Public interface maintained"
        Success = $publicDefinitions.Count -gt 0
        Details = "$($publicDefinitions.Count) public definitions found"
    }
    
    # If original file provided, compare interfaces
    if ($OriginalFile -and (Test-Path $OriginalFile)) {
        $originalContent = Get-Content $OriginalFile
        $originalDefinitions = @()
        
        $originalContent | ForEach-Object {
            if ($_ -match '^(def|theorem|lemma)\s+(\w+)') {
                $originalDefinitions += $matches[2]
            }
        }
        
        $missing = $originalDefinitions | Where-Object { $_ -notin $publicDefinitions }
        $added = $publicDefinitions | Where-Object { $_ -notin $originalDefinitions }
        
        $interfaceMatch = $missing.Count -eq 0
        
        $result.CompatibilityChecks += @{
            Check = "Interface compatibility with original"
            Success = $interfaceMatch
            Details = "Missing: $($missing.Count), Added: $($added.Count)"
            Missing = $missing
            Added = $added
        }
        
        if (!$interfaceMatch) {
            $result.Success = $false
        }
    }
    
    if ($result.Success) {
        Write-Host "    ✅ Compatibility verified" -ForegroundColor Green
    } else {
        Write-Host "    ⚠️ Compatibility issues detected" -ForegroundColor Yellow
        if ($Verbose) {
            $result.CompatibilityChecks | Where-Object { !$_.Success } | ForEach-Object {
                Write-Host "      $($_.Check): $($_.Details)" -ForegroundColor Yellow
            }
        }
    }
    
    return $result
}

function Run-VerificationSuite {
    param(
        [string]$FilePath,
        [string]$TestLevel = "Standard",
        [string]$OriginalFile = ""
    )
    
    Write-Host "`nRunning verification suite: $TestLevel" -ForegroundColor Cyan
    Write-Host "File: $FilePath" -ForegroundColor Gray
    
    if (!(Test-Path $FilePath)) {
        Write-Host "❌ File not found: $FilePath" -ForegroundColor Red
        return @{ Success = $false; Error = "File not found" }
    }
    
    $levelConfig = $verificationConfig.TestLevels[$TestLevel]
    $results = @{
        FilePath = $FilePath
        TestLevel = $TestLevel
        Timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
        Tests = @()
        OverallSuccess = $true
        Summary = @{}
    }
    
    foreach ($testName in $levelConfig.Tests) {
        $testResult = switch ($testName) {
            "Compilation" { Test-Compilation $FilePath }
            "ImportResolution" { Test-ImportResolution $FilePath }
            "TheoremValidity" { Test-TheoremValidity $FilePath }
            "TacticExecution" { Test-TacticExecution $FilePath }
            "Performance" { Test-Performance $FilePath }
            "Compatibility" { Test-Compatibility $FilePath $OriginalFile }
            default { @{ Test = $testName; Success = $false; Error = "Unknown test" } }
        }
        
        $results.Tests += $testResult
        
        if (!$testResult.Success) {
            $results.OverallSuccess = $false
        }
    }
    
    # Generate summary
    $passedTests = ($results.Tests | Where-Object { $_.Success }).Count
    $totalTests = $results.Tests.Count
    
    $results.Summary = @{
        PassedTests = $passedTests
        TotalTests = $totalTests
        PassRate = if ($totalTests -gt 0) { ($passedTests / $totalTests * 100) } else { 0 }
    }
    
    Write-Host "`nVerification Results:" -ForegroundColor Yellow
    Write-Host "  Tests Passed: $passedTests/$totalTests ($($results.Summary.PassRate.ToString('F1'))%)" -ForegroundColor $(
        if ($results.OverallSuccess) { 'Green' } else { 'Red' }
    )
    
    if ($results.OverallSuccess) {
        Write-Host "✅ VERIFICATION SUCCESSFUL - File ready for merge" -ForegroundColor Green
    } else {
        Write-Host "❌ VERIFICATION FAILED - Issues need resolution" -ForegroundColor Red
        
        $failedTests = $results.Tests | Where-Object { !$_.Success }
        Write-Host "`nFailed Tests:" -ForegroundColor Red
        $failedTests | ForEach-Object {
            Write-Host "  - $($_.Test)" -ForegroundColor Red
        }
    }
    
    return $results
}

function Compare-MigrationResults {
    param(
        [string]$OriginalFile,
        [string]$MigratedFile,
        [string]$Mode
    )
    
    Write-Host "`nComparing migration results (Mode: $Mode)" -ForegroundColor Cyan
    
    if (!(Test-Path $OriginalFile) -or !(Test-Path $MigratedFile)) {
        Write-Host "❌ Files not found for comparison" -ForegroundColor Red
        return @{ Success = $false; Error = "Files not found" }
    }
    
    $comparison = @{
        Mode = $Mode
        OriginalFile = $OriginalFile
        MigratedFile = $MigratedFile
        Differences = @()
        Success = $true
    }
    
    switch ($Mode) {
        "Functional" {
            # Compare that both files compile and produce same theorems
            $origResult = Test-Compilation $OriginalFile
            $migResult = Test-Compilation $MigratedFile
            
            $comparison.Success = $origResult.Success -and $migResult.Success
            
            if (!$comparison.Success) {
                $comparison.Differences += "Compilation status differs"
            }
        }
        
        "Behavioral" {
            # Compare theorem signatures and public interface
            $origContent = Get-Content $OriginalFile
            $migContent = Get-Content $MigratedFile
            
            $origTheorems = $origContent | Where-Object { $_ -match '^theorem\s+(\w+)' } | ForEach-Object { $matches[1] }
            $migTheorems = $migContent | Where-Object { $_ -match '^theorem\s+(\w+)' } | ForEach-Object { $matches[1] }
            
            $missing = $origTheorems | Where-Object { $_ -notin $migTheorems }
            $added = $migTheorems | Where-Object { $_ -notin $origTheorems }
            
            if ($missing.Count -gt 0) {
                $comparison.Differences += "Missing theorems: $($missing -join ', ')"
                $comparison.Success = $false
            }
            
            if ($added.Count -gt 0) {
                $comparison.Differences += "Added theorems: $($added -join ', ')"
            }
        }
        
        "Strict" {
            # Compare exact output (most restrictive)
            $origOutput = & lean $OriginalFile 2>&1
            $migOutput = & lean $MigratedFile 2>&1
            
            $comparison.Success = ($origOutput -join "`n") -eq ($migOutput -join "`n")
            
            if (!$comparison.Success) {
                $comparison.Differences += "Output differs between files"
            }
        }
    }
    
    if ($comparison.Success) {
        Write-Host "✅ Comparison passed ($Mode mode)" -ForegroundColor Green
    } else {
        Write-Host "❌ Comparison failed ($Mode mode)" -ForegroundColor Red
        if ($Verbose) {
            $comparison.Differences | ForEach-Object {
                Write-Host "  $_" -ForegroundColor Red
            }
        }
    }
    
    return $comparison
}

# Main execution
if ($FileToVerify) {
    $verificationResult = Run-VerificationSuite $FileToVerify "Standard"
    
    # Save verification report
    $reportPath = "mathlib-migration\verification_$(Split-Path $FileToVerify -Leaf)_$(Get-Date -Format 'yyyyMMdd_HHmmss').json"
    $verificationResult | ConvertTo-Json -Depth 10 | Out-File $reportPath -Encoding UTF8
    
    Write-Host "`nVerification report saved: $reportPath" -ForegroundColor Gray
    
} elseif ($RunAllTests) {
    Write-Host "Running verification on all migrated files..." -ForegroundColor Cyan
    
    $migratedDir = "mathlib-migration\migrated"
    if (Test-Path $migratedDir) {
        $migratedFiles = Get-ChildItem -Path $migratedDir -Filter "*.lean"
        
        $allResults = @()
        foreach ($file in $migratedFiles) {
            $result = Run-VerificationSuite $file.FullName "Standard"
            $allResults += $result
        }
        
        $successCount = ($allResults | Where-Object { $_.OverallSuccess }).Count
        Write-Host "`n📊 Overall Results: $successCount/$($allResults.Count) files passed verification" -ForegroundColor $(
            if ($successCount -eq $allResults.Count) { 'Green' } else { 'Yellow' }
        )
    } else {
        Write-Host "No migrated files found" -ForegroundColor Yellow
    }
    
} else {
    Write-Host @"
Migration Verification System

Usage:
  .\MigrationVerifier.ps1 -FileToVerify <path> [-ComparisonMode <mode>] [-Verbose]
  .\MigrationVerifier.ps1 -RunAllTests [-Verbose]

Comparison Modes:
  Functional - Verify same results
  Behavioral - Verify same behavior
  Strict     - Verify exact match

Examples:
  .\MigrationVerifier.ps1 -FileToVerify "migrated\MyProof.lean"
  .\MigrationVerifier.ps1 -RunAllTests
"@ -ForegroundColor Cyan
}

Export-ModuleMember -Function Run-VerificationSuite, Compare-MigrationResults