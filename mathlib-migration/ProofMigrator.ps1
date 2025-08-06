# Proof Migration Tool for Mathlib
# Gradually migrates proofs from standard Lean to Mathlib-enhanced versions

param(
    [string]$SourceFile,
    [string]$OutputFile = "",
    [string]$MigrationLevel = "Basic", # Basic, Standard, Advanced
    [switch]$DryRun,
    [switch]$Verbose
)

# Migration patterns and rules
$migrationRules = @{
    ImportMappings = @{
        # Basic imports to add
        "Basic" = @(
            "import Mathlib.Tactic.Basic"
        )
        "Standard" = @(
            "import Mathlib.Tactic.Basic",
            "import Mathlib.Data.Nat.Basic",
            "import Mathlib.Data.Int.Basic"
        )
        "Advanced" = @(
            "import Mathlib.Tactic.Basic",
            "import Mathlib.Tactic.Ring",
            "import Mathlib.Tactic.Omega",
            "import Mathlib.Data.Nat.Basic",
            "import Mathlib.Data.Int.Basic",
            "import Mathlib.Data.Real.Basic"
        )
    }
    
    TypeMappings = @{
        # Type conversions
        @{ Pattern = '\bNat\b'; Replacement = 'ℕ'; Unicode = $true },
        @{ Pattern = '\bInt\b'; Replacement = 'ℤ'; Unicode = $true },
        @{ Pattern = '\bReal\b'; Replacement = 'ℝ'; Unicode = $true },
        @{ Pattern = '\bRat\b'; Replacement = 'ℚ'; Unicode = $true }
    }
    
    TacticMappings = @{
        # Tactic improvements
        @{ 
            Pattern = 'sorry'
            Replacement = 'by sorry'
            Condition = 'NotInBy'
        },
        @{
            Pattern = 'exact\s+⟨([^⟩]+)⟩'
            Replacement = 'use $1'
            RequiresImport = 'Mathlib.Tactic.Use'
        },
        @{
            Pattern = 'by\s+sorry'
            Replacement = 'by ring'
            Condition = 'ArithmeticProof'
            RequiresImport = 'Mathlib.Tactic.Ring'
        }
    }
    
    TheoremMappings = @{
        # Common theorem name changes
        @{ Old = 'Nat.add_zero'; New = 'add_zero' },
        @{ Old = 'Nat.zero_add'; New = 'zero_add' },
        @{ Old = 'Nat.add_comm'; New = 'add_comm' },
        @{ Old = 'Nat.add_assoc'; New = 'add_assoc' },
        @{ Old = 'Int.add_zero'; New = 'add_zero' },
        @{ Old = 'Int.zero_add'; New = 'zero_add' }
    }
}

function Analyze-ProofFile {
    param([string]$FilePath)
    
    Write-Host "Analyzing proof file: $FilePath" -ForegroundColor Cyan
    
    if (!(Test-Path $FilePath)) {
        throw "File not found: $FilePath"
    }
    
    $content = Get-Content $FilePath -Raw
    $lines = Get-Content $FilePath
    
    $analysis = @{
        FilePath = $FilePath
        FileName = Split-Path $FilePath -Leaf
        TotalLines = $lines.Count
        Imports = @()
        Definitions = @()
        Theorems = @()
        UsesUnicode = $false
        UsesMathlib = $false
        Complexity = "Simple"
        MigrationCandidates = @()
    }
    
    # Analyze imports
    $analysis.Imports = $lines | Where-Object { $_ -match '^import\s+' }
    $analysis.UsesMathlib = ($analysis.Imports -join " ") -match 'Mathlib'
    
    # Analyze definitions and theorems
    $lines | ForEach-Object {
        if ($_ -match '^def\s+(\w+)') {
            $analysis.Definitions += $matches[1]
        }
        if ($_ -match '^theorem\s+(\w+)') {
            $analysis.Theorems += $matches[1]
        }
    }
    
    # Check for Unicode
    $analysis.UsesUnicode = $content -match '[ℕℤℝℚ∀∃λ→↔⟨⟩‹›]'
    
    # Assess complexity
    $tacticsUsed = @()
    $lines | ForEach-Object {
        if ($_ -match 'by\s+(\w+)') {
            $tacticsUsed += $matches[1]
        }
    }
    
    $analysis.Complexity = if ($tacticsUsed.Count -eq 0) { "Trivial" }
                          elseif ($tacticsUsed.Count -le 3) { "Simple" }
                          elseif ($tacticsUsed.Count -le 10) { "Moderate" }
                          else { "Complex" }
    
    # Identify migration candidates
    foreach ($theorem in $analysis.Theorems) {
        $theoremContent = ""
        $inTheorem = $false
        foreach ($line in $lines) {
            if ($line -match "theorem\s+$theorem") {
                $inTheorem = $true
            }
            if ($inTheorem) {
                $theoremContent += "$line`n"
                if ($line -match '^\s*$' -and $theoremContent.Length -gt 0) {
                    break
                }
            }
        }
        
        # Check if theorem can be migrated
        $canMigrate = $theoremContent -match 'sorry' -or 
                     $theoremContent -notmatch 'Mathlib' -or
                     !$analysis.UsesUnicode
        
        if ($canMigrate) {
            $analysis.MigrationCandidates += @{
                Name = $theorem
                Content = $theoremContent
                Reason = if ($theoremContent -match 'sorry') { "Contains sorry" }
                        elseif (!$analysis.UsesUnicode) { "No Unicode types" }
                        else { "Not using Mathlib" }
            }
        }
    }
    
    if ($Verbose) {
        Write-Host "Analysis Results:" -ForegroundColor Yellow
        Write-Host "  Total Lines: $($analysis.TotalLines)" -ForegroundColor Gray
        Write-Host "  Imports: $($analysis.Imports.Count)" -ForegroundColor Gray
        Write-Host "  Definitions: $($analysis.Definitions.Count)" -ForegroundColor Gray
        Write-Host "  Theorems: $($analysis.Theorems.Count)" -ForegroundColor Gray
        Write-Host "  Uses Mathlib: $($analysis.UsesMathlib)" -ForegroundColor $(if($analysis.UsesMathlib) {'Green'} else {'Red'})
        Write-Host "  Complexity: $($analysis.Complexity)" -ForegroundColor Gray
        Write-Host "  Migration Candidates: $($analysis.MigrationCandidates.Count)" -ForegroundColor Green
    }
    
    return $analysis
}

function Migrate-ProofContent {
    param(
        [string]$Content,
        [string]$Level,
        [hashtable]$Analysis
    )
    
    Write-Host "Migrating proof content (Level: $Level)" -ForegroundColor Cyan
    
    $migratedContent = $Content
    $changesApplied = @()
    
    # Step 1: Add Mathlib imports
    $importsToAdd = $migrationRules.ImportMappings[$Level]
    $existingImports = $Analysis.Imports
    
    $newImports = @()
    foreach ($import in $importsToAdd) {
        if ($existingImports -notcontains $import) {
            $newImports += $import
            $changesApplied += "Added import: $import"
        }
    }
    
    if ($newImports.Count -gt 0) {
        # Find insertion point (after existing imports or at beginning)
        if ($existingImports.Count -gt 0) {
            $lastImport = $existingImports[-1]
            $migratedContent = $migratedContent -replace "($lastImport)", "`$1`n$($newImports -join "`n")"
        } else {
            $migratedContent = "$($newImports -join "`n")`n`n$migratedContent"
        }
    }
    
    # Step 2: Apply type mappings (if level is Standard or Advanced)
    if ($Level -in @("Standard", "Advanced")) {
        foreach ($mapping in $migrationRules.TypeMappings) {
            $originalContent = $migratedContent
            $migratedContent = $migratedContent -replace $mapping.Pattern, $mapping.Replacement
            if ($originalContent -ne $migratedContent) {
                $changesApplied += "Type conversion: $($mapping.Pattern) -> $($mapping.Replacement)"
            }
        }
    }
    
    # Step 3: Apply theorem mappings
    foreach ($mapping in $migrationRules.TheoremMappings) {
        $originalContent = $migratedContent
        $migratedContent = $migratedContent -replace $mapping.Old, $mapping.New
        if ($originalContent -ne $migratedContent) {
            $changesApplied += "Theorem mapping: $($mapping.Old) -> $($mapping.New)"
        }
    }
    
    # Step 4: Apply tactic improvements (if level is Advanced)
    if ($Level -eq "Advanced") {
        foreach ($mapping in $migrationRules.TacticMappings) {
            # Check conditions
            $shouldApply = $true
            
            if ($mapping.Condition -eq "NotInBy") {
                # Only apply if not already in a 'by' block
                $shouldApply = $migratedContent -notmatch "by\s+$($mapping.Pattern)"
            }
            
            if ($mapping.RequiresImport) {
                # Check if required import is present
                $hasImport = ($newImports + $existingImports) -match $mapping.RequiresImport
                if (!$hasImport) {
                    $shouldApply = $false
                }
            }
            
            if ($shouldApply) {
                $originalContent = $migratedContent
                if ($mapping.Replacement -match '\$\d') {
                    # Regex replacement with capture groups
                    $migratedContent = $migratedContent -replace $mapping.Pattern, $mapping.Replacement
                } else {
                    $migratedContent = $migratedContent -replace $mapping.Pattern, $mapping.Replacement
                }
                
                if ($originalContent -ne $migratedContent) {
                    $changesApplied += "Tactic improvement: $($mapping.Pattern) -> $($mapping.Replacement)"
                }
            }
        }
    }
    
    Write-Host "Applied $($changesApplied.Count) changes" -ForegroundColor Green
    if ($Verbose) {
        $changesApplied | ForEach-Object {
            Write-Host "  - $_" -ForegroundColor Gray
        }
    }
    
    return @{
        Content = $migratedContent
        Changes = $changesApplied
        Success = $true
    }
}

function Test-MigratedProof {
    param([string]$FilePath)
    
    Write-Host "Testing migrated proof: $FilePath" -ForegroundColor Cyan
    
    try {
        # Create temp file for testing
        $tempFile = "temp_migration_test_$(Get-Date -Format 'HHmmssff').lean"
        Copy-Item $FilePath $tempFile
        
        # Test with lean
        $output = & lean $tempFile 2>&1
        $success = $LASTEXITCODE -eq 0
        
        # Clean up
        Remove-Item $tempFile -ErrorAction SilentlyContinue
        
        if ($success) {
            Write-Host "✅ Migration successful - file compiles" -ForegroundColor Green
        } else {
            Write-Host "❌ Migration has errors" -ForegroundColor Red
            $errors = $output | Where-Object { $_ -match "error:" }
            if ($Verbose -and $errors) {
                Write-Host "Errors found:" -ForegroundColor Red
                $errors | Select-Object -First 3 | ForEach-Object {
                    Write-Host "  $_" -ForegroundColor Red
                }
            }
        }
        
        return @{
            Success = $success
            Output = $output -join "`n"
            Errors = $errors
        }
        
    } catch {
        Write-Host "❌ Test failed: $($_.Exception.Message)" -ForegroundColor Red
        return @{
            Success = $false
            Error = $_.Exception.Message
        }
    }
}

function Migrate-SingleFile {
    param(
        [string]$InputFile,
        [string]$OutputPath,
        [string]$Level
    )
    
    Write-Host "`nMigrating file: $InputFile" -ForegroundColor Yellow
    Write-Host "Migration level: $Level" -ForegroundColor Gray
    
    # Analyze the file
    $analysis = Analyze-ProofFile $InputFile
    
    # Read content
    $content = Get-Content $InputFile -Raw
    
    # Perform migration
    $migrationResult = Migrate-ProofContent $content $Level $analysis
    
    if ($migrationResult.Success) {
        # Determine output path
        if (!$OutputPath) {
            $outputDir = "mathlib-migration\migrated"
            if (!(Test-Path $outputDir)) {
                New-Item -ItemType Directory -Path $outputDir -Force | Out-Null
            }
            $fileName = Split-Path $InputFile -Leaf
            $OutputPath = "$outputDir\$fileName"
        }
        
        if (!$DryRun) {
            # Save migrated content
            [System.IO.File]::WriteAllText($OutputPath, $migrationResult.Content)
            Write-Host "✅ Saved migrated file: $OutputPath" -ForegroundColor Green
            
            # Test the migrated file
            $testResult = Test-MigratedProof $OutputPath
            
            return @{
                Success = $testResult.Success
                InputFile = $InputFile
                OutputFile = $OutputPath
                Changes = $migrationResult.Changes
                TestResult = $testResult
            }
        } else {
            Write-Host "🔍 DRY RUN - Would save to: $OutputPath" -ForegroundColor Cyan
            Write-Host "Changes that would be applied:" -ForegroundColor Yellow
            $migrationResult.Changes | ForEach-Object {
                Write-Host "  - $_" -ForegroundColor Gray
            }
            
            return @{
                Success = $true
                DryRun = $true
                Changes = $migrationResult.Changes
            }
        }
    } else {
        Write-Host "❌ Migration failed" -ForegroundColor Red
        return @{
            Success = $false
            Error = "Migration process failed"
        }
    }
}

# Main execution
if ($SourceFile) {
    if (Test-Path $SourceFile) {
        $result = Migrate-SingleFile $SourceFile $OutputFile $MigrationLevel
        
        if ($result.Success -and !$result.DryRun) {
            Write-Host "`n✅ Migration completed successfully" -ForegroundColor Green
            Write-Host "Input: $($result.InputFile)" -ForegroundColor Gray
            Write-Host "Output: $($result.OutputFile)" -ForegroundColor Gray
            Write-Host "Changes: $($result.Changes.Count)" -ForegroundColor Gray
            
            if ($result.TestResult -and !$result.TestResult.Success) {
                Write-Host "⚠️ Note: Migrated file has compilation errors that need manual fixing" -ForegroundColor Yellow
            }
        }
    } else {
        Write-Host "❌ Source file not found: $SourceFile" -ForegroundColor Red
    }
} else {
    Write-Host @"
Proof Migration Tool for Mathlib

Usage:
  .\ProofMigrator.ps1 -SourceFile <path> [-OutputFile <path>] [-MigrationLevel <level>] [-DryRun] [-Verbose]

Migration Levels:
  Basic    - Add basic Mathlib imports only
  Standard - Add imports and convert types to Unicode
  Advanced - Full migration with tactic improvements

Examples:
  .\ProofMigrator.ps1 -SourceFile "MyProof.lean" -MigrationLevel "Standard"
  .\ProofMigrator.ps1 -SourceFile "MyProof.lean" -DryRun -Verbose
"@ -ForegroundColor Cyan
}

Export-ModuleMember -Function Analyze-ProofFile, Migrate-ProofContent, Test-MigratedProof, Migrate-SingleFile