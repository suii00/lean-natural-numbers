# Simple Import Learning Test

Write-Host "Import Learning System Test" -ForegroundColor Green

# Test imports list
$testImports = @(
    "import Mathlib.Tactic.Basic",
    "import Mathlib.Data.Nat.Basic", 
    "import Mathlib.NonExistent.Module"
)

# Test cases
$testCases = @{
    "import Mathlib.Tactic.Basic" = "theorem test_basic : True := by trivial"
    "import Mathlib.Data.Nat.Basic" = "theorem test_nat (n : Nat) : n + 0 = n := by sorry"
    "import Mathlib.NonExistent.Module" = "theorem test_fail : True := trivial"
}

Write-Host "Test imports: $($testImports.Count)" -ForegroundColor Gray

# Load and run learning system
. "import-learning\ImportLearningSystem.ps1"

try {
    $database = Start-ImportLearningSession $testImports $testCases -ExportReport -Verbose
    Write-Host "Test completed successfully!" -ForegroundColor Green
} catch {
    Write-Host "Test failed: $_" -ForegroundColor Red
}