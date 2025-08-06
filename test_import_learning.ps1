# Import学習システムのテスト実行

Write-Host "🧪 Import学習システム テスト開始" -ForegroundColor Green

# テスト対象のImport文リスト
$testImports = @(
    "import Mathlib.Tactic.Basic",
    "import Mathlib.Data.Nat.Basic", 
    "import Mathlib.Data.Int.Basic",
    "import Mathlib.Tactic.Ring",
    "import Mathlib.Tactic.Omega",
    "import Mathlib.Data.Nat.Parity",
    "import Mathlib.NonExistent.Module",  # 意図的な失敗テスト
    "import Mathlib.Data.Real.Basic"
)

# 各Importに対するテストコード
$testCases = @{
    "import Mathlib.Tactic.Basic" = "theorem test_basic : True := by trivial"
    "import Mathlib.Data.Nat.Basic" = "theorem test_nat : ∀ n : ℕ, n + 0 = n := add_zero"
    "import Mathlib.Data.Int.Basic" = "theorem test_int : ∀ n : ℤ, n + 0 = n := add_zero"
    "import Mathlib.Tactic.Ring" = @"
theorem test_ring (a b : ℕ) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  ring
"@
    "import Mathlib.Tactic.Omega" = "theorem test_omega (n : ℕ) : n + 0 = n := by omega"
    "import Mathlib.Data.Nat.Parity" = "theorem test_parity : Even 4 := by use 2; rfl"
    "import Mathlib.NonExistent.Module" = "theorem test_fail : True := trivial"
    "import Mathlib.Data.Real.Basic" = "theorem test_real : ∀ x : ℝ, x + 0 = x := add_zero"
}

# 学習システム読み込み
. "import-learning\ImportLearningSystem.ps1"

# テスト実行
Write-Host "テストImport数: $($testImports.Count)" -ForegroundColor Gray
Write-Host "テストケース数: $($testCases.Count)" -ForegroundColor Gray

$database = Start-ImportLearningSession $testImports $testCases -ExportReport -Verbose

Write-Host "`n🎯 テスト完了!" -ForegroundColor Green