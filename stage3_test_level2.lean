-- Stage 3 Test Level 2: Basic Math Functions
import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Basic

theorem test_nat : ∀ n : ℕ, n + 0 = n := Nat.add_zero

example : Even 4 := by use 2; rfl

#check Nat.add_zero
#check Even