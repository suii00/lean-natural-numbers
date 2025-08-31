-- Test module for mathlib functionality
-- Module name: Theorem1.Proof

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace Theorem1

theorem simple_add (n : ℕ) : n + 0 = n := by
  rw [add_zero]

theorem double_nat (n : ℕ) : n + n = 2 * n := by
  rw [two_mul]

example (a b : ℕ) : a + b = b + a := by
  rw [add_comm]

end Theorem1