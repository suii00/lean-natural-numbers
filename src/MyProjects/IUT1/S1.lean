import Mathlib

namespace HW_IUT1_S01

-- P01: 整数の加法群構造
theorem S1_P01 (a b c : Int) : (a + b) + c = a + (b + c) := by
  simp [add_assoc]

-- P02: 整数の環構造
theorem S1_P02 (a b c : Int) : a * (b + c) = a * b + a * c := by
  exact Int.mul_add a b c

-- P03: 整数の順序性質
theorem S1_P03 (a b : Int) (h : a ≤ b) : a + 1 ≤ b + 1 := by
  exact add_le_add_right h 1

-- P04: 整数の除法性質（導入）
theorem S1_P04 (n : Int) : (2 : Int) ∣ (2 * n) := by
  refine ⟨n, ?_⟩
  simp

-- P05: 整数の絶対値
theorem S1_P05 (a : Int) : 0 ≤ Int.natAbs a := by
  exact Nat.zero_le _

-- CH: Well-Ordering Principle の部分的実現
theorem S1_CH : ∃ m, m ∈ ({2, 5, 3} : Set Nat) ∧ ∀ x ∈ ({2, 5, 3} : Set Nat), m ≤ x := by
  refine ⟨2, ?_⟩
  constructor
  · simp
  · intro x hx
    have hx' := hx
    simp at hx'
    rcases hx' with rfl | rfl | rfl
    · exact le_rfl
    · decide
    · decide

end HW_IUT1_S01
