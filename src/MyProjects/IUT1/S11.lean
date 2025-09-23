import Mathlib

namespace HW_IUT1_S11

-- P01
theorem S11_P01 : ∃ (x y : ℤ), x ^ 2 + y ^ 2 = 13 := by
  refine ⟨2, 3, ?_⟩
  norm_num

-- P02
theorem S11_P02 : (3 : ℤ) ^ 2 - 2 * 2 ^ 2 = 1 := by
  norm_num

-- P03
theorem S11_P03 : ∃ (a b c d : ℤ), a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 7 := by
  refine ⟨2, 1, 1, 1, ?_⟩
  norm_num

-- P04
theorem S11_P04 : Complex.normSq (3 + 4 * Complex.I) = 25 := by
  have : (3 : ℝ) * 3 + (4 : ℝ) * 4 = 25 := by norm_num
  simpa [Complex.normSq] using this

-- P05
theorem S11_P05 : (3 : ℤ) ^ 2 % 8 = 1 ∧ 3 % 5 = 3 := by
  constructor <;> decide

-- Challenge
theorem S11_CH :
    let disc_f := -20
    let disc_g := -20
    (disc_f = disc_g) ∧
    (∃ (x y : ℤ), x ^ 2 + 5 * y ^ 2 = 29) ∧
    (∃ (u v : ℤ), 2 * u ^ 2 + 2 * u * v + 3 * v ^ 2 = 7) := by
  classical
  change (-20 = -20) ∧ (∃ (x y : ℤ), x ^ 2 + 5 * y ^ 2 = 29) ∧ (∃ (u v : ℤ), 2 * u ^ 2 + 2 * u * v + 3 * v ^ 2 = 7)
  refine And.intro rfl ?_
  refine And.intro ?_ ?_
  · refine ⟨3, 2, ?_⟩
    norm_num
  · refine ⟨1, 1, ?_⟩
    norm_num

end HW_IUT1_S11
