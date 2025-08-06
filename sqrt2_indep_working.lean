import Mathlib.Data.Real.Irrational
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Rat.Cast.Defs

-- √2が無理数であることの補助定理
lemma sqrt_two_irrational : Irrational (Real.sqrt 2) := by
  exact irrational_sqrt_two

-- より簡潔で安全なバージョン
theorem rational_linear_combination_sqrt_two_zero
  (x y : ℚ) (h : (x : ℝ) + (y : ℝ) * Real.sqrt 2 = 0) : x = 0 ∧ y = 0 := by
  by_contra h_not_both_zero
  push_neg at h_not_both_zero
  -- x ≠ 0 または y ≠ 0
  rcases h_not_both_zero with (hx | hy)
  · -- x ≠ 0 の場合
    by_cases hy_zero : y = 0
    · -- y = 0, x ≠ 0
      rw [hy_zero] at h
      simp at h
      have x_cast_ne_zero : (x : ℝ) ≠ 0 := by
        intro hx_eq_zero
        exact hx (Rat.cast_injective (by rwa [Rat.cast_zero]))
      exact x_cast_ne_zero h
    · -- x ≠ 0, y ≠ 0
      have y_cast_ne_zero : (y : ℝ) ≠ 0 := by
        intro hy_eq_zero
        exact hy_zero (Rat.cast_injective (by rwa [Rat.cast_zero]))
      -- √2 が有理数になってしまう
      have sqrt_rational : Real.sqrt 2 = -(x : ℝ) / (y : ℝ) := by
        field_simp [y_cast_ne_zero] at h ⊢
        linarith
      have : ∃ q : ℚ, (q : ℝ) = Real.sqrt 2 := by
        use -x / y
        rw [sqrt_rational]
        simp [Rat.cast_neg, Rat.cast_div]
      obtain ⟨q, hq⟩ := this
      have : ¬ Irrational (q : ℝ) := by
        rw [irrational_iff_ne_rational]
        push_neg
        exact ⟨q, rfl⟩
      rw [← hq] at this
      exact this sqrt_two_irrational
  · -- y ≠ 0 の場合
    have y_cast_ne_zero : (y : ℝ) ≠ 0 := by
      intro hy_eq_zero
      exact hy (Rat.cast_injective (by rwa [Rat.cast_zero]))
    -- 同様に √2 が有理数になる
    have sqrt_rational : Real.sqrt 2 = -(x : ℝ) / (y : ℝ) := by
      field_simp [y_cast_ne_zero] at h ⊢
      linarith
    have : ∃ q : ℚ, (q : ℝ) = Real.sqrt 2 := by
      use -x / y  
      rw [sqrt_rational]
      simp [Rat.cast_neg, Rat.cast_div]
    obtain ⟨q, hq⟩ := this
    have : ¬ Irrational (q : ℝ) := by
      rw [irrational_iff_ne_rational]
      push_neg
      exact ⟨q, rfl⟩
    rw [← hq] at this
    exact this sqrt_two_irrational

-- 検証
#check rational_linear_combination_sqrt_two_zero

-- 使用例
example : (0 : ℚ) + (0 : ℚ) * Real.sqrt 2 = 0 := by simp