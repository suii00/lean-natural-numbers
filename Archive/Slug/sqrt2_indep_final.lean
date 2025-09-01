import Mathlib.Data.Real.Irrational
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Rat.Cast.Defs

-- √2が無理数であることの補助定理
lemma sqrt_two_irrational : Irrational (Real.sqrt 2) := by
  exact irrational_sqrt_two

-- メイン定理の最終版
theorem rational_linear_combination_sqrt_two_zero
  (x y : ℚ) (h : (x : ℝ) + (y : ℝ) * Real.sqrt 2 = 0) : x = 0 ∧ y = 0 := by
  by_contra h_not_both_zero
  -- ¬(x = 0 ∧ y = 0) は (x ≠ 0 ∨ y ≠ 0) と同値
  rw [not_and_or] at h_not_both_zero
  cases h_not_both_zero with
  | inl hx_ne_zero =>
    -- x ≠ 0 の場合
    by_cases hy_zero : y = 0
    · -- y = 0, x ≠ 0
      rw [hy_zero] at h
      simp at h
      -- h : (x : ℝ) = 0 だが x ≠ 0 なので矛盾
      have x_cast_ne_zero : (x : ℝ) ≠ 0 := by
        intro hx_cast_zero
        have x_zero : x = 0 := Rat.cast_injective (by rwa [Rat.cast_zero])
        exact hx_ne_zero x_zero
      exact x_cast_ne_zero h
    · -- x ≠ 0, y ≠ 0
      have y_cast_ne_zero : (y : ℝ) ≠ 0 := by
        intro hy_cast_zero
        have y_zero : y = 0 := Rat.cast_injective (by rwa [Rat.cast_zero])
        exact hy_zero y_zero
      -- h から √2 = -(x : ℝ) / (y : ℝ) を導く
      have h_rearrange : (y : ℝ) * Real.sqrt 2 = -(x : ℝ) := by
        linarith [h]
      have sqrt_eq : Real.sqrt 2 = -(x : ℝ) / (y : ℝ) := by
        rw [← h_rearrange]
        rw [mul_div_cancel_left' (Real.sqrt 2) y_cast_ne_zero]
      -- -(x : ℝ) / (y : ℝ) は有理数として表現可能
      have rational_exists : ∃ q : ℚ, (q : ℝ) = Real.sqrt 2 := by
        use -x / y
        rw [sqrt_eq]
        rw [Rat.cast_neg, Rat.cast_div]
      obtain ⟨q, hq⟩ := rational_exists
      -- q は有理数なので無理数ではない
      have q_not_irrational : ¬ Irrational (q : ℝ) := by
        rw [irrational_iff_ne_rational]
        push_neg
        exact ⟨q, rfl⟩
      rw [← hq] at q_not_irrational
      exact q_not_irrational sqrt_two_irrational
  | inr hy_ne_zero =>
    -- y ≠ 0 の場合
    have y_cast_ne_zero : (y : ℝ) ≠ 0 := by
      intro hy_cast_zero
      have y_zero : y = 0 := Rat.cast_injective (by rwa [Rat.cast_zero])
      exact hy_ne_zero y_zero
    -- 同様の論理で √2 が有理数になる
    have h_rearrange : (y : ℝ) * Real.sqrt 2 = -(x : ℝ) := by
      linarith [h]
    have sqrt_eq : Real.sqrt 2 = -(x : ℝ) / (y : ℝ) := by
      rw [← h_rearrange]
      rw [mul_div_cancel_left' (Real.sqrt 2) y_cast_ne_zero]
    have rational_exists : ∃ q : ℚ, (q : ℝ) = Real.sqrt 2 := by
      use -x / y
      rw [sqrt_eq]
      rw [Rat.cast_neg, Rat.cast_div]
    obtain ⟨q, hq⟩ := rational_exists
    have q_not_irrational : ¬ Irrational (q : ℝ) := by
      rw [irrational_iff_ne_rational]
      push_neg
      exact ⟨q, rfl⟩
    rw [← hq] at q_not_irrational
    exact q_not_irrational sqrt_two_irrational

-- 検証
#check rational_linear_combination_sqrt_two_zero

-- 使用例
example : (0 : ℚ) + (0 : ℚ) * Real.sqrt 2 = 0 := by simp

-- 非自明な例
example : ∀ x y : ℚ, (x : ℝ) + (y : ℝ) * Real.sqrt 2 = 0 → x = 0 ∧ y = 0 :=
  rational_linear_combination_sqrt_two_zero