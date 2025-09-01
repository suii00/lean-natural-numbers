import Mathlib.Data.Real.Irrational
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic

-- √2が無理数であることの補助定理
lemma sqrt_two_irrational : Irrational (Real.sqrt 2) := by
  exact irrational_sqrt_two

-- メインの定理：x + y√2 = 0 かつ x, y が有理数 ⟹ x = y = 0
theorem rational_linear_combination_sqrt_two_zero 
  (x y : ℚ) (h : (x : ℝ) + (y : ℝ) * Real.sqrt 2 = 0) : x = 0 ∧ y = 0 := by
  constructor
  · -- x = 0 を証明
    by_contra hx_ne_zero
    by_cases hy : y = 0
    · -- y = 0 の場合
      rw [hy] at h
      simp at h
      -- (x : ℝ) = 0 だが x ≠ 0 なので矛盾
      have : (x : ℝ) ≠ 0 := by
        intro hx_eq_zero
        have : x = 0 := by
          rw [← Rat.cast_zero] at hx_eq_zero
          exact Rat.cast_injective hx_eq_zero
        exact hx_ne_zero this
      exact this h
    · -- y ≠ 0 の場合
      have hy_ne_zero : (y : ℝ) ≠ 0 := by
        intro hy_eq_zero
        have : y = 0 := by
          rw [← Rat.cast_zero] at hy_eq_zero
          exact Rat.cast_injective hy_eq_zero
        exact hy this
      -- h から √2 = -x/y を導く
      have h_sqrt : Real.sqrt 2 = -(x : ℝ) / (y : ℝ) := by
        have : (y : ℝ) * Real.sqrt 2 = -(x : ℝ) := by linarith
        rw [← this, mul_div_cancel_left _ hy_ne_zero]
      -- -x/y は有理数なので √2 が有理数になり矛盾
      have : ∃ q : ℚ, (q : ℝ) = -(x : ℝ) / (y : ℝ) := by
        use -x / y
        rw [Rat.cast_neg, Rat.cast_div]
      obtain ⟨q, hq⟩ := this
      rw [← hq] at h_sqrt
      -- q は有理数なので無理数ではない
      have : ¬ Irrational (q : ℝ) := by
        rw [irrational_iff_ne_rational]
        push_neg
        exact ⟨q, rfl⟩
      rw [h_sqrt] at this
      exact this sqrt_two_irrational
  · -- y = 0 を証明
    by_contra hy_ne_zero
    -- 最初の部分で x = 0 が証明されている
    have hx_zero : x = 0 := by
      by_contra hx_ne_zero
      by_cases hy_zero : y = 0
      · rw [hy_zero] at h
        simp at h
        have : (x : ℝ) ≠ 0 := by
          intro hx_eq_zero
          have : x = 0 := by
            rw [← Rat.cast_zero] at hx_eq_zero
            exact Rat.cast_injective hx_eq_zero
          exact hx_ne_zero this
        exact this h
      · have hy_ne_zero_real : (y : ℝ) ≠ 0 := by
          intro hy_eq_zero
          have : y = 0 := by
            rw [← Rat.cast_zero] at hy_eq_zero
            exact Rat.cast_injective hy_eq_zero
          exact hy_zero this
        have h_sqrt : Real.sqrt 2 = -(x : ℝ) / (y : ℝ) := by
          have : (y : ℝ) * Real.sqrt 2 = -(x : ℝ) := by linarith
          rw [← this, mul_div_cancel_left _ hy_ne_zero_real]
        have : ∃ q : ℚ, (q : ℝ) = -(x : ℝ) / (y : ℝ) := by
          use -x / y
          rw [Rat.cast_neg, Rat.cast_div]
        obtain ⟨q, hq⟩ := this
        rw [← hq] at h_sqrt
        have : ¬ Irrational (q : ℝ) := by
          rw [irrational_iff_ne_rational]
          push_neg
          exact ⟨q, rfl⟩
        rw [h_sqrt] at this
        exact this sqrt_two_irrational
    -- x = 0 を代入
    rw [hx_zero] at h
    simp at h
    -- y * √2 = 0 かつ y ≠ 0 なので √2 = 0 となるが、これは矛盾
    have hy_ne_zero_real : (y : ℝ) ≠ 0 := by
      intro hy_eq_zero
      have : y = 0 := by
        rw [← Rat.cast_zero] at hy_eq_zero
        exact Rat.cast_injective hy_eq_zero
      exact hy_ne_zero this
    have sqrt_zero : Real.sqrt 2 = 0 := by
      rw [← mul_div_cancel_left (Real.sqrt 2) hy_ne_zero_real]
      rw [h, zero_div]
    have sqrt_pos : Real.sqrt 2 > 0 := by
      exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
    rw [sqrt_zero] at sqrt_pos
    exact lt_irrefl 0 sqrt_pos

-- より簡潔なバージョン
theorem rational_linear_combination_sqrt_two_zero_v2
  (x y : ℚ) (h : (x : ℝ) + (y : ℝ) * Real.sqrt 2 = 0) : x = 0 ∧ y = 0 := by
  -- 対偶を使った証明
  by_contra h_not_both_zero
  push_neg at h_not_both_zero
  rcases h_not_both_zero with (hx | hy)
  · -- x ≠ 0 の場合
    by_cases hy_zero : y = 0
    · -- y = 0, x ≠ 0
      rw [hy_zero] at h
      simp at h
      have : (x : ℝ) ≠ 0 := by
        intro hx_zero
        exact hx (Rat.cast_injective (by rwa [Rat.cast_zero]))
      exact this h
    · -- x ≠ 0, y ≠ 0
      -- √2 が有理数になってしまう
      have hy_ne_zero_real : (y : ℝ) ≠ 0 := by
        intro hy_zero_real
        exact hy_zero (Rat.cast_injective (by rwa [Rat.cast_zero]))
      have sqrt_rational : Real.sqrt 2 = -(x : ℝ) / (y : ℝ) := by
        field_simp [hy_ne_zero_real] at h ⊢
        linarith
      -- 右辺は有理数
      have : ∃ q : ℚ, (q : ℝ) = Real.sqrt 2 := by
        use -x / y
        rw [sqrt_rational, Rat.cast_neg, Rat.cast_div]
      obtain ⟨q, hq⟩ := this
      have : ¬ Irrational (q : ℝ) := by
        rw [irrational_iff_ne_rational]
        push_neg
        exact ⟨q, rfl⟩
      rw [← hq] at this
      exact this sqrt_two_irrational
  · -- y ≠ 0 の場合
    have hy_ne_zero_real : (y : ℝ) ≠ 0 := by
      intro hy_zero_real
      exact hy (Rat.cast_injective (by rwa [Rat.cast_zero]))
    -- 同様に √2 が有理数になる
    have sqrt_rational : Real.sqrt 2 = -(x : ℝ) / (y : ℝ) := by
      field_simp [hy_ne_zero_real] at h ⊢
      linarith
    have : ∃ q : ℚ, (q : ℝ) = Real.sqrt 2 := by
      use -x / y
      rw [sqrt_rational, Rat.cast_neg, Rat.cast_div]
    obtain ⟨q, hq⟩ := this
    have : ¬ Irrational (q : ℝ) := by
      rw [irrational_iff_ne_rational]
      push_neg
      exact ⟨q, rfl⟩
    rw [← hq] at this
    exact this sqrt_two_irrational

-- 使用例
example : (0 : ℚ) + (0 : ℚ) * Real.sqrt 2 = 0 := by simp

#check rational_linear_combination_sqrt_two_zero
#check rational_linear_combination_sqrt_two_zero_v2