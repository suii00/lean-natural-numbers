import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Irrational

-- √2が無理数であることの補助定理
lemma sqrt_two_irrational : Irrational (Real.sqrt 2) := by
  exact irrational_sqrt_two

-- メイン定理の実用的な版
theorem rational_linear_combination_sqrt_two_zero
  (x y : ℚ) (h : (x : ℝ) + (y : ℝ) * Real.sqrt 2 = 0) : x = 0 ∧ y = 0 := by
  -- 対偶を使った証明
  by_contra h_not_both_zero
  -- ¬(x = 0 ∧ y = 0) は (x ≠ 0 ∨ y ≠ 0) と同値
  rw [not_and_or] at h_not_both_zero
  cases h_not_both_zero with
  | inl hx_ne_zero =>
    -- x ≠ 0 の場合
    by_cases hy_zero : y = 0
    · -- y = 0, x ≠ 0
      rw [hy_zero, Rat.cast_zero, zero_mul, add_zero] at h
      -- h : (x : ℝ) = 0 だが x ≠ 0 なので矛盾
      have x_cast_ne_zero : (x : ℝ) ≠ 0 := by
        intro hx_cast_zero
        exact hx_ne_zero (Rat.cast_injective hx_cast_zero)
      exact x_cast_ne_zero h
    · -- x ≠ 0, y ≠ 0
      have y_cast_ne_zero : (y : ℝ) ≠ 0 := by
        intro hy_cast_zero
        exact hy_zero (Rat.cast_injective hy_cast_zero)
      -- √2が有理数で表現可能になってしまう
      have sqrt_eq : Real.sqrt 2 = -(x : ℝ) / (y : ℝ) := by
        field_simp [y_cast_ne_zero] at h ⊢
        linarith
      -- -x/y は有理数
      have sqrt_rational : ∃ q : ℚ, (q : ℝ) = Real.sqrt 2 := by
        use -x / y
        rw [sqrt_eq, Rat.cast_neg, Rat.cast_div]
      obtain ⟨q, hq⟩ := sqrt_rational
      have not_irrational : ¬Irrational (q : ℝ) := by
        exact not_irrational_rat_cast q
      rw [← hq] at not_irrational
      exact not_irrational sqrt_two_irrational
  | inr hy_ne_zero =>
    -- y ≠ 0 の場合も同様
    have y_cast_ne_zero : (y : ℝ) ≠ 0 := by
      intro hy_cast_zero
      exact hy_ne_zero (Rat.cast_injective hy_cast_zero)
    have sqrt_eq : Real.sqrt 2 = -(x : ℝ) / (y : ℝ) := by
      field_simp [y_cast_ne_zero] at h ⊢
      linarith
    have sqrt_rational : ∃ q : ℚ, (q : ℝ) = Real.sqrt 2 := by
      use -x / y
      rw [sqrt_eq, Rat.cast_neg, Rat.cast_div]
    obtain ⟨q, hq⟩ := sqrt_rational
    have not_irrational : ¬Irrational (q : ℝ) := by
      exact not_irrational_rat_cast q
    rw [← hq] at not_irrational
    exact not_irrational sqrt_two_irrational

-- より簡潔な証明
theorem rational_linear_combination_sqrt_two_zero_alt
  (x y : ℚ) (h : (x : ℝ) + (y : ℝ) * Real.sqrt 2 = 0) : x = 0 ∧ y = 0 := by
  constructor <;> {
    by_contra h_ne_zero
    -- どちらかが非零なら√2が有理数になる矛盾
    have : ∃ q : ℚ, (q : ℝ) = Real.sqrt 2 := by
      by_cases hy_zero : y = 0
      · -- x ≠ 0, y = 0 の場合
        rw [hy_zero, Rat.cast_zero, zero_mul, add_zero] at h
        exfalso
        exact h_ne_zero (Rat.cast_injective h)
      · -- 一般の場合
        have y_ne_zero : (y : ℝ) ≠ 0 := by
          intro hy_cast_zero
          exact hy_zero (Rat.cast_injective hy_cast_zero)
        use -x / y
        field_simp [y_ne_zero] at h ⊢
        rw [Rat.cast_neg, Rat.cast_div]
        linarith
    obtain ⟨q, hq⟩ := this
    have : ¬Irrational (q : ℝ) := not_irrational_rat_cast q
    rw [← hq] at this
    exact this sqrt_two_irrational
  }

-- 検証
#check rational_linear_combination_sqrt_two_zero
#check rational_linear_combination_sqrt_two_zero_alt

-- 使用例
example : (0 : ℚ) + (0 : ℚ) * Real.sqrt 2 = 0 := by simp

-- より具体的な例
example : ∀ a b : ℚ, (a : ℝ) + (b : ℝ) * Real.sqrt 2 = 0 → a = 0 ∧ b = 0 := 
  rational_linear_combination_sqrt_two_zero

-- 実用性テスト
example (x y : ℚ) : (x : ℝ) + (y : ℝ) * Real.sqrt 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · exact rational_linear_combination_sqrt_two_zero x y
  · intro ⟨hx, hy⟩
    rw [hx, hy]
    simp