import Mathlib.Data.Real.Irrational
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

-- √2が無理数であることの補助定理
lemma sqrt_two_irrational : Irrational (Real.sqrt 2) := by
  exact irrational_sqrt_two

-- 有理数のキャストに関する補助定理
lemma rat_cast_injective {x y : ℚ} : (x : ℝ) = (y : ℝ) → x = y := by
  intro h
  -- 有理数から実数への埋め込みは単射
  exact Rat.cast_injective h

lemma rat_cast_ne_zero {x : ℚ} : x ≠ 0 ↔ (x : ℝ) ≠ 0 := by
  constructor
  · intro h_ne_zero h_cast_zero
    have : x = 0 := rat_cast_injective (by rwa [Rat.cast_zero])
    exact h_ne_zero this
  · intro h_cast_ne_zero h_zero
    rw [h_zero, Rat.cast_zero] at h_cast_ne_zero
    exact h_cast_ne_zero rfl

-- メインの定理：x + y√2 = 0 かつ x, y が有理数 ⟹ x = y = 0
theorem rational_linear_combination_sqrt_two_zero
  (x y : ℚ) (h : (x : ℝ) + (y : ℝ) * Real.sqrt 2 = 0) : x = 0 ∧ y = 0 := by
  constructor
  · -- x = 0 を証明
    by_contra hx_ne_zero
    by_cases hy : y = 0
    · -- y = 0 の場合
      rw [hy, Rat.cast_zero, zero_mul, add_zero] at h
      -- (x : ℝ) = 0 だが x ≠ 0 なので矛盾
      have hx_cast_ne_zero : (x : ℝ) ≠ 0 := rat_cast_ne_zero.mp hx_ne_zero
      exact hx_cast_ne_zero h
    · -- y ≠ 0 の場合
      have hy_cast_ne_zero : (y : ℝ) ≠ 0 := rat_cast_ne_zero.mp hy
      -- h から √2 = -x/y を導く
      have h_sqrt : Real.sqrt 2 = -(x : ℝ) / (y : ℝ) := by
        have : (y : ℝ) * Real.sqrt 2 = -(x : ℝ) := by linarith
        rw [← this, mul_div_cancel_left _ hy_cast_ne_zero]
      -- -x/y は有理数なので √2 が有理数になり矛盾
      have rational_quotient : ((-x / y) : ℚ) = (-(x : ℝ) / (y : ℝ)) := by
        rw [Rat.cast_neg, Rat.cast_div]
      have : Irrational ((-x / y : ℚ) : ℝ) := by
        rw [rational_quotient, h_sqrt]
        exact sqrt_two_irrational
      -- 有理数は無理数ではない
      have : ¬ Irrational ((-x / y : ℚ) : ℝ) := by
        rw [irrational_iff_ne_rational]
        push_neg
        exact ⟨-x / y, rfl⟩
      contradiction
  · -- y = 0 を証明
    by_contra hy_ne_zero
    -- 上で証明したロジックを再利用
    have hx_zero : x = 0 := by
      by_contra hx_ne_zero
      by_cases hy_zero : y = 0
      · rw [hy_zero, Rat.cast_zero, zero_mul, add_zero] at h
        have hx_cast_ne_zero : (x : ℝ) ≠ 0 := rat_cast_ne_zero.mp hx_ne_zero
        exact hx_cast_ne_zero h
      · have hy_cast_ne_zero : (y : ℝ) ≠ 0 := rat_cast_ne_zero.mp hy_zero
        have h_sqrt : Real.sqrt 2 = -(x : ℝ) / (y : ℝ) := by
          have : (y : ℝ) * Real.sqrt 2 = -(x : ℝ) := by linarith
          rw [← this, mul_div_cancel_left _ hy_cast_ne_zero]
        have rational_quotient : ((-x / y) : ℚ) = (-(x : ℝ) / (y : ℝ)) := by
          rw [Rat.cast_neg, Rat.cast_div]
        have : Irrational ((-x / y : ℚ) : ℝ) := by
          rw [rational_quotient, h_sqrt]
          exact sqrt_two_irrational
        have : ¬ Irrational ((-x / y : ℚ) : ℝ) := by
          rw [irrational_iff_ne_rational]
          push_neg
          exact ⟨-x / y, rfl⟩
        contradiction
    -- x = 0 を代入
    rw [hx_zero, Rat.cast_zero, zero_add] at h
    have hy_cast_ne_zero : (y : ℝ) ≠ 0 := rat_cast_ne_zero.mp hy_ne_zero
    -- y * √2 = 0 かつ y ≠ 0 なので √2 = 0 となるが、これは矛盾
    have sqrt_zero : Real.sqrt 2 = 0 := by
      rw [mul_eq_zero] at h
      cases h with
      | inl hy_zero => exact False.elim (hy_cast_ne_zero hy_zero)
      | inr h_sqrt_zero => exact h_sqrt_zero
    have sqrt_pos : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
    rw [sqrt_zero] at sqrt_pos
    exact lt_irrefl 0 sqrt_pos

-- より直接的なバージョン
theorem rational_linear_combination_sqrt_two_zero_direct
  (x y : ℚ) (h : (x : ℝ) + (y : ℝ) * Real.sqrt 2 = 0) : x = 0 ∧ y = 0 := by
  -- 対偶：x ≠ 0 または y ≠ 0 なら x + y√2 ≠ 0
  by_contra h_not_both_zero
  push_neg at h_not_both_zero
  -- x ≠ 0 または y ≠ 0
  cases h_not_both_zero with
  | inl hx_ne_zero =>
    -- x ≠ 0 の場合
    by_cases hy_zero : y = 0
    · -- y = 0, x ≠ 0
      rw [hy_zero, Rat.cast_zero, zero_mul, add_zero] at h
      have : (x : ℝ) ≠ 0 := rat_cast_ne_zero.mp hx_ne_zero
      exact this h
    · -- x ≠ 0, y ≠ 0
      have hy_cast_ne_zero : (y : ℝ) ≠ 0 := rat_cast_ne_zero.mp hy_zero
      have sqrt_eq : Real.sqrt 2 = -(x : ℝ) / (y : ℝ) := by
        have : (y : ℝ) * Real.sqrt 2 = -(x : ℝ) := by linarith
        rw [← this, mul_div_cancel_left _ hy_cast_ne_zero]
      -- 右辺は有理数なので矛盾
      have : ((-x / y) : ℚ) = (-(x : ℝ) / (y : ℝ)) := by
        rw [Rat.cast_neg, Rat.cast_div]
      have : Irrational ((-x / y : ℚ) : ℝ) := by
        rw [this, sqrt_eq]
        exact sqrt_two_irrational
      have : ¬ Irrational ((-x / y : ℚ) : ℝ) := by
        rw [irrational_iff_ne_rational]
        push_neg
        exact ⟨-x / y, rfl⟩
      contradiction
  | inr hy_ne_zero =>
    -- y ≠ 0 の場合
    have hy_cast_ne_zero : (y : ℝ) ≠ 0 := rat_cast_ne_zero.mp hy_ne_zero
    -- 同様に √2 が有理数になる
    have sqrt_eq : Real.sqrt 2 = -(x : ℝ) / (y : ℝ) := by
      have : (y : ℝ) * Real.sqrt 2 = -(x : ℝ) := by linarith
      rw [← this, mul_div_cancel_left _ hy_cast_ne_zero]
    have : ((-x / y) : ℚ) = (-(x : ℝ) / (y : ℝ)) := by
      rw [Rat.cast_neg, Rat.cast_div]
    have : Irrational ((-x / y : ℚ) : ℝ) := by
      rw [this, sqrt_eq]
      exact sqrt_two_irrational
    have : ¬ Irrational ((-x / y : ℚ) : ℝ) := by
      rw [irrational_iff_ne_rational]
      push_neg
      exact ⟨-x / y, rfl⟩
    contradiction

-- 最も基本的なバージョン（手動で場合分けを明示）
theorem rational_linear_combination_sqrt_two_zero_basic
  (x y : ℚ) (h : (x : ℝ) + (y : ℝ) * Real.sqrt 2 = 0) : x = 0 ∧ y = 0 := by
  constructor
  -- Part 1: x = 0 を証明
  · intro hx_ne_zero
    -- Case 1: y = 0
    have case1 : y = 0 → False := by
      intro hy_zero
      rw [hy_zero] at h
      simp at h
      have : (x : ℝ) ≠ 0 := by
        intro hx_zero
        have : x = 0 := rat_cast_injective (by rwa [Rat.cast_zero])
        exact hx_ne_zero this
      exact this h
    -- Case 2: y ≠ 0
    have case2 : y ≠ 0 → False := by
      intro hy_ne_zero
      have hy_cast_ne_zero : (y : ℝ) ≠ 0 := by
        intro hy_zero
        have : y = 0 := rat_cast_injective (by rwa [Rat.cast_zero])
        exact hy_ne_zero this
      -- √2 = -x/y
      have sqrt_eq : Real.sqrt 2 = -(x : ℝ) / (y : ℝ) := by
        have rearranged : (y : ℝ) * Real.sqrt 2 = -(x : ℝ) := by linarith
        exact (eq_div_iff_mul_eq hy_cast_ne_zero).mpr rearranged
      -- 矛盾を導く
      have quotient_eq : ((-x / y) : ℚ) = (-(x : ℝ) / (y : ℝ)) := by
        rw [Rat.cast_neg, Rat.cast_div]
      have irrational_claim : Irrational ((-x / y : ℚ) : ℝ) := by
        rw [quotient_eq, sqrt_eq]
        exact sqrt_two_irrational
      have rational_fact : ¬ Irrational ((-x / y : ℚ) : ℝ) := by
        rw [irrational_iff_ne_rational]
        push_neg
        exact ⟨-x / y, rfl⟩
      exact rational_fact irrational_claim
    -- 排中律を使用
    cases Classical.em (y = 0) with
    | inl hy_zero => exact case1 hy_zero
    | inr hy_ne_zero => exact case2 hy_ne_zero
  -- Part 2: y = 0 を証明（同様の論法）
  · intro hy_ne_zero
    -- 最初に x = 0 であることを示す
    have hx_zero : x = 0 := by
      intro hx_ne_zero
      cases Classical.em (y = 0) with
      | inl hy_zero =>
        rw [hy_zero] at h
        simp at h
        have : (x : ℝ) ≠ 0 := by
          intro hx_zero_cast
          have : x = 0 := rat_cast_injective (by rwa [Rat.cast_zero])
          exact hx_ne_zero this
        exact this h
      | inr hy_zero =>
        have hy_cast_ne_zero : (y : ℝ) ≠ 0 := by
          intro hy_zero_cast
          have : y = 0 := rat_cast_injective (by rwa [Rat.cast_zero])
          exact hy_zero this
        have sqrt_eq : Real.sqrt 2 = -(x : ℝ) / (y : ℝ) := by
          have rearranged : (y : ℝ) * Real.sqrt 2 = -(x : ℝ) := by linarith
          exact (eq_div_iff_mul_eq hy_cast_ne_zero).mpr rearranged
        have quotient_eq : ((-x / y) : ℚ) = (-(x : ℝ) / (y : ℝ)) := by
          rw [Rat.cast_neg, Rat.cast_div]
        have irrational_claim : Irrational ((-x / y : ℚ) : ℝ) := by
          rw [quotient_eq, sqrt_eq]
          exact sqrt_two_irrational
        have rational_fact : ¬ Irrational ((-x / y : ℚ) : ℝ) := by
          rw [irrational_iff_ne_rational]
          push_neg
          exact ⟨-x / y, rfl⟩
        exact rational_fact irrational_claim
    -- x = 0 を使って矛盾を導く
    rw [hx_zero] at h
    simp at h
    have hy_cast_ne_zero : (y : ℝ) ≠ 0 := by
      intro hy_zero
      have : y = 0 := rat_cast_injective (by rwa [Rat.cast_zero])
      exact hy_ne_zero this
    have sqrt_zero : Real.sqrt 2 = 0 := by
      rw [mul_eq_zero] at h
      cases h with
      | inl hy_zero => exact False.elim (hy_cast_ne_zero hy_zero)
      | inr sqrt_zero => exact sqrt_zero
    have sqrt_pos : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
    rw [sqrt_zero] at sqrt_pos
    exact lt_irrefl 0 sqrt_pos

-- 使用例
example : (0 : ℚ) + (0 : ℚ) * Real.sqrt 2 = 0 := by simp

#check rational_linear_combination_sqrt_two_zero
#check rational_linear_combination_sqrt_two_zero_direct
#check rational_linear_combination_sqrt_two_zero_basic
