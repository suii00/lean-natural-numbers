import Mathlib.Data.Real.Irrational
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Rat.Cast

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
      have x_cast_ne_zero : (x : ℝ) ≠ 0 := by
        intro hx_eq_zero
        have x_eq_zero : x = 0 := Rat.cast_injective (by rwa [Rat.cast_zero])
        exact hx_ne_zero x_eq_zero
      exact x_cast_ne_zero h
    · -- y ≠ 0 の場合
      have y_cast_ne_zero : (y : ℝ) ≠ 0 := by
        intro hy_eq_zero
        have y_eq_zero : y = 0 := Rat.cast_injective (by rwa [Rat.cast_zero])
        exact hy y_eq_zero
      -- h から √2 = -x/y を導く
      have h_sqrt : Real.sqrt 2 = -(x : ℝ) / (y : ℝ) := by
        field_simp [y_cast_ne_zero] at h ⊢
        linarith
      -- -x/y は有理数なので √2 が有理数になり矛盾
      have rational_sqrt : ∃ q : ℚ, (q : ℝ) = Real.sqrt 2 := by
        use -x / y
        rw [h_sqrt]
        simp [Rat.cast_neg, Rat.cast_div]
      obtain ⟨q, hq⟩ := rational_sqrt
      have q_not_irrational : ¬ Irrational (q : ℝ) := by
        rw [irrational_iff_ne_rational]
        push_neg
        exact ⟨q, rfl⟩
      rw [← hq] at q_not_irrational
      exact q_not_irrational sqrt_two_irrational
  · -- y = 0 を証明
    by_contra hy_ne_zero
    -- 最初の部分と同様の論理で x = 0 を示し、それを使って矛盾を導く
    have hx_zero : x = 0 := by
      by_contra hx_ne_zero
      by_cases hy_zero : y = 0
      · -- y = 0, x ≠ 0 の場合
        rw [hy_zero] at h
        simp at h
        have x_cast_ne_zero : (x : ℝ) ≠ 0 := by
          intro hx_eq_zero
          have x_eq_zero : x = 0 := Rat.cast_injective (by rwa [Rat.cast_zero])
          exact hx_ne_zero x_eq_zero
        exact x_cast_ne_zero h
      · -- x ≠ 0, y ≠ 0 の場合
        have y_cast_ne_zero : (y : ℝ) ≠ 0 := by
          intro hy_eq_zero
          have y_eq_zero : y = 0 := Rat.cast_injective (by rwa [Rat.cast_zero])
          exact hy_zero y_eq_zero
        have h_sqrt : Real.sqrt 2 = -(x : ℝ) / (y : ℝ) := by
          field_simp [y_cast_ne_zero] at h ⊢
          linarith
        have rational_sqrt : ∃ q : ℚ, (q : ℝ) = Real.sqrt 2 := by
          use -x / y
          rw [h_sqrt]
          simp [Rat.cast_neg, Rat.cast_div]
        obtain ⟨q, hq⟩ := rational_sqrt
        have q_not_irrational : ¬ Irrational (q : ℝ) := by
          rw [irrational_iff_ne_rational]
          push_neg
          exact ⟨q, rfl⟩
        rw [← hq] at q_not_irrational
        exact q_not_irrational sqrt_two_irrational
    -- x = 0 を代入
    rw [hx_zero] at h
    simp at h
    -- y * √2 = 0 かつ y ≠ 0 なので √2 = 0 となるが、これは矛盾
    have y_cast_ne_zero : (y : ℝ) ≠ 0 := by
      intro hy_eq_zero
      have y_eq_zero : y = 0 := Rat.cast_injective (by rwa [Rat.cast_zero])
      exact hy_ne_zero y_eq_zero
    -- y * √2 = 0 かつ y ≠ 0 から √2 = 0 を導く
    have sqrt_zero : Real.sqrt 2 = 0 := by
      have : (y : ℝ) * Real.sqrt 2 = 0 := h
      have : Real.sqrt 2 = 0 := by
        rw [← one_mul (Real.sqrt 2)]
        rw [← div_mul_cancel (1 : ℝ) y_cast_ne_zero]
        rw [one_div, mul_inv_cancel_left_of_imp_ne]
        · rw [← this, zero_mul]
        · exact y_cast_ne_zero
      exact this
    -- しかし √2 > 0 なので矛盾
    have sqrt_pos : Real.sqrt 2 > 0 := by
      exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
    rw [sqrt_zero] at sqrt_pos
    exact lt_irrefl 0 sqrt_pos

-- より簡潔なバージョン
theorem rational_linear_combination_sqrt_two_zero_simple
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
#check rational_linear_combination_sqrt_two_zero_simple

-- 使用例
example : (0 : ℚ) + (0 : ℚ) * Real.sqrt 2 = 0 := by simp