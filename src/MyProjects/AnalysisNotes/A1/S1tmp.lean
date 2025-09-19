import Mathlib

noncomputable section
open scoped Real Interval

lemma s1_q2_tmp (a b m n : ℝ) :
    ∫ x in a..b, m * x + n = m * ((b ^ 2 - a ^ 2) / 2) + n * (b - a) := by
  classical
  let F : ℝ → ℝ := fun x => m * x ^ 2 / 2 + n * x
  have h_deriv : ∀ x ∈ Set.uIcc a b, HasDerivAt F (m * x + n) x := by
    intro x hx
    have hm : HasDerivAt (fun x : ℝ => m * x ^ 2 / 2) (m * x) x := by
      have := ((hasDerivAt_pow (n := 2) x).mul_const m).div_const (2 : ℝ)
      simpa [F, pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using this
    have hn : HasDerivAt (fun x : ℝ => n * x) n x := by
      simpa [mul_comm] using (hasDerivAt_mul_const (c := n) (x := x))
    simpa [F, add_comm, add_left_comm, add_assoc, mul_add]
      using hm.add hn
  have h_int : IntervalIntegrable (fun x : ℝ => m * x + n) MeasureTheory.volume a b := by
    refine ((continuous_const : Continuous fun _ : ℝ => m).mul continuous_id).add
        (continuous_const : Continuous fun _ : ℝ => n)
      |>.intervalIntegrable (μ := MeasureTheory.volume) (a := a) (b := b)
  have h_eq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b)
    (f := F) (f' := fun x : ℝ => m * x + n) h_deriv h_int
  have h_twice : 2 * (F b - F a)
      = m * (b ^ 2 - a ^ 2) + (2 * n) * (b - a) := by
    simp [F, pow_two, div_eq_mul_inv, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc, two_mul]
  have h_rhs : 2 * (m * ((b ^ 2 - a ^ 2) / 2) + n * (b - a))
      = m * (b ^ 2 - a ^ 2) + (2 * n) * (b - a) := by
    simp [div_eq_mul_inv, mul_add, add_comm, add_left_comm, add_assoc, pow_two,
      mul_comm, mul_left_comm, mul_assoc, two_mul]
  have h_eq_twice := by
    simpa [h_rhs, mul_comm] using h_twice
  have h₂ : (2 : ℝ) ≠ 0 := two_ne_zero
  have h_eval : F b - F a = m * ((b ^ 2 - a ^ 2) / 2) + n * (b - a) :=
    (mul_right_cancel₀ h₂).1 <|
      by simpa [mul_add] using h_eq_twice
  simpa [F, h_eval] using h_eq

end
