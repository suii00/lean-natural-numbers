import Mathlib

noncomputable section

open Real BigOperators MeasureTheory Filter Topology
open scoped Real BigOperators Topology Interval

namespace Zen.Analysis1.S1

lemma zero_mem_uIcc_neg_pos (a : ℝ) : (0 : ℝ) ∈ [[-a, a]] := by
  by_cases h : a ≤ 0
  · exact (Set.mem_uIcc).2 <| Or.inr ⟨h, by simpa using neg_nonneg.mpr h⟩
  · have h' : 0 ≤ a := le_of_lt (lt_of_not_ge h)
    exact (Set.mem_uIcc).2 <| Or.inl ⟨by simpa using neg_nonpos.mpr h', h'⟩

lemma neg_mem_uIcc_neg_pos (a : ℝ) : (-a : ℝ) ∈ [[-a, a]] := Set.left_mem_uIcc
lemma pos_mem_uIcc_neg_pos (a : ℝ) : (a : ℝ) ∈ [[-a, a]] := Set.right_mem_uIcc

theorem s1_q1 (a b c : ℝ) :
    ∫ x in a..b, c = (b - a) * c := by
  simpa using intervalIntegral.integral_const (a := a) (b := b) (c := c)

theorem s1_q2 (a b m n : ℝ) :
    ∫ x in a..b, m * x + n
      = m * ((b ^ 2 - a ^ 2) / 2) + n * (b - a) := by
  classical
  have h_mx : IntervalIntegrable (fun x : ℝ => m * x) volume a b :=
    ((continuous_const : Continuous fun _ : ℝ => m).mul continuous_id)
      .intervalIntegrable (μ := volume) (a := a) (b := b)
  have h_const : IntervalIntegrable (fun _ : ℝ => n) volume a b :=
    (continuous_const : Continuous fun _ : ℝ => n)
      .intervalIntegrable (μ := volume) (a := a) (b := b)
  have h_id : ∫ x in a..b, x = (b ^ 2 - a ^ 2) / 2 := by
    simpa [pow_two] using
      (intervalIntegral.integral_pow (n := (1 : ℕ)) (a := a) (b := b))
  have h_mx_eval : ∫ x in a..b, m * x = m * ((b ^ 2 - a ^ 2) / 2) := by
    simpa [h_id] using
      (intervalIntegral.integral_const_mul (μ := volume) (a := a) (b := b)
        (r := m) (f := fun x : ℝ => x))
  have h_const_eval : ∫ x in a..b, n = (b - a) * n := by
    simpa using intervalIntegral.integral_const (a := a) (b := b) (c := n)
  calc
    ∫ x in a..b, m * x + n
        = (∫ x in a..b, m * x) + (∫ x in a..b, n) :=
            (intervalIntegral.integral_add (hf := h_mx) (hg := h_const))
    _ = m * ((b ^ 2 - a ^ 2) / 2) + (b - a) * n := by
        simp [h_mx_eval, h_const_eval]
    _ = m * ((b ^ 2 - a ^ 2) / 2) + n * (b - a) := by
        ring_nf

theorem s1_q3
    (a : ℝ) (f : ℝ → ℝ)
    (hodd : Function.Odd f)
    (hf : IntervalIntegrable f volume (-a) a) :
    ∫ x in -a..a, f x = 0 := by
  classical
  have hcomp := intervalIntegral.integral_comp_neg (f := f) (a := (-a : ℝ)) (b := (a : ℝ))
  have hcongr := intervalIntegral.integral_congr (μ := volume)
    (a := (-a : ℝ)) (b := a)
    (f := fun x : ℝ => f (-x)) (g := fun x : ℝ => -f x)
    (by
      intro x hx
      simpa using hodd x)
  have hI : ∫ x in -a..a, f x = -∫ x in -a..a, f x := by
    simpa [hcongr, intervalIntegral.integral_neg] using hcomp.symm
  have hsum : (∫ x in -a..a, f x) + ∫ x in -a..a, f x = 0 :=
    (eq_neg_iff_add_eq_zero).1 hI
  have hmul : (2 : ℝ) * ∫ x in -a..a, f x = 0 := by
    simpa [two_mul] using hsum
  have : ∫ x in -a..a, f x = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (two_ne_zero : (2 : ℝ) ≠ 0)
  simpa using this

theorem s1_q4 :
    ∫ x in (-1 : ℝ)..2, |x| = (5 : ℝ) / 2 := by
  classical
  have hab : IntervalIntegrable (fun x : ℝ => |x|) volume (-1 : ℝ) 0 := by
    simpa using
      (continuous_abs : Continuous fun x : ℝ => |x|).intervalIntegrable
        (μ := volume) (a := (-1 : ℝ)) (b := (0 : ℝ))
  have hbc : IntervalIntegrable (fun x : ℝ => |x|) volume (0 : ℝ) 2 := by
    simpa using
      (continuous_abs : Continuous fun x : ℝ => |x|).intervalIntegrable
        (μ := volume) (a := (0 : ℝ)) (b := (2 : ℝ))
  have hsplit := (intervalIntegral.integral_add_adjacent_intervals
    (μ := volume) (f := fun x : ℝ => |x|)
    (a := (-1 : ℝ)) (b := (0 : ℝ)) (c := (2 : ℝ))
    (hab := hab) (hbc := hbc)).symm
  have h_id_neg : ∫ x in (-1 : ℝ)..0, x = -((1 : ℝ) / 2) := by
    simpa [pow_two] using
      (intervalIntegral.integral_pow (n := (1 : ℕ)) (a := (-1 : ℝ)) (b := (0 : ℝ)))
  have hneg : ∫ x in (-1 : ℝ)..0, |x| = (1 : ℝ) / 2 := by
    have hcongr := intervalIntegral.integral_congr (μ := volume)
      (a := (-1 : ℝ)) (b := (0 : ℝ))
      (f := fun x : ℝ => |x|) (g := fun x : ℝ => -x)
      (by
        intro x hx
        have hxIcc : x ∈ Set.Icc (-1 : ℝ) 0 := by
          simpa [Set.uIcc_of_le (show (-1 : ℝ) ≤ 0 by norm_num)] using hx
        have hx' : x ≤ 0 := hxIcc.2
        simp [abs_of_nonpos hx'])
    have := hcongr.trans (intervalIntegral.integral_neg
      (f := fun x : ℝ => x) (a := (-1 : ℝ)) (b := (0 : ℝ)))
    simpa [h_id_neg] using this
  have h_id_pos : ∫ x in (0 : ℝ)..2, x = ((2 : ℝ) ^ 2 - (0 : ℝ) ^ 2) / 2 := by
    simpa [pow_two] using
      (intervalIntegral.integral_pow (n := (1 : ℕ)) (a := (0 : ℝ)) (b := (2 : ℝ)))
  have hpos : ∫ x in (0 : ℝ)..2, |x| = 2 := by
    have hcongr := intervalIntegral.integral_congr (μ := volume)
      (a := (0 : ℝ)) (b := (2 : ℝ))
      (f := fun x : ℝ => |x|) (g := fun x : ℝ => x)
      (by
        intro x hx
        have hxIcc : x ∈ Set.Icc (0 : ℝ) 2 := by
          simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 2 by norm_num)] using hx
        have hx' : 0 ≤ x := hxIcc.1
        simp [abs_of_nonneg hx'])
    have : ∫ x in (0 : ℝ)..2, |x| = ((2 : ℝ) ^ 2 - (0 : ℝ) ^ 2) / 2 := by
      simpa [h_id_pos] using hcongr
    simpa [pow_two] using this
  calc
    ∫ x in (-1 : ℝ)..2, |x|
        = ∫ x in (-1 : ℝ)..0, |x| + ∫ x in (0 : ℝ)..2, |x| := by
          simpa [add_comm] using hsplit
    _ = 1 / 2 + 2 := by simp [hneg, hpos]
    _ = (5 : ℝ) / 2 := by norm_num

theorem s1_q5
    {a b : ℝ} (h_ab : a ≤ b) (f : ℝ → ℝ)
    (h_nonneg : ∀ x ∈ Set.Icc a b, 0 ≤ f x)
    (hf : IntervalIntegrable f volume a b) :
    0 ≤ ∫ x in a..b, f x := by
  simpa using intervalIntegral.integral_nonneg (μ := volume) (f := f) h_ab h_nonneg

def fe (f : ℝ → ℝ) : ℝ → ℝ := fun x => (f x + f (-x)) / 2
def fo (f : ℝ → ℝ) : ℝ → ℝ := fun x => (f x - f (-x)) / 2

theorem s1_challenge
    (a : ℝ) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (-a) a) :
    ∫ x in -a..a, f x = 2 * ∫ x in (0 : ℝ)..a, fe f x := by
  classical
  have hf_neg' := hf.comp_sub_left (c := (0 : ℝ))
  have hf_neg : IntervalIntegrable (fun x : ℝ => f (-x)) volume (-a) a := hf_neg'.symm
  have h_sum : IntervalIntegrable (fun x : ℝ => f x + f (-x)) volume (-a) a := hf.add hf_neg
  have h_diff : IntervalIntegrable (fun x : ℝ => f x - f (-x)) volume (-a) a :=
    hf.sub hf_neg
  have h_fe : IntervalIntegrable (fe f) volume (-a) a := by
    refine (IntervalIntegrable.const_mul (hf := h_sum) (c := (1 / 2 : ℝ))).congr ?_
    have : (fun x : ℝ => (1 / 2 : ℝ) * (f x + f (-x))) =ᵐ[volume]
        fun x => fe f x := Filter.Eventually.of_forall (by
          intro x; simp [fe, div_eq_mul_inv])
    exact ae_restrict_of_ae this
  have h_fo : IntervalIntegrable (fo f) volume (-a) a := by
    refine (IntervalIntegrable.const_mul (hf := h_diff) (c := (1 / 2 : ℝ))).congr ?_
    have : (fun x : ℝ => (1 / 2 : ℝ) * (f x - f (-x))) =ᵐ[volume]
        fun x => fo f x := Filter.Eventually.of_forall (by
          intro x; simp [fo, div_eq_mul_inv, sub_eq_add_neg])
    exact ae_restrict_of_ae this
  have h_even_fe : Function.Even (fe f) := by
    intro x; simp [fe, add_comm]
  have h_odd_fo : Function.Odd (fo f) := by
    intro x; simp [fo, sub_eq_add_neg]
  have h_integrand :
      Set.EqOn (fun x : ℝ => f x)
        (fun x : ℝ => fe f x + fo f x) [[(-a : ℝ), a]] := by
    intro x hx; simp [fe, fo, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
  have h_integral := intervalIntegral.integral_congr (μ := volume)
    (a := (-a : ℝ)) (b := (a : ℝ)) h_integrand
  have h_add := intervalIntegral.integral_add (hf := h_fe) (hg := h_fo)
  have h_fo_zero : ∫ x in -a..a, fo f x = 0 :=
    s1_q3 a (fo f) h_odd_fo h_fo
  have h_fe_neg : IntervalIntegrable (fe f) volume (-a) 0 :=
    h_fe.mono_set <|
      Set.uIcc_subset_uIcc (neg_mem_uIcc_neg_pos a) (zero_mem_uIcc_neg_pos a)
  have h_fe_pos : IntervalIntegrable (fe f) volume 0 a :=
    h_fe.mono_set <|
      Set.uIcc_subset_uIcc (zero_mem_uIcc_neg_pos a) (pos_mem_uIcc_neg_pos a)
  have h_split_fe := (intervalIntegral.integral_add_adjacent_intervals
    (μ := volume) (f := fe f) (a := (-a : ℝ)) (b := (0 : ℝ)) (c := (a : ℝ))
    (hab := h_fe_neg) (hbc := h_fe_pos)).symm
  have h_half : ∫ x in (-a : ℝ)..0, fe f x = ∫ x in (0 : ℝ)..a, fe f x := by
    have hcomp := intervalIntegral.integral_comp_neg (f := fe f)
      (a := (0 : ℝ)) (b := (a : ℝ))
    have hcongr := intervalIntegral.integral_congr (μ := volume)
      (a := (0 : ℝ)) (b := (a : ℝ))
      (f := fun x => fe f (-x)) (g := fun x => fe f x)
      (by intro x hx; simpa using h_even_fe x)
    simpa [neg_zero] using (Eq.symm hcomp).trans hcongr
    exact hcomp.symm.trans hcongr
    have h_fe_split :
      ∫ x in (-a : ℝ)..a, fe f x = 2 * ∫ x in (0 : ℝ)..a, fe f x := by
    calc
      ∫ x in (-a : ℝ)..a, fe f x
          = ∫ x in (-a : ℝ)..0, fe f x + ∫ x in (0 : ℝ)..a, fe f x := by
            simpa [add_comm] using h_split_fe
      _ = ∫ x in (0 : ℝ)..a, fe f x + ∫ x in (0 : ℝ)..a, fe f x := by
            simp [h_half]
      _ = 2 * ∫ x in (0 : ℝ)..a, fe f x := by
            ring_nf
  calc
    ∫ x in -a..a, f x
        = ∫ x in -a..a, fe f x + fo f x := by
            simpa using h_integral
        _ = ∫ x in -a..a, fe f x + ∫ x in -a..a, fo f x := by
          simpa using h_add
    _ = ∫ x in -a..a, fe f x := by simp [h_fo_zero]
    _ = 2 * ∫ x in (0 : ℝ)..a, fe f x := h_fe_split

example (a b c : ℝ) : ∫ x in a..b, c = (b - a) * c := by
  simpa using intervalIntegral.integral_const (a := a) (b := b) (c := c)

end Zen.Analysis1.S1
