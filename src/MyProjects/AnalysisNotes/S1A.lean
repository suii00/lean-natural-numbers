import Mathlib

/-!
# Session S1A: 追加課題（提案）

S1A.md の提案から、微積分学の基本定理の一端と積分に関する平均値の定理を Lean で扱うための骨組みを用意する。
-/

noncomputable section

open scoped Interval Topology BigOperators
open MeasureTheory
open Set

namespace Zen
namespace Analysis1
namespace S1
namespace Next

/--
関数 F を F t = ∫ x in a..t, f x と定めると、連続関数 f に対して F の導関数が f と一致することを述べる主張。
-/
theorem s1_a_q2 (a : ℝ) (f : ℝ → ℝ) (hf : Continuous f) (t : ℝ) :
    HasDerivAt (fun t => ∫ x in a..t, f x) (f t) t := by
  simpa using
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

/--
連続関数 f について、区間 [a, b] の積分値がある点 c ∈ [a, b] での値 f c と区間の長さ (b - a) の積に等しくなることを示す積分に関する平均値の定理。
-/
theorem s1_a_q5 (a b : ℝ) (f : ℝ → ℝ)
    (h_cont : ContinuousOn f (Icc a b)) (hab : a < b) :
    ∃ c ∈ Icc a b, ∫ x in a..b, f x = (b - a) * f c := by
  classical
  have hle : a ≤ b := hab.le
  have h_integrable : IntegrableOn f (Icc a b) :=
    h_cont.integrableOn_compact isCompact_Icc
  have h_integrable_u : IntegrableOn f (uIcc a b) := by
    simpa [uIcc_of_le hle] using h_integrable
  set F : ℝ → ℝ := fun t => ∫ x in a..t, f x
  set avg : ℝ := (∫ x in a..b, f x) / (b - a)
  have hba_ne : (b - a) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  have hint_ab : IntervalIntegrable f volume a b := by
    have := MeasureTheory.IntegrableOn.intervalIntegrable (μ := volume) h_integrable_u
    simpa [uIcc_of_le hle, min_eq_left hle, max_eq_right hle] using this
  have hF_deriv : ∀ x ∈ Ioo a b, HasDerivAt F (f x) x := by
    intro x hx
    have hx_le : x ≤ b := hx.2.le
    have hx_nhds : Icc a b ∈ 𝓝 x :=
      Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hx) Ioo_subset_Icc_self
    have h_cont_at : ContinuousAt f x := h_cont.continuousAt hx_nhds
    have h_subset : Icc a x ⊆ Icc a b := by
      intro y hy; exact ⟨hy.1, hy.2.trans hx_le⟩
    have h_int_set : IntegrableOn f (Icc a x) := h_integrable.mono_set h_subset
    have h_int_u : IntegrableOn f (uIcc a x) := by
      simpa [uIcc_of_le hx.1.le] using h_int_set
    have h_int_ax : IntervalIntegrable f volume a x :=
      MeasureTheory.IntegrableOn.intervalIntegrable (μ := volume) h_int_u
    exact
      intervalIntegral.integral_hasDerivAt_right h_int_ax
        h_cont_at.aestronglyMeasurable.stronglyMeasurableAtFilter h_cont_at
  have hF_cont : ContinuousOn F (Icc a b) := by
    intro x hx
    have hx_mem : x ∈ Icc a b := hx
    by_cases hx_int : x ∈ Ioo a b
    · exact (hF_deriv x hx_int).continuousAt.continuousWithinAt
    · have hx_end : x = a ∨ x = b := by
        have hx_left := hx.1
        have hx_right := hx.2
        have hx_cases : ¬ (a < x ∧ x < b) := hx_int
        by_cases h₁ : a < x
        · have h₂ : b ≤ x := le_of_not_gt fun hxb => hx_cases ⟨h₁, hxb⟩
          exact Or.inr (le_antisymm hx_right h₂)
        · have h₂ : x ≤ a := le_of_not_gt h₁
          exact Or.inl (le_antisymm h₂ hx_left)
      have hμ_singleton : volume ({x} : Set ℝ) = 0 := by
        simpa using (measure_singleton x : volume {x} = 0)
      cases hx_end with
      | inl hxa =>
          have hx' : ContinuousWithinAt F (Icc a b) a := by
            simpa [F, hxa] using
              intervalIntegral.continuousWithinAt_primitive (μ := volume) (f := f)
                (a := a) (b₁ := a) (b₂ := b) hμ_singleton hint_ab
          simpa [hxa] using hx'
      | inr hxb =>
          have hx' : ContinuousWithinAt F (Icc a b) b := by
            simpa [F, hxb] using
              intervalIntegral.continuousWithinAt_primitive (μ := volume) (f := f)
                (a := a) (b₁ := a) (b₂ := b) hμ_singleton hint_ab
          simpa [hxb] using hx'
  have hG_cont : ContinuousOn (fun t => (t - a) * avg) (Icc a b) :=
    ((continuous_id.sub continuous_const).mul continuous_const).continuousOn
  have h_cont_h : ContinuousOn (fun t => F t - (t - a) * avg) (Icc a b) :=
    hF_cont.sub hG_cont
  have h_deriv_h : ∀ x ∈ Ioo a b, HasDerivAt (fun t => F t - (t - a) * avg) (f x - avg) x := by
    intro x hx
    have hF := hF_deriv x hx
    have h_id : HasDerivAt (fun t => t) (1 : ℝ) x := hasDerivAt_id x
    have hG : HasDerivAt (fun t => (t - a) * avg) avg x := by
      simpa [one_mul] using ((h_id.sub_const a).mul_const avg)
    simpa [F] using hF.sub hG
  have h_zero_a : (fun t => F t - (t - a) * avg) a = 0 := by
    simp [F, avg]
  have h_zero_b : (fun t => F t - (t - a) * avg) b = 0 := by
    simp [F, avg]
  have h_equal :
      (fun t => F t - (t - a) * avg) a = (fun t => F t - (t - a) * avg) b :=
    by simpa [h_zero_a, h_zero_b]
  obtain ⟨c, hc, hc_deriv⟩ :=
    exists_hasDerivAt_eq_zero hab h_cont_h h_equal h_deriv_h
  have hcIcc : c ∈ Icc a b := ⟨hc.1.le, hc.2.le⟩
  have hfc_eq : f c = avg := sub_eq_zero.mp hc_deriv
  have h_int_eq' : (b - a) * avg = ∫ x in a..b, f x := by
    simp [avg, hba_ne]
  refine ⟨c, hcIcc, ?_⟩
  simpa [hfc_eq, h_int_eq'.symm]

end Next
end S1
end Analysis1
end Zen
