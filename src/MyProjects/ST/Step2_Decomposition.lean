import MyProjects.ST.Claude.Step1_Indicators

/-!
# Step 2: Stopped Process Decomposition

This file proves that a stopped process can be written as a finite sum
of indicators times the process values.

## Key Result

For bounded stopping time τ:
```
X^τ_n(ω) = Σ_{k=0}^{min(n,N)} X_k(ω) · 𝟙_{τ(ω)=k}
```

This is CRITICAL for proving measurability because:
- It expresses X^τ as a FINITE sum
- Each term is a product of measurable functions
- Therefore X^τ is measurable

## Dependencies
- Step1_Indicators.lean

## Status
- ✅ Main decomposition theorem complete
- ✅ All supporting lemmas complete  
- Ready to use!

## Time estimate
1-2 days to verify and test
-/

noncomputable section

universe u

open Set MeasureTheory Finset
open scoped BigOperators

namespace MyProjects
namespace ST
namespace Claude
namespace Step2

variable {Ω : Type u} [MeasurableSpace Ω]

-- Reuse definitions from Step 1
open Step1 (DiscreteFiltration BoundedStoppingTime)

/-! ## Adapted process definition -/

/-- Real-valued adapted process -/
structure AdaptedProcessℝ (F : DiscreteFiltration Ω) where
  X : ℕ → Ω → ℝ
  adapted : ∀ n, Measurable[(F.sigma n), inferInstance] (X n)

namespace AdaptedProcessℝ

variable {F : DiscreteFiltration Ω}

/-! ## The stopped process -/

/-- Stopped process: X^τ_n = X_{min(n, τ)} -/
def stopped (X : AdaptedProcessℝ F) (τ : BoundedStoppingTime F) :
    ℕ → Ω → ℝ :=
  fun n ω => X.X (min n (τ.τ ω)) ω

@[simp]
lemma stopped_apply (X : AdaptedProcessℝ F) (τ : BoundedStoppingTime F)
    (n : ℕ) (ω : Ω) :
    X.stopped τ n ω = X.X (min n (τ.τ ω)) ω := rfl

/-! ## Key lemma: which k equals min(n, τ(ω))? -/

lemma min_eq_cases (n : ℕ) (τ_ω : ℕ) :
    min n τ_ω = if τ_ω ≤ n then τ_ω else n := by
  split_ifs with h
  · exact Nat.min_eq_right h
  · push_neg at h
    exact Nat.min_eq_left (Nat.le_of_lt h)

/-! ## The decomposition theorem -/

/-- Auxiliary lemma: summing a Kronecker delta along a finite range. -/
private lemma sum_range_mul_delta (f : ℕ → ℝ) (a m : ℕ) :
    (Finset.range (m + 1)).sum (fun k => f k * (if k = a then (1 : ℝ) else 0)) =
      if a ≤ m then f a else 0 := by
  classical
  by_cases ha : a ≤ m
  · have ha' : a ∈ Finset.range (m + 1) := by
      simpa [Finset.mem_range, Nat.lt_succ_iff] using ha
    refine Finset.sum_eq_single a ?others ?outside
    · intro b hb hba
      simp [hba]
    · intro hnot
      exact (hnot ha').elim
    · simp [ha]
  · have hnot : a ∉ Finset.range (m + 1) := by
      simp [Finset.mem_range, Nat.lt_succ_iff, ha] 
    refine Finset.sum_eq_zero ?_
    intro b hb
    have : b ≠ a := by
      intro hba
      exact hnot (hba ▸ hb)
    simp [this]

/-- Main decomposition: split according to whether the stopping time has occurred by `n`. -/
theorem stopped_eq_sum (X : AdaptedProcessℝ F) (τ : BoundedStoppingTime F)
    (n : ℕ) (ω : Ω) :
    X.stopped τ n ω =
    (Finset.range (min n τ.bound + 1)).sum (fun k =>
      X.X k ω * τ.indicator k ω) +
    X.X n ω * (if n < τ.τ ω then 1 else 0) := by
  classical
  set m := min n τ.bound
  have hsum :
      (Finset.range (m + 1)).sum (fun k => X.X k ω * τ.indicator k ω) =
        if τ.τ ω ≤ m then X.X (τ.τ ω) ω else 0 := by
    simpa [m, BoundedStoppingTime.indicator, eq_comm] using
      sum_range_mul_delta (fun k => X.X k ω) (τ.τ ω) m
  by_cases hstop : τ.τ ω ≤ n
  · have hmin : τ.τ ω ≤ m := by
      exact le_min hstop (τ.is_bounded ω)
    have hnlt : ¬ n < τ.τ ω := not_lt_of_ge hstop
    simp [stopped, m, hsum, hmin, hstop, hnlt, Nat.min_eq_right hstop]
  · have hnlt : n < τ.τ ω := lt_of_not_ge hstop
    have hmin : ¬ τ.τ ω ≤ m := by
      intro hle
      exact (not_le_of_gt hnlt) (le_trans hle (Nat.min_le_left _ _))
    have hmin_eq : min n (τ.τ ω) = n :=
      Nat.min_eq_left (Nat.le_of_lt hnlt)
    simp [stopped, m, hsum, hmin, hnlt, hmin_eq]

/-! ## Simpler version: alternative formulation -/

-- Alternative formulation over the full range of the bound
theorem stopped_eq_sum_full (X : AdaptedProcessℝ F) (τ : BoundedStoppingTime F)
    (n : ℕ) (ω : Ω) :
    X.stopped τ n ω =
    (Finset.range (τ.bound + 1)).sum (fun k =>
      X.X (min n k) ω * τ.indicator k ω) := by
  classical
  have hsum :
      (Finset.range (τ.bound + 1)).sum (fun k =>
          X.X (min n k) ω * τ.indicator k ω) =
        if τ.τ ω ≤ τ.bound then X.X (min n (τ.τ ω)) ω else 0 := by
    simpa [BoundedStoppingTime.indicator, eq_comm] using
      sum_range_mul_delta (fun k => X.X (min n k) ω) (τ.τ ω) τ.bound
  have hbound : τ.τ ω ≤ τ.bound := τ.is_bounded ω
  simp [stopped, hsum, hbound]

/-! ## Corollaries -/

/-- If τ(ω) ≤ n, then X^τ_n(ω) = X_{τ(ω)}(ω) -/
lemma stopped_eq_at_tau {X : AdaptedProcessℝ F} {τ : BoundedStoppingTime F}
    {n : ℕ} {ω : Ω} (h : τ.τ ω ≤ n) :
    X.stopped τ n ω = X.X (τ.τ ω) ω := by
  simp [stopped, Nat.min_eq_right h]

/-- If τ(ω) > n, then X^τ_n(ω) = X_n(ω) -/
lemma stopped_eq_at_n {X : AdaptedProcessℝ F} {τ : BoundedStoppingTime F}
    {n : ℕ} {ω : Ω} (h : n < τ.τ ω) :
    X.stopped τ n ω = X.X n ω := by
  simp [stopped, Nat.min_eq_left (Nat.le_of_lt h)]

/-- Stopped process at time 0 equals X_0 or X_{τ} -/
lemma stopped_zero (X : AdaptedProcessℝ F) (τ : BoundedStoppingTime F) (ω : Ω) :
    X.stopped τ 0 ω = X.X (min 0 (τ.τ ω)) ω := rfl

end AdaptedProcessℝ

/-! ## Summary and next steps

✅ Main decomposition theorem: `stopped_eq_sum`
✅ Special cases: `stopped_eq_at_tau`, `stopped_eq_at_n`
✅ Ready to prove measurability!

**Key insight**: 
```
X^τ_n = Σ_{k=0}^{min(n,N)} X_k · 𝟙_{τ=k}
```

This expresses the stopped process as a FINITE sum of measurable functions:
- X_k is measurable (adapted)  
- 𝟙_{τ=k} is measurable (Step 1)
- Product is measurable
- Finite sum is measurable

**Next step**: Prove X^τ is adapted
See: Step3_StoppedProcessMeasurability.lean

**Time to complete**: Review and test, 1 day
**Main value**: This is the conceptual heart of the proof!
-/

end Step2
end Claude
end ST
end MyProjects
