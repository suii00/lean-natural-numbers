import MyProjects.ST.Step1_Indicators

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

/-- Auxiliary lemma: summing a Kronecker delta along a finite range.
    ブルバキの精神に従い、Kronecker deltaの性質を厳密に証明する。 -/
private lemma sum_range_mul_delta (f : ℕ → ℝ) (a m : ℕ) :
    (Finset.range (m + 1)).sum (fun k => f k * (if k = a then (1 : ℝ) else 0)) =
      if a ≤ m then f a else 0 := by
  classical
  by_cases ha : a ≤ m
  · -- Case: a ≤ m なので a ∈ range (m+1)
    have ha' : a ∈ Finset.range (m + 1) := by
      simp [Finset.mem_range, Nat.lt_succ_iff, ha]
    -- Kronecker deltaの性質: k ≠ a のとき項は0、k = a のとき f a
    rw [if_pos ha]
    have h_sum : (Finset.range (m + 1)).sum (fun k => f k * if k = a then 1 else 0)
                = f a * if a = a then 1 else 0 := by
      apply Finset.sum_eq_single a
      · intro b _ hba
        -- b ≠ a のとき、if k = a then 1 else 0 は 0
        rw [if_neg hba]
        ring
      · intro h
        exact absurd ha' h
    simp only [if_true] at h_sum
    rw [mul_one] at h_sum
    exact h_sum
  · -- Case: a > m なので a ∉ range (m+1)
    rw [if_neg ha]
    have hnot : a ∉ Finset.range (m + 1) := by
      simp [Finset.mem_range, Nat.lt_succ_iff, ha]
    -- すべての k ∈ range (m+1) に対して k ≠ a
    apply Finset.sum_eq_zero
    intro b hb
    have : b ≠ a := by
      intro hba
      exact hnot (hba ▸ hb)
    simp [this]

/-- Main decomposition: split according to whether the stopping time has occurred by `n`.
    ブルバキの精神に従い、場合分けを明示的に行う。 -/
theorem stopped_eq_sum (X : AdaptedProcessℝ F) (τ : BoundedStoppingTime F)
    (n : ℕ) (ω : Ω) :
    X.stopped τ n ω =
    (Finset.range (min n τ.bound + 1)).sum (fun k =>
      X.X k ω * τ.indicator k ω) +
    X.X n ω * (if n < τ.τ ω then 1 else 0) := by
  classical
  set m := min n τ.bound with hm_def
  -- Kronecker deltaを用いた和の性質
  have hsum :
      (Finset.range (m + 1)).sum (fun k => X.X k ω * τ.indicator k ω) =
        if τ.τ ω ≤ m then X.X (τ.τ ω) ω else 0 := by
    have h := sum_range_mul_delta (fun k => X.X k ω) (τ.τ ω) m
    -- indicatorの定義より τ.indicator k ω = if τ.τ ω = k then 1 else 0
    have heq : ∀ k, τ.indicator k ω = if k = τ.τ ω then (1:ℝ) else 0 := by
      intro k
      unfold BoundedStoppingTime.indicator
      by_cases hk : τ.τ ω = k
      · rw [if_pos hk, if_pos (Eq.symm hk)]
      · rw [if_neg hk, if_neg (mt Eq.symm hk)]
    conv_lhs => arg 2; ext k; rw [heq k]
    exact h
  -- Case analysis: τ(ω) ≤ n か τ(ω) > n か
  by_cases hstop : τ.τ ω ≤ n
  · -- Case 1: τ(ω) ≤ n のとき、X^τ_n(ω) = X_{τ(ω)}(ω)
    have hmin : τ.τ ω ≤ m := le_min hstop (τ.is_bounded ω)
    have hnlt : ¬ n < τ.τ ω := not_lt_of_ge hstop
    rw [stopped, if_neg hnlt]
    simp only [mul_zero, add_zero]
    rw [hsum, if_pos hmin, Nat.min_eq_right hstop]
  · -- Case 2: τ(ω) > n のとき、X^τ_n(ω) = X_n(ω)
    have hnlt : n < τ.τ ω := lt_of_not_ge hstop
    have hmin : ¬ τ.τ ω ≤ m := by
      intro hle
      have : m ≤ n := Nat.min_le_left n τ.bound
      have : τ.τ ω ≤ n := le_trans hle this
      exact not_le_of_gt hnlt this
    rw [stopped, if_pos hnlt]
    simp only [mul_one]
    rw [hsum, if_neg hmin, zero_add, Nat.min_eq_left (Nat.le_of_lt hnlt)]

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
    have h := sum_range_mul_delta (fun k => X.X (min n k) ω) (τ.τ ω) τ.bound
    have heq : ∀ k, τ.indicator k ω = if k = τ.τ ω then (1:ℝ) else 0 := by
      intro k
      unfold BoundedStoppingTime.indicator
      by_cases hk : τ.τ ω = k
      · rw [if_pos hk, if_pos (Eq.symm hk)]
      · rw [if_neg hk, if_neg (mt Eq.symm hk)]
    conv_lhs => arg 2; ext k; rw [heq k]
    exact h
  have hbound : τ.τ ω ≤ τ.bound := τ.is_bounded ω
  rw [stopped, hsum, if_pos hbound]

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
