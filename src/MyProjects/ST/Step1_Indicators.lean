import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-
# Step 1: Stopping Time Indicators

Lean version of the basic indicator lemmas used in Phase 1.
-/

noncomputable section

universe u

open Set MeasureTheory

namespace MyProjects
namespace ST
namespace Claude
namespace Step1

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Simplified discrete filtration -/
structure DiscreteFiltration (Ω : Type u) [MeasurableSpace Ω] where
  sigma : ℕ → MeasurableSpace Ω
  adapted : ∀ {m n : ℕ}, m ≤ n → sigma m ≤ sigma n
  bounded : ∀ n, sigma n ≤ (inferInstance : MeasurableSpace Ω)

/-- Simplified bounded stopping time (ℕ-valued) -/
structure BoundedStoppingTime (F : DiscreteFiltration Ω) where
  τ : Ω → ℕ
  bound : ℕ
  is_bounded : ∀ ω, τ ω ≤ bound
  adapted : ∀ n, MeasurableSet[(F.sigma n)] {ω | τ ω ≤ n}

namespace BoundedStoppingTime

variable {F : DiscreteFiltration Ω} (τ : BoundedStoppingTime F)

/-- Indicator function for the event `{τ = k}`. -/
def indicator (k : ℕ) : Ω → ℝ :=
  fun ω => if τ.τ ω = k then 1 else 0

@[simp]
lemma indicator_apply (k : ℕ) (ω : Ω) :
    τ.indicator k ω = if τ.τ ω = k then 1 else 0 := rfl

lemma indicator_eq_one {k : ℕ} {ω : Ω} :
    τ.indicator k ω = 1 ↔ τ.τ ω = k := by
  simp [indicator]

lemma indicator_eq_zero {k : ℕ} {ω : Ω} :
    τ.indicator k ω = 0 ↔ τ.τ ω ≠ k := by
  simp [indicator]

/-- `{τ = k.succ}` is `{τ ≤ k.succ} \ {τ ≤ k}`. -/
lemma set_eq_inter_compl_succ (k : ℕ) :
    {ω | τ.τ ω = k.succ} =
      {ω | τ.τ ω ≤ k.succ} ∩ {ω | τ.τ ω ≤ k}ᶜ := by
  ext ω; constructor
  · intro hω
    have hω' : τ.τ ω = k.succ := by
      simpa [Set.mem_setOf_eq] using hω
    simp [Set.mem_setOf_eq, hω']
  · rintro ⟨hle, hnot⟩
    have hlt : k < τ.τ ω := Nat.lt_of_not_ge hnot
    have : τ.τ ω = k.succ := Nat.le_antisymm hle (Nat.succ_le_of_lt hlt)
    simp [Set.mem_setOf_eq, this]

/-- `{τ = 0}` equals `{τ ≤ 0}`. -/
lemma set_eq_zero_eq_le :
    {ω | τ.τ ω = 0} = {ω | τ.τ ω ≤ 0} := by
  ext ω
  constructor
  · intro hω
    have hω' : τ.τ ω = 0 := by simpa [Set.mem_setOf_eq] using hω
    simp [Set.mem_setOf_eq, hω']
  · intro hω
    have hle : τ.τ ω ≤ 0 := by simpa [Set.mem_setOf_eq] using hω
    have hω' : τ.τ ω = 0 := Nat.le_zero.mp hle
    simp [Set.mem_setOf_eq, hω']

/-- `{τ = k}` is measurable with respect to `F.sigma n` when `k ≤ n`. -/
theorem set_eq_measurable (k n : ℕ) (hkn : k ≤ n) :
    MeasurableSet[(F.sigma n)] {ω | τ.τ ω = k} := by
  classical
  by_cases hk0 : k = 0
  · subst hk0
    have h₀ :
        MeasurableSet[(F.sigma 0)] {ω | τ.τ ω = 0} := by
      simpa [set_eq_zero_eq_le τ] using τ.adapted 0
    exact (F.adapted hkn) _ h₀
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    subst hk
    have hk_le : k.succ ≤ n := by simpa using hkn
    have hk_le_n : k ≤ n := le_trans (Nat.le_succ k) hk_le
    have h₁ :
        MeasurableSet[(F.sigma n)] {ω | τ.τ ω ≤ k.succ} :=
      (F.adapted hk_le) _ (τ.adapted k.succ)
    have h₂ :
        MeasurableSet[(F.sigma n)] {ω | τ.τ ω ≤ k} :=
      (F.adapted hk_le_n) _ (τ.adapted k)
    have hx :
        {ω | τ.τ ω = k.succ} =
          {ω | τ.τ ω ≤ k.succ} ∩ {ω | τ.τ ω ≤ k}ᶜ :=
      set_eq_inter_compl_succ (τ := τ) k
    simpa [hx] using h₁.inter h₂.compl

/-- The indicator is measurable whenever `k ≤ n`. -/
theorem indicator_measurable (k n : ℕ) (hkn : k ≤ n) :
    Measurable[(F.sigma n), (inferInstance : MeasurableSpace ℝ)]
      (τ.indicator k) := by
  classical
  have hset := set_eq_measurable (τ := τ) k n hkn
  have hite :
      Measurable[(F.sigma n), inferInstance]
        (fun ω => if ω ∈ {ω | τ.τ ω = k} then (1 : ℝ) else 0) :=
    Measurable.ite hset measurable_const measurable_const
  have hrewrite :
      (fun ω => if ω ∈ {ω | τ.τ ω = k} then (1 : ℝ) else 0) =
        τ.indicator k := by
    funext ω
    simp [indicator, Set.mem_setOf_eq]
  simpa [hrewrite] using hite

/-- Absolute value of the indicator is bounded by `1`. -/
lemma indicator_bounded (k : ℕ) :
    ∀ ω, |τ.indicator k ω| ≤ 1 := by
  intro ω
  by_cases h : τ.τ ω = k
  · simp [indicator, h]
  · simp [indicator, h, abs_zero]

/-- Indicator values are non-negative. -/
lemma indicator_nonneg (k : ℕ) :
    ∀ ω, 0 ≤ τ.indicator k ω := by
  intro ω
  by_cases h : τ.τ ω = k
  · simp [indicator, h]
  · simp [indicator, h]

/-- Indicator evaluated at `τ ω` equals `1`. -/
lemma indicator_at_value (ω : Ω) :
    τ.indicator (τ.τ ω) ω = 1 := by
  simp [indicator]

end BoundedStoppingTime

end Step1
end Claude
end ST
end MyProjects
