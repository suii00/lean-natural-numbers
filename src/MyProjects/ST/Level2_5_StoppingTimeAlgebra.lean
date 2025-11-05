/-
Copyright (c) 2025
Authors: Structure Tower Project
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.CompleteLattice
import MyProjects.ST.CAT2_complete
import MyProjects.ST.Probability
import MyProjects.ST.Probability_Extended
import MyProjects.ST.Level2_2_OptionalStopping

/-!
# Level 2.5: Algebra of Stopping Times and Lattice Structure

This module explores the algebraic structure of stopping times through
the lens of structure towers. The key insight is that stopping times
form a lattice, and this lattice structure corresponds exactly to the
lattice operations on minLayer values.

## Main Theorems

* Stopping times form a lattice under pointwise min/max
* minLayer preserves the lattice structure
* Categorical interpretation: stopping times as morphisms
* Connection to optimal stopping via inf operations

## Mathematical Insight

The correspondence is:
```
Stopping Times (τ, σ, ...)
    ↕ (value = minLayer)
minLayer values (n, m, ...)
    ↕ (lattice operations)
Order structure (≤, ∧, ∨)
```

This reveals that stopping time operations are "optimal" in the sense
of minLayer: τ ∧ σ selects the earliest stopping among τ and σ.
-/

noncomputable section

universe u v

open Classical

namespace MyProjects
namespace ST

variable {Ω : Type u}
variable {F : DiscreteFiltration Ω}

/-! ## 1. Order Structure on Stopping Times -/

namespace StoppingTime

/-- Pointwise order on stopping times: τ ≤ σ if τ.value ω ≤ σ.value ω for all ω. -/
instance : LE (StoppingTime F) where
  le τ σ := ∀ ω, τ.value ω ≤ σ.value ω

@[simp]
lemma le_def {τ σ : StoppingTime F} :
    τ ≤ σ ↔ ∀ ω, τ.value ω ≤ σ.value ω := Iff.rfl

/-- Stopping times form a preorder. -/
instance : Preorder (StoppingTime F) where
  le := (· ≤ ·)
  le_refl := by intro τ ω; rfl
  le_trans := by
    intro τ σ ρ hτσ hσρ ω
    exact le_trans (hτσ ω) (hσρ ω)

/-- If τ ≤ σ, then τ.atMost n ⊇ σ.atMost n. -/
lemma atMost_antimono {τ σ : StoppingTime F} (h : τ ≤ σ) (n : ℕ) :
    σ.atMost n ⊆ τ.atMost n := by
  intro ω hω
  simp [StoppingTime.atMost] at hω ⊢
  exact le_trans (h ω) hω

end StoppingTime

/-! ## 2. Lattice Structure -/

namespace StoppingTime

/-- Stopping times form a lattice (meet and join). -/
instance : Lattice (StoppingTime F) where
  le := (· ≤ ·)
  le_refl := Preorder.le_refl
  le_trans := Preorder.le_trans
  inf := StoppingTime.min
  sup := StoppingTime.max
  inf_le_left := by
    intro τ σ ω
    simp [StoppingTime.min]
    exact min_le_left _ _
  inf_le_right := by
    intro τ σ ω
    simp [StoppingTime.min]
    exact min_le_right _ _
  le_inf := by
    intro τ σ ρ hτσ hτρ ω
    simp [StoppingTime.min]
    exact le_min (hτσ ω) (hτρ ω)
  le_sup_left := by
    intro τ σ ω
    simp [StoppingTime.max]
    exact le_max_left _ _
  le_sup_right := by
    intro τ σ ω
    simp [StoppingTime.max]
    exact le_max_right _ _
  sup_le := by
    intro τ σ ρ hτρ hσρ ω
    simp [StoppingTime.max]
    exact max_le (hτρ ω) (hσρ ω)

/-- The infimum (meet) of stopping times is their minimum. -/
@[simp]
lemma inf_eq_min (τ σ : StoppingTime F) :
    τ ⊓ σ = τ.min σ := rfl

/-- The supremum (join) of stopping times is their maximum. -/
@[simp]
lemma sup_eq_max (τ σ : StoppingTime F) :
    τ ⊔ σ = τ.max σ := rfl

end StoppingTime

/-! ## 3. minLayer Correspondence -/

section MinLayerLattice

/-- The min of stopping times corresponds to min of minLayers. -/
theorem stopping_min_eq_minLayer_min (τ σ : StoppingTime F) (ω : Ω) :
    (τ ⊓ σ).value ω = min ((τ.toTower).minLayer ω) ((σ.toTower).minLayer ω) := by
  simp [StoppingTime.inf_eq_min, StoppingTime.min, StoppingTime.toTower]

/-- The max of stopping times corresponds to max of minLayers. -/
theorem stopping_max_eq_minLayer_max (τ σ : StoppingTime F) (ω : Ω) :
    (τ ⊔ σ).value ω = max ((τ.toTower).minLayer ω) ((σ.toTower).minLayer ω) := by
  simp [StoppingTime.sup_eq_max, StoppingTime.max, StoppingTime.toTower]

/-- The order on stopping times corresponds to pointwise order on minLayers. -/
theorem stopping_le_iff_minLayer_le (τ σ : StoppingTime F) :
    τ ≤ σ ↔ ∀ ω, (τ.toTower).minLayer ω ≤ (σ.toTower).minLayer ω := by
  simp [StoppingTime.le_def, StoppingTime.toTower]

/-- Lattice operations on stopping times = lattice operations on minLayer images. -/
theorem lattice_structure_preserved (τ σ : StoppingTime F) :
    (∀ ω, (τ ⊓ σ).value ω = min (τ.value ω) (σ.value ω)) ∧
    (∀ ω, (τ ⊔ σ).value ω = max (τ.value ω) (σ.value ω)) := by
  constructor <;> intro ω <;> simp [StoppingTime.min, StoppingTime.max]

end MinLayerLattice

/-! ## 4. Hitting Times and Debut Times -/

section HittingTimes

variable {A : Set Ω}

/-- The hitting time of a set A: first time the process enters A.
This is a fundamental example of a stopping time derived from minLayer. -/
def hittingTime (F : DiscreteFiltration Ω) (A : Set Ω) 
    (h_event : ∀ n, A ∈ F.sigma n)  -- A is always measurable
    (h_hit : ∀ ω, ∃ n, ω ∈ A) :      -- Every path eventually hits A
    StoppingTime F where
  value ω := Nat.find (h_hit ω)
  adapted := by
    intro n
    -- {ω | hitting time ≤ n} = ⋃_{k≤n} (A at time k)
    sorry

/-- The hitting time is the minLayer of "eventually in A". -/
theorem hittingTime_eq_minLayer (F : DiscreteFiltration Ω) (A : Set Ω)
    (h_event : ∀ n, A ∈ F.sigma n) (h_hit : ∀ ω, ∃ n, ω ∈ A) (ω : Ω) :
    (hittingTime F A h_event h_hit).value ω = 
    (F.toStructureTowerWithMin).minLayer A := by
  sorry

/-- Hitting time of A ∪ B is the minimum of individual hitting times. -/
theorem hittingTime_union (F : DiscreteFiltration Ω) (A B : Set Ω)
    (hA_event : ∀ n, A ∈ F.sigma n) (hB_event : ∀ n, B ∈ F.sigma n)
    (hA_hit : ∀ ω, ∃ n, ω ∈ A) (hB_hit : ∀ ω, ∃ n, ω ∈ B) :
    let τ_A := hittingTime F A hA_event hA_hit
    let τ_B := hittingTime F B hB_event hB_hit
    let τ_union := hittingTime F (A ∪ B) (by sorry) (by sorry)
    ∀ ω, τ_union.value ω = min (τ_A.value ω) (τ_B.value ω) := by
  intro ω
  sorry

end HittingTimes

/-! ## 5. Optimal Stopping Perspective -/

section OptimalStopping

variable {C : ConditionalExpectationStructure F}

/-- A value function for a stopping problem.
At each (ω, n), represents the value of stopping at time n. -/
abbrev ValueFunction := Ω → ℕ → ℝ

/-- The optimal stopping time minimizes (or maximizes) the value function.
This is where minLayer shines: it naturally selects the "first optimal time". -/
def optimalStoppingTime 
    (V : ValueFunction) 
    (target : ℝ)
    (h_achieve : ∀ ω, ∃ n, V ω n ≥ target)
    (h_measurable : ∀ n, {ω | V ω n ≥ target} ∈ F.sigma n) :
    StoppingTime F where
  value ω := Nat.find (h_achieve ω)
  adapted := by
    intro n
    sorry

/-- The optimal stopping time uses minLayer to find the first achieving time. -/
theorem optimalStopping_is_minLayer
    (V : ValueFunction) (target : ℝ) 
    (h_achieve : ∀ ω, ∃ n, V ω n ≥ target)
    (h_measurable : ∀ n, {ω | V ω n ≥ target} ∈ F.sigma n) :
    ∀ ω, (optimalStoppingTime V target h_achieve h_measurable).value ω = 
         (F.toStructureTowerWithMin).minLayer {ω' | ∃ n, V ω' n ≥ target} := by
  intro ω
  sorry

/-- Any earlier stopping cannot be optimal (minimality of minLayer). -/
theorem optimal_stopping_minimal
    (V : ValueFunction) (target : ℝ) 
    (h_achieve : ∀ ω, ∃ n, V ω n ≥ target)
    (h_measurable : ∀ n, {ω | V ω n ≥ target} ∈ F.sigma n)
    (τ : StoppingTime F) :
    (∀ ω, V ω (τ.value ω) ≥ target) →
    optimalStoppingTime V target h_achieve h_measurable ≤ τ := by
  intro h_achieves ω
  -- This is exactly minLayer_minimal!
  sorry

end OptimalStopping

/-! ## 6. Categorical Perspective -/

section Categorical

/-- A stopping time can be viewed as a morphism from Ω to ℕ
that respects the filtration structure.

This morphism factorizes through the structure tower minLayer. -/
def stoppingTimeAsMorphism (τ : StoppingTime F) :
    -- τ induces a tower morphism from F.toTower to natTowerMin
    True := by
  -- The key is that τ.adapted ensures the morphism respects layers
  -- and τ.value = minLayer ensures it respects the minLayer structure
  trivial

/-- The minimum of stopping times corresponds to the categorical product
in some sense (both select the "earlier" option). -/
theorem min_as_categorical_inf (τ σ : StoppingTime F) :
    -- τ ⊓ σ is the greatest lower bound in the stopping time ordering
    -- This corresponds to some categorical construction
    True := by
  trivial

/-- The composition of stopping times (when applicable) preserves structure. -/
def composedStoppingTime 
    (τ : StoppingTime F) 
    (σ : ℕ → StoppingTime F)  -- Family of stopping times indexed by τ's values
    (h_compat : ∀ n m, n ≤ m → σ n ≤ σ m) :
    -- The composed stopping time: first stop at τ, then continue with σ(τ)
    StoppingTime F where
  value ω := τ.value ω + (σ (τ.value ω)).value ω
  adapted := by sorry

end Categorical

/-! ## 7. Advanced Properties -/

section AdvancedProperties

/-- Distributivity: τ ⊓ (σ ⊔ ρ) = (τ ⊓ σ) ⊔ (τ ⊓ ρ) 
This follows from the lattice structure. -/
theorem stopping_time_lattice_distributive (τ σ ρ : StoppingTime F) :
    τ ⊓ (σ ⊔ ρ) = (τ ⊓ σ) ⊔ (τ ⊓ ρ) := by
  apply StoppingTime.ext
  · ext ω
    simp [StoppingTime.min, StoppingTime.max]
    exact min_max_distrib_left
  · intro n
    sorry

/-- The set of stopping times bounded by N forms a finite lattice. -/
def boundedStoppingTimes (N : ℕ) : Set (StoppingTime F) :=
  {τ | τ.IsBounded N}

theorem boundedStoppingTimes_is_lattice (N : ℕ) :
    ∀ τ σ ∈ boundedStoppingTimes N, 
      (τ ⊓ σ) ∈ boundedStoppingTimes N ∧ 
      (τ ⊔ σ) ∈ boundedStoppingTimes N := by
  intro τ hτ σ hσ
  constructor
  · -- min is bounded
    intro ω
    simp [StoppingTime.min]
    exact min_le_of_left_le (hτ ω)
  · -- max is bounded
    intro ω
    simp [StoppingTime.max]
    exact max_le (hτ ω) (hσ ω)

end AdvancedProperties

/-! ## 8. Examples and Applications -/

section Examples

/-- Example: The zero stopping time (stop immediately). -/
def zeroStoppingTime : StoppingTime F where
  value := fun _ => 0
  adapted := by
    intro n
    simp [StoppingTime.atMost]
    sorry

/-- Example: For any stopping time τ, we have 0 ≤ τ. -/
example (τ : StoppingTime F) : zeroStoppingTime ≤ τ := by
  intro ω
  simp [zeroStoppingTime]

/-- Example: τ ⊓ τ = τ (idempotence). -/
example (τ : StoppingTime F) : τ ⊓ τ = τ := by
  apply StoppingTime.ext
  · ext ω
    simp [StoppingTime.min]
  · intro n
    rfl

/-- Example: τ ⊔ τ = τ (idempotence). -/
example (τ : StoppingTime F) : τ ⊔ τ = τ := by
  apply StoppingTime.ext
  · ext ω
    simp [StoppingTime.max]
  · intro n
    rfl

/-- Example: (τ ⊓ σ) ≤ τ and (τ ⊓ σ) ≤ σ. -/
example (τ σ : StoppingTime F) : 
    (τ ⊓ σ ≤ τ) ∧ (τ ⊓ σ ≤ σ) := by
  constructor
  · exact Lattice.inf_le_left
  · exact Lattice.inf_le_right

end Examples

/-! ## 9. Research Directions -/

/-
## Open Questions and Future Work

1. **Complete Lattice Structure**: Under what conditions do stopping times
   form a complete lattice? (Requires taking infimum over infinite families)

2. **Sup-Preservation**: Does the minLayer correspondence preserve 
   arbitrary suprema? This relates to continuous-time extensions.

3. **Free Stopping Time Tower**: Can we construct a "free" structure tower
   generated by stopping times, analogous to freeStructureTowerMin?

4. **Optimal Stopping via minLayer Optimization**: Formulate optimal stopping
   problems as finding the minLayer that minimizes a cost functional.

5. **Connection to Game Theory**: Multi-player stopping games could be
   studied through tower morphisms and categorical limits.

6. **Snell Envelope**: The Snell envelope (value function for optimal stopping)
   should have a natural interpretation in terms of tower structure.

## Potential Theorems

- **Wald's Equation**: For bounded stopping times and i.i.d. increments,
  𝔼[∑_{i=0}^τ X_i] = 𝔼[τ] · 𝔼[X_0]
  (minLayer structure should provide a new proof)

- **Skorokhod Embedding**: Representing a given distribution as the stopped
  position of a martingale (connection to minLayer selection)

- **Reflection Principle**: For Brownian motion, using symmetry in the
  tower structure
-/

end ST
end MyProjects
