/-
Copyright (c) 2025
Authors: Structure Tower Project
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import MyProjects.ST.CAT2_complete
import MyProjects.ST.Probability
import MyProjects.ST.Level2_2_OptionalStopping

/-
# Level 2.5: Algebraic Operations on Stopping Times

In the Bourbaki-inspired set-theoretic spirit of `Probability.md`, this file
develops the elementary algebra of discrete stopping times.  Instead of relying
on measure-theoretic closure properties of σ-algebras, we reason directly with
the pointwise values of stopping times and the associated `minLayer`
description supplied by structure towers.

Main takeaways:
* A natural order on stopping times is given by pointwise comparison of their
  values.
* Pointwise minimum/maximum/sum encode the usual lattice-style operations on
  stopping times; their basic inequalities follow from the corresponding facts
  about natural numbers.
* The `minLayer` viewpoint explains these operations geometrically: taking the
  minimum (resp. maximum) of stopping times amounts to taking the infimum
  (resp. supremum) of the layers in the tower.
-/

noncomputable section

universe u v

open Classical

namespace MyProjects
namespace ST

variable {Ω : Type u} {F : DiscreteFiltration Ω}

/- Auxiliary facts about stopping times expressed through their values. -/
namespace StoppingTime

/-- Pointwise order: `τ ≤ σ` when the value of `τ` is everywhere less than or
equal to the value of `σ`. -/
instance : LE (StoppingTime F) where
  le τ σ := ∀ ω, τ.value ω ≤ σ.value ω

@[simp]
lemma le_iff {τ σ : StoppingTime F} :
    τ ≤ σ ↔ ∀ ω, τ.value ω ≤ σ.value ω :=
  Iff.rfl

/-- The pointwise order turns stopping times into a preorder. -/
instance : Preorder (StoppingTime F) where
  le := (· ≤ ·)
  le_refl := by
    intro τ ω; exact le_rfl
  le_trans := by
    intro τ σ ρ hτσ hσρ ω
    exact (hτσ ω).trans (hσρ ω)

/-- Pointwise minimum of two stopping times (as a function). -/
def infValue (τ σ : StoppingTime F) : Ω → ℕ :=
  fun ω => min (τ.value ω) (σ.value ω)

/-- Pointwise maximum of two stopping times (as a function). -/
def supValue (τ σ : StoppingTime F) : Ω → ℕ :=
  fun ω => max (τ.value ω) (σ.value ω)

/-- Pointwise sum: “first apply `τ`, then wait for `σ` more steps”. -/
def addValue (τ σ : StoppingTime F) : Ω → ℕ :=
  fun ω => τ.value ω + σ.value ω

@[simp]
lemma infValue_le_left (τ σ : StoppingTime F) :
    ∀ ω, infValue τ σ ω ≤ τ.value ω := by
  intro ω; unfold infValue; exact Nat.min_le_left _ _

@[simp]
lemma infValue_le_right (τ σ : StoppingTime F) :
    ∀ ω, infValue τ σ ω ≤ σ.value ω := by
  intro ω; unfold infValue; exact Nat.min_le_right _ _

@[simp]
lemma le_supValue_left (τ σ : StoppingTime F) :
    ∀ ω, τ.value ω ≤ supValue τ σ ω := by
  intro ω; unfold supValue; exact Nat.le_max_left _ _

@[simp]
lemma le_supValue_right (τ σ : StoppingTime F) :
    ∀ ω, σ.value ω ≤ supValue τ σ ω := by
  intro ω; unfold supValue; exact Nat.le_max_right _ _

/-- The event that the pointwise minimum occurs no later than `n`. -/
def infAtMost (τ σ : StoppingTime F) (n : ℕ) : Set Ω :=
  {ω | infValue τ σ ω ≤ n}

/-- The event that the pointwise maximum occurs no later than `n`. -/
def supAtMost (τ σ : StoppingTime F) (n : ℕ) : Set Ω :=
  {ω | supValue τ σ ω ≤ n}

/-- The event describing the sum of two stopping times. -/
def addAtMost (τ σ : StoppingTime F) (n : ℕ) : Set Ω :=
  {ω | addValue τ σ ω ≤ n}

@[simp]
lemma mem_infAtMost {τ σ : StoppingTime F} {n : ℕ} {ω : Ω} :
    ω ∈ infAtMost τ σ n ↔
      ω ∈ τ.atMost n ∨ ω ∈ σ.atMost n := by
  classical
  unfold infAtMost StoppingTime.atMost infValue
  constructor
  · intro h
    have h' : min (τ.value ω) (σ.value ω) ≤ n := by
      simpa [Set.mem_setOf_eq] using h
    have h'' := (min_le_iff).1 h'
    cases h'' with
    | inl hτ =>
        left
        simpa [Set.mem_setOf_eq]
    | inr hσ =>
        right
        simpa [Set.mem_setOf_eq]
  · intro h
    cases h with
    | inl hτ =>
        have hτ' : τ.value ω ≤ n := by
          simpa [Set.mem_setOf_eq] using hτ
        have : min (τ.value ω) (σ.value ω) ≤ n :=
          (min_le_iff).2 (Or.inl hτ')
        simpa [Set.mem_setOf_eq]
    | inr hσ =>
        have hσ' : σ.value ω ≤ n := by
          simpa [Set.mem_setOf_eq] using hσ
        have : min (τ.value ω) (σ.value ω) ≤ n :=
          (min_le_iff).2 (Or.inr hσ')
        simpa [Set.mem_setOf_eq]

@[simp]
lemma mem_supAtMost {τ σ : StoppingTime F} {n : ℕ} {ω : Ω} :
    ω ∈ supAtMost τ σ n ↔
      ω ∈ τ.atMost n ∧ ω ∈ σ.atMost n := by
  classical
  unfold supAtMost StoppingTime.atMost supValue
  constructor
  · intro h
    have h' : max (τ.value ω) (σ.value ω) ≤ n := by
      simpa [Set.mem_setOf_eq] using h
    rcases (max_le_iff).1 h' with ⟨hτ, hσ⟩
    exact
      ⟨by simpa [Set.mem_setOf_eq] using hτ,
       by simpa [Set.mem_setOf_eq] using hσ⟩
  · intro h
    rcases h with ⟨hτ, hσ⟩
    have hτ' : τ.value ω ≤ n := by simpa [Set.mem_setOf_eq] using hτ
    have hσ' : σ.value ω ≤ n := by simpa [Set.mem_setOf_eq] using hσ
    exact (max_le_iff).2 ⟨hτ', hσ'⟩

@[simp]
lemma mem_addAtMost {τ σ : StoppingTime F} {n : ℕ} {ω : Ω} :
    ω ∈ addAtMost τ σ n ↔
      τ.value ω + σ.value ω ≤ n := Iff.rfl

/-- Bounded stopping times remain bounded after taking pointwise minima. -/
lemma infValue_bounded {τ σ : StoppingTime F} {N : ℕ}
    (hτ : τ.IsBounded N) (hσ : σ.IsBounded N) :
    ∀ ω, infValue τ σ ω ≤ N := by
  intro ω
  unfold infValue
  have hτω := hτ ω
  have hσω := hσ ω
  exact (min_le_iff).2 (Or.inl hτω)

/-- Bounded stopping times remain bounded after taking pointwise maxima. -/
lemma supValue_bounded {τ σ : StoppingTime F} {N : ℕ}
    (hτ : τ.IsBounded N) (hσ : σ.IsBounded N) :
    ∀ ω, supValue τ σ ω ≤ N := by
  intro ω
  unfold supValue
  exact (max_le_iff).2 ⟨hτ ω, hσ ω⟩

/-- Bounding the pointwise sum with two separate bounds. -/
lemma addValue_bounded {τ σ : StoppingTime F} {N M : ℕ}
    (hτ : τ.IsBounded N) (hσ : σ.IsBounded M) :
    ∀ ω, addValue τ σ ω ≤ N + M := by
  intro ω
  unfold addValue
  exact Nat.add_le_add (hτ ω) (hσ ω)

/-- The minimum with itself is just the original value. -/
@[simp] lemma infValue_self (τ : StoppingTime F) :
    infValue τ τ = τ.value := by
  funext ω; unfold infValue; simp

/-- The maximum with itself is the original value. -/
@[simp] lemma supValue_self (τ : StoppingTime F) :
    supValue τ τ = τ.value := by
  funext ω; unfold supValue; simp

end StoppingTime

end ST
end MyProjects
