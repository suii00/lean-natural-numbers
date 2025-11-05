/-
Copyright (c) 2025
Authors: Structure Tower Project
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Nat
import MyProjects.ST.CAT2_complete
import MyProjects.ST.Probability
import MyProjects.ST.Probability_Extended

/-
# Level 2.1 Guide: Martingales through Structure Towers

This module refines the outline from `Probability.md` into Lean code that
follows the Bourbaki-style set-theoretic presentation.  We treat martingales,
submartingales, and supermartingales abstractly by relying only on the
structure-tower description of filtrations together with an abstract
conditional expectation operator.

Main components:
* `IsMartingale`, `IsSubmartingale`, `IsSupermartingale` — set-theoretic
  predicates that encode the usual tower property requirements.
* Structural lemmas showing how these predicates decompose into tower and
  adaptedness conditions.
* `martingaleDebutLayer` — the debut time of a process expressed via the
  minimal-layer operator of the associated structure tower.

These definitions are lightweight abstractions intended as stepping stones
towards fully measure-theoretic developments.
-/

noncomputable section

universe u v

open Classical

namespace MyProjects
namespace ST

variable {Ω : Type u}

/-- Real-valued random variables in the simplified setting. -/
abbrev RandomVariable (Ω : Type u) := Ω → ℝ

/-- Bourbaki-style martingale: adaptedness and tower invariance with respect to
an abstract conditional expectation operator. -/
structure IsMartingale
    (F : DiscreteFiltration Ω)
    (C : ConditionalExpectationStructure F)
    (X : ℕ → RandomVariable Ω) : Prop where
  /-- Adaptedness: upper level sets are visible at time `n`. -/
  adapted :
    ∀ n r, {ω : Ω | X n ω ≤ r} ∈ F.sigma n
  /-- Tower invariance: conditioning down to time `m` collapses the future. -/
  martingale_condition :
    ∀ {m n}, m ≤ n → C.cond m (X n) = X m

/-- Bourbaki-style submartingale: adaptedness together with the usual
inequality between a value and its conditioned future. -/
structure IsSubmartingale
    (F : DiscreteFiltration Ω)
    (C : ConditionalExpectationStructure F)
    (X : ℕ → RandomVariable Ω) : Prop where
  adapted :
    ∀ n r, {ω : Ω | X n ω ≤ r} ∈ F.sigma n
  submartingale_condition :
    ∀ {m n}, m ≤ n → ∀ ω, X m ω ≤ C.cond m (X n) ω

/-- Bourbaki-style supermartingale: adaptedness together with the usual
inequality swapped. -/
structure IsSupermartingale
    (F : DiscreteFiltration Ω)
    (C : ConditionalExpectationStructure F)
    (X : ℕ → RandomVariable Ω) : Prop where
  adapted :
    ∀ n r, {ω : Ω | X n ω ≤ r} ∈ F.sigma n
  supermartingale_condition :
    ∀ {m n}, m ≤ n → ∀ ω, C.cond m (X n) ω ≤ X m ω

namespace IsMartingale

variable {F : DiscreteFiltration Ω}
variable {C : ConditionalExpectationStructure F}
variable {X : ℕ → RandomVariable Ω}

lemma adapted_event (h : IsMartingale F C X) (n : ℕ) (r : ℝ) :
    {ω : Ω | X n ω ≤ r} ∈ F.sigma n :=
  h.adapted n r

lemma martingale_property (h : IsMartingale F C X) {m n : ℕ} (hmn : m ≤ n) :
    C.cond m (X n) = X m :=
  h.martingale_condition hmn

end IsMartingale

namespace IsSubmartingale

variable {F : DiscreteFiltration Ω}
variable {C : ConditionalExpectationStructure F}
variable {X : ℕ → RandomVariable Ω}

lemma adapted_event (h : IsSubmartingale F C X) (n : ℕ) (r : ℝ) :
    {ω : Ω | X n ω ≤ r} ∈ F.sigma n :=
  h.adapted n r

lemma inequality (h : IsSubmartingale F C X) {m n : ℕ} (hmn : m ≤ n) (ω : Ω) :
    X m ω ≤ C.cond m (X n) ω :=
  h.submartingale_condition hmn ω

end IsSubmartingale

namespace IsSupermartingale

variable {F : DiscreteFiltration Ω}
variable {C : ConditionalExpectationStructure F}
variable {X : ℕ → RandomVariable Ω}

lemma adapted_event (h : IsSupermartingale F C X) (n : ℕ) (r : ℝ) :
    {ω : Ω | X n ω ≤ r} ∈ F.sigma n :=
  h.adapted n r

lemma inequality (h : IsSupermartingale F C X) {m n : ℕ} (hmn : m ≤ n) (ω : Ω) :
    C.cond m (X n) ω ≤ X m ω :=
  h.supermartingale_condition hmn ω

end IsSupermartingale

section StructuralLemmas

variable (F : DiscreteFiltration Ω)
variable (C : ConditionalExpectationStructure F)
variable (X : ℕ → RandomVariable Ω)

/-- A martingale splits exactly into tower invariance and adaptedness. -/
theorem martingale_tower_invariance :
    IsMartingale F C X ↔
      (∀ m n, m ≤ n → C.cond m (X n) = X m) ∧
      (∀ n r, {ω : Ω | X n ω ≤ r} ∈ F.sigma n) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro m n hmn
      exact h.martingale_property hmn
    · intro n r
      exact h.adapted_event n r
  · intro h
    rcases h with ⟨hmart, hadapt⟩
    exact
      ⟨(fun n r => hadapt n r),
        (fun {m n} hmn => hmart m n hmn)⟩

/-- Conditioning further down a martingale collapses information. -/
theorem tower_property_for_martingale
    (hX : IsMartingale F C X) :
    ∀ {k m n}, k ≤ m → m ≤ n →
      C.cond k (X n) = C.cond k (X m) := by
  intro k m n hkm hmn
  have hmart := hX.martingale_property hmn
  have htower := C.tower k m (X n) hkm
  calc
    C.cond k (X n)
        = C.cond k (C.cond m (X n)) := by
            exact htower.symm
    _ = C.cond k (X m) := by
            simp [hmart]

/-- Debut layer of a martingale-valued process expressed via the tower. -/
def martingaleDebutLayer (ω : Ω) : ℕ :=
  (F.toStructureTowerWithMin).minLayer
    {ω' : Ω | ∃ n, X n ω' = X 0 ω}

lemma martingaleDebutLayer_mem (ω : Ω) :
    {ω' : Ω | ∃ n, X n ω' = X 0 ω} ∈
      F.sigma (martingaleDebutLayer (F := F) (X := X) ω) := by
  classical
  change {ω' : Ω | ∃ n, X n ω' = X 0 ω} ∈
      F.sigma
        ((F.toStructureTowerWithMin).minLayer
          {ω' : Ω | ∃ n, X n ω' = X 0 ω})
  exact
    F.minLayer_mem {ω' : Ω | ∃ n, X n ω' = X 0 ω}

end StructuralLemmas

/-- Basic usage example: the martingale condition at level zero is immediate. -/
example
    (F : DiscreteFiltration Ω)
    (C : ConditionalExpectationStructure F)
    (X : ℕ → RandomVariable Ω)
    (hX : IsMartingale F C X) :
    C.cond 0 (X 0) = X 0 :=
  hX.martingale_property le_rfl

end ST
end MyProjects
