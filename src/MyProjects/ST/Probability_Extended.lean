import Mathlib.Data.Nat.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.Order.Nat
import MyProjects.ST.CAT2_complete
import MyProjects.ST.Probability

/-
# Probability Towers — Extended Level 1 Library

This file elaborates on `Probability.md` in the Bourbaki spirit.
We organise filtrations, stopping times, adapted processes, and tower
constructions purely set-theoretically on top of `StructureTowerWithMin`.
The focus is on clear correspondences between probabilistic notions and
structure tower primitives.
-/

noncomputable section

open Classical

universe u v w

namespace MyProjects
namespace ST

/-! ## 1. Filtrations as structure towers -/

section FiltrationTowers

variable {Ω : Type u}

@[simp]
lemma filtrationTower_layer_iff
    (F : DiscreteFiltration Ω) {n : ℕ} {E : Set Ω} :
    E ∈ (F.toStructureTowerWithMin).layer n ↔ E ∈ F.sigma n :=
  F.mem_layer_iff

lemma filtrationTower_minLayer_le
    (F : DiscreteFiltration Ω) {E : Set Ω} {n : ℕ}
    (hE : E ∈ F.sigma n) :
    (F.toStructureTowerWithMin).minLayer E ≤ n :=
  F.minLayer_le hE

lemma filtrationTower_covering
    (F : DiscreteFiltration Ω) (E : Set Ω) :
    ∃ n : ℕ, E ∈ (F.toStructureTowerWithMin).layer n := by
  obtain ⟨n, hn⟩ := F.covering E
  exact ⟨n, (filtrationTower_layer_iff F).2 hn⟩

end FiltrationTowers

/-! ## 2. Stopping times and debut towers -/

namespace StoppingTime

variable {Ω : Type u} {F : DiscreteFiltration Ω}

/-- The structure tower whose layers record that the stopping time
has been reached by a given step. -/
def toTower (τ : StoppingTime F) : StructureTowerWithMin where
  carrier := Ω
  Index := ℕ
  indexPreorder := inferInstance
  layer := fun n : ℕ => {ω : Ω | τ.value ω ≤ n}
  covering := by
    intro ω
    refine ⟨τ.value ω, ?_⟩
    simp
  monotone := by
    intro i j hij ω hω
    exact le_trans hω hij
  minLayer := τ.value
  minLayer_mem := by
    intro ω
    simp
  minLayer_minimal := by
    intro ω i hi
    exact hi

@[simp]
lemma layer_apply
    (τ : StoppingTime F) (n : ℕ) :
    (τ.toTower).layer n = {ω : Ω | τ.value ω ≤ n} := rfl

@[simp]
lemma mem_layer_iff
    (τ : StoppingTime F) {n : ℕ} {ω : Ω} :
    ω ∈ (τ.toTower).layer n ↔ τ.value ω ≤ n := Iff.rfl

@[simp]
lemma minLayer_eq_value
    (τ : StoppingTime F) (ω : Ω) :
    (τ.toTower).minLayer ω = τ.value ω :=
  rfl

@[simp]
lemma atMost_eq_layer
    (τ : StoppingTime F) (n : ℕ) :
    τ.atMost n = (τ.toTower).layer n :=
  rfl

lemma atMost_monotone
    (τ : StoppingTime F) :
    Monotone τ.atMost := by
  intro i j hij ω hi
  exact le_trans hi hij

@[simp]
lemma self_mem_atMost
    (τ : StoppingTime F) (ω : Ω) :
    ω ∈ τ.atMost (τ.value ω) := by
  simp [StoppingTime.atMost]

end StoppingTime

/-! ## 3. Adapted stochastic processes -/

section StochasticProcesses

variable {Ω : Type u}

/-- A discrete-time process adapted to a filtration in the discrete,
set-theoretic sense: fibre events live in the appropriate sigma layer. -/
structure StochasticProcess
    (F : DiscreteFiltration Ω) (β : Type v) [DecidableEq β] where
  /-- Value of the process at time `n`. -/
  value : ℕ → Ω → β
  /-- Adaptedness: each fibre `{ω | Xₙ ω = b}` is visible at time `n`. -/
  adapted :
    ∀ n b, {ω : Ω | value n ω = b} ∈ F.sigma n

namespace StochasticProcess

variable {F : DiscreteFiltration Ω} {β : Type v} [DecidableEq β]

def fibre (X : StochasticProcess F β) (n : ℕ) (b : β) :
    Set Ω := {ω | X.value n ω = b}

@[simp]
lemma mem_fibre (X : StochasticProcess F β) (n : ℕ) (b : β) (ω : Ω) :
    ω ∈ X.fibre n b ↔ X.value n ω = b := Iff.rfl

lemma fibre_mem_sigma
    (X : StochasticProcess F β) (n : ℕ) (b : β) :
    X.fibre n b ∈ F.sigma n :=
  X.adapted n b

def const
    (Ω : Type u) (c : β) :
    StochasticProcess (DiscreteFiltration.trivial Ω) β where
  value _ _ := c
  adapted := by
    intro n b
    classical
    by_cases h : c = b
    · have : {ω : Ω | c = b} = (Set.univ : Set Ω) := by
        ext ω
        simp [h]
      simp [this, DiscreteFiltration.trivial_sigma]
    · have : {ω : Ω | c = b} = (∅ : Set Ω) := by
        ext ω
        simp [h]
      simp [this, DiscreteFiltration.trivial_sigma]

@[simp]
lemma const_value
    (Ω : Type u) (c : β) (n : ℕ) (ω : Ω) :
    (const (Ω := Ω) c).value n ω = c :=
  rfl

example
    (Ω : Type u) (c : β) :
    {ω : Ω | (const (Ω := Ω) (β := β) c).value 0 ω = c} ∈
        (DiscreteFiltration.trivial Ω).sigma 0 := by
  classical
  simp [const, DiscreteFiltration.trivial_sigma]

end StochasticProcess

end StochasticProcesses

/-! ## 4. Tower property axiomatisation -/

section ConditionalExpectation

variable {Ω : Type u}

/-- A Bourbaki-style axiomatisation of conditional expectations indexed by time. -/
structure ConditionalExpectationStructure
    (F : DiscreteFiltration Ω) where
  /-- Conditional expectation operator `E[· | ℱₙ]`. -/
  cond : ℕ → (Ω → ℝ) → Ω → ℝ
  /-- Tower property: iterated conditioning collapses. -/
  tower :
    ∀ m n (X : Ω → ℝ), m ≤ n →
      cond m (cond n X) = cond m X

namespace ConditionalExpectationStructure

variable {F : DiscreteFiltration Ω}

@[simp]
lemma tower_eval
    (C : ConditionalExpectationStructure F)
    {m n : ℕ} {X : Ω → ℝ} (hmn : m ≤ n) (ω : Ω) :
    C.cond m (C.cond n X) ω = C.cond m X ω := by
  have := C.tower m n X hmn
  exact congrArg (fun f => f ω) this

lemma tower_idempotent
    (C : ConditionalExpectationStructure F)
    {n : ℕ} {X : Ω → ℝ} :
    C.cond n (C.cond n X) = C.cond n X := by
  simpa using C.tower n n X le_rfl

end ConditionalExpectationStructure

end ConditionalExpectation

/-! ## 5. Products of filtration towers -/

section Products

variable {Ω : Type u}

def filtrationTowerProd
    (F₁ F₂ : DiscreteFiltration Ω) :
    StructureTowerWithMin :=
  StructureTowerWithMin.prod
    F₁.toStructureTowerWithMin
    F₂.toStructureTowerWithMin

def filtrationTowerProj₁
    (F₁ F₂ : DiscreteFiltration Ω) :
    filtrationTowerProd F₁ F₂ ⟶ F₁.toStructureTowerWithMin :=
  StructureTowerWithMin.proj₁
    F₁.toStructureTowerWithMin
    F₂.toStructureTowerWithMin

def filtrationTowerProj₂
    (F₁ F₂ : DiscreteFiltration Ω) :
    filtrationTowerProd F₁ F₂ ⟶ F₂.toStructureTowerWithMin :=
  StructureTowerWithMin.proj₂
    F₁.toStructureTowerWithMin
    F₂.toStructureTowerWithMin

end Products

end ST
end MyProjects
