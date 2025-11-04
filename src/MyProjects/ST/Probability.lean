import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Nat
import MyProjects.ST.CAT2_complete

/-!
# Probability Towers

This file formalises the discrete filtration viewpoint from `Probability.md`
inside the `StructureTowerWithMin` framework.  We work abstractly in the spirit
of Nicolas Bourbaki: filtrations are handled as increasing families of event
sets, stopping times are order-compatible time indices, and adapted processes
are phrased through tower morphisms.
-/

noncomputable section

universe u v

open Classical

namespace MyProjects
namespace ST

/-- A discrete filtration on a type `Ω` is an increasing family of collections
of events.  We only require the Bourbaki-style axioms: monotonicity and the
assumption that every event appears in some layer. -/
structure DiscreteFiltration (Ω : Type u) where
  /-- The σ-algebra-like layer at discrete time `n`. -/
  sigma : ℕ → Set (Set Ω)
  /-- Monotonicity: information only increases with time. -/
  mono : Monotone sigma
  /-- Covering: every event is eventually measurable. -/
  covering : ∀ E : Set Ω, ∃ n : ℕ, E ∈ sigma n

namespace DiscreteFiltration

variable {Ω : Type u} (F : DiscreteFiltration Ω)

/-- Auxiliary lemma: membership in the filtration is monotone in the time index. -/
lemma mem_of_le {m n : ℕ} (hmn : m ≤ n) {E : Set Ω} (hE : E ∈ F.sigma m) :
    E ∈ F.sigma n :=
  F.mono hmn hE

/-- The filtration associated with `F` viewed as a `StructureTowerWithMin`. -/
def toStructureTowerWithMin : StructureTowerWithMin where
  carrier := Set Ω
  Index := ℕ
  indexPreorder := inferInstance
  layer n := {E : Set Ω | E ∈ F.sigma n}
  covering := by
    intro E
    obtain ⟨n, hn⟩ := F.covering E
    exact ⟨n, hn⟩
  monotone := by
    intro i j hij E hE
    exact F.mem_of_le hij hE
  minLayer := fun E =>
    @Nat.find (fun n : ℕ => E ∈ F.sigma n) (Classical.decPred _) (F.covering E)
  minLayer_mem := by
    intro E
    classical
    simpa using
      @Nat.find_spec (fun n : ℕ => E ∈ F.sigma n) (Classical.decPred _) (F.covering E)
  minLayer_minimal := by
    intro E i hi
    classical
    exact
      @Nat.find_min' (fun n : ℕ => E ∈ F.sigma n) (Classical.decPred _) (F.covering E) i hi

@[simp]
lemma mem_layer_iff {n : ℕ} {E : Set Ω} :
    E ∈ (F.toStructureTowerWithMin).layer n ↔ E ∈ F.sigma n :=
  Iff.rfl

@[simp]
lemma minLayer_mem (E : Set Ω) :
    E ∈ F.sigma ((F.toStructureTowerWithMin).minLayer E) := by
  classical
  change E ∈ F.sigma
      (@Nat.find (fun n : ℕ => E ∈ F.sigma n) (Classical.decPred _) (F.covering E))
  simpa using
    @Nat.find_spec (fun n : ℕ => E ∈ F.sigma n) (Classical.decPred _) (F.covering E)

lemma minLayer_le {E : Set Ω} {n : ℕ} (h : E ∈ F.sigma n) :
    (F.toStructureTowerWithMin).minLayer E ≤ n := by
  classical
  change
      @Nat.find (fun m : ℕ => E ∈ F.sigma m) (Classical.decPred _) (F.covering E) ≤ n
  simpa using
    @Nat.find_min' (fun m : ℕ => E ∈ F.sigma m) (Classical.decPred _) (F.covering E) n h

/-- The trivial filtration in which every event is visible from time zero. -/
def trivial (Ω : Type u) : DiscreteFiltration Ω where
  sigma _ := Set.univ
  mono := by
    intro m n _ E _
    trivial
  covering := by
    intro E
    exact ⟨0, by trivial⟩

@[simp]
lemma trivial_sigma (Ω : Type u) (n : ℕ) :
    (trivial Ω).sigma n = Set.univ := rfl

end DiscreteFiltration

variable {Ω : Type u}

/-- Stopping times are order-valued maps whose debut events live in the filtration. -/
structure StoppingTime (F : DiscreteFiltration Ω) where
  /-- The stopping index for each outcome. -/
  value : Ω → ℕ
  /-- Debut measurability: `{ω | τ ω ≤ n}` appears in the layer at time `n`. -/
  adapted :
    ∀ n : ℕ, {ω : Ω | value ω ≤ n} ∈ F.sigma n

namespace StoppingTime

variable {F : DiscreteFiltration Ω} (τ : StoppingTime F)

/-- The event that the stopping time has occurred by `n`. -/
def atMost (n : ℕ) : Set Ω := {ω | τ.value ω ≤ n}

@[simp]
lemma atMost_mem (n : ℕ) : τ.atMost n ∈ F.sigma n :=
  τ.adapted n

end StoppingTime

/-- A basic sanity check: under the trivial filtration every event belongs to layer `0`. -/
example (Ω : Type*) :
    (Set.univ : Set Ω) ∈
        ((DiscreteFiltration.trivial Ω).toStructureTowerWithMin).layer (0 : ℕ) := by
  simp [DiscreteFiltration.trivial, DiscreteFiltration.toStructureTowerWithMin]

end ST
end MyProjects
