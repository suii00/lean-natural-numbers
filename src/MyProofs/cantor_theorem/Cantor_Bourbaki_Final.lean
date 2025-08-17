/-
  ======================================================================
  CANTOR'S THEOREM - BOURBAKI STYLE FORMALIZATION
  ======================================================================
  
  Following Nicolas Bourbaki's "Théorie des Ensembles" 
  and Zermelo-Fraenkel Set Theory axioms
  
  Author: Formalized in Lean 4
  Date: 2025-08-16
  ======================================================================
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Basic

namespace CantorBourbaki

open Set Function

/-
  ======================================================================
  THÉORÈME DE CANTOR (Cantor's Theorem)
  ======================================================================
  
  Énoncé (Statement):
  Pour tout ensemble X, il n'existe pas de surjection de X vers P(X).
  (For any set X, there is no surjection from X to its power set P(X).)
  
  Démonstration (Proof):
  Par l'argument diagonal (diagonalization argument).
  ======================================================================
-/

theorem theoreme_de_cantor {α : Type*} (f : α → Set α) : ¬Surjective f := by
  -- Étape 1: Construction de l'ensemble diagonal
  -- (Step 1: Construction of the diagonal set)
  -- D := {x ∈ α | x ∉ f(x)}
  let D : Set α := {x | x ∉ f x}
  
  -- Étape 2: Supposons que f est surjective
  -- (Step 2: Assume f is surjective)
  intro h_surj
  
  -- Étape 3: Par surjectivité, ∃ a ∈ α, f(a) = D
  -- (Step 3: By surjectivity, ∃ a ∈ α, f(a) = D)
  obtain ⟨a, ha⟩ := h_surj D
  
  -- Étape 4: Établir l'équivalence contradictoire
  -- (Step 4: Establish the contradictory equivalence)
  have h_contra : a ∈ D ↔ a ∉ f a := by
    simp only [D, mem_setOf]
  
  -- Étape 5: Substitution f(a) = D
  -- (Step 5: Substitution f(a) = D)
  rw [ha] at h_contra
  
  -- Étape 6: Contradiction finale: a ∈ D ↔ a ∉ D
  -- (Step 6: Final contradiction: a ∈ D ↔ a ∉ D)
  by_cases h : a ∈ D
  · exact h_contra.mp h h
  · exact h (h_contra.mpr h)

/-
  ======================================================================
  COROLLAIRES (Corollaries)
  ======================================================================
-/

/-- Corollaire 1: Il n'existe pas de bijection entre un ensemble et son ensemble des parties
    (Corollary 1: There is no bijection between a set and its power set) --/
theorem pas_de_bijection {α : Type*} : ¬∃ f : α → Set α, Bijective f := by
  intro ⟨f, hf_bij⟩
  exact theoreme_de_cantor f hf_bij.surjective

/-- Corollaire 2: Il existe une injection mais pas de surjection
    (Corollary 2: There exists an injection but no surjection) --/
theorem injection_sans_surjection {α : Type*} :
  (∃ f : α → Set α, Injective f) ∧ (¬∃ g : α → Set α, Surjective g) := by
  constructor
  -- L'application singleton est injective
  -- The singleton map is injective
  · use fun x => ({x} : Set α)
    intro x y h
    -- Si {x} = {y}, alors x = y
    simp only [Set.singleton_eq_singleton_iff] at h
    exact h
  -- Aucune surjection n'existe par le théorème de Cantor
  -- No surjection exists by Cantor's theorem
  · intro ⟨g, hg⟩
    exact theoreme_de_cantor g hg

/-
  ======================================================================
  CONTEXTE ZFC (ZFC Context)
  ======================================================================
-/

section AxiomesZFC

variable {α : Type*}

/-- Axiome d'extensionnalité (Axiom of Extensionality) --/
theorem axiome_extensionnalite {A B : Set α} :
  (∀ x, x ∈ A ↔ x ∈ B) → A = B :=
  Set.ext

/-- Axiome de l'ensemble des parties (Axiom of Power Set) --/
theorem axiome_ensemble_parties (A : Set α) :
  ∃ P : Set (Set α), ∀ B, B ∈ P ↔ B ⊆ A :=
  ⟨powerset A, fun _ => Iff.rfl⟩

/-- Axiome de spécification (Axiom of Specification) --/
theorem axiome_specification (A : Set α) (φ : α → Prop) :
  ∃ B : Set α, ∀ x, x ∈ B ↔ (x ∈ A ∧ φ x) :=
  ⟨{x ∈ A | φ x}, fun _ => by simp⟩

end AxiomesZFC

/-
  ======================================================================
  NOTE HISTORIQUE (Historical Note)
  ======================================================================
  
  Ce théorème a été démontré par Georg Cantor en 1891.
  La formalisation suit le style rigoureux de Nicolas Bourbaki,
  avec une attention particulière à la structure logique et
  l'utilisation explicite des axiomes de la théorie des ensembles.
  
  This theorem was proved by Georg Cantor in 1891.
  The formalization follows Nicolas Bourbaki's rigorous style,
  with particular attention to logical structure and
  explicit use of set theory axioms.
  ======================================================================
-/

end CantorBourbaki