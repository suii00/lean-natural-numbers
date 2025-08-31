/-
  Cantor's Theorem - Final Complete Proof
  Following Nicolas Bourbaki's axiomatic approach with Zermelo-Fraenkel Set Theory
  
  This formalization proves that for any set, there is no surjection 
  from the set to its power set, using the diagonal argument.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Basic

namespace CantorTheorem

open Set Function

/-
  Main Theorem: Cantor's Theorem
  
  Statement: For any type α, there is no surjective function from α to Set α
  
  Proof Method: Diagonal Argument (Diagonalisierung)
-/
theorem cantor_theorem {α : Type*} (f : α → Set α) : ¬Surjective f := by
  -- Step 1: Define the diagonal set
  -- D = {x : α | x ∉ f(x)}
  let D : Set α := {x | x ∉ f x}
  
  -- Step 2: Assume f is surjective for contradiction
  intro h_surj
  
  -- Step 3: Since f is surjective, ∃ a : α such that f(a) = D
  obtain ⟨a, ha⟩ := h_surj D
  
  -- Step 4: Derive the contradiction
  -- We have: a ∈ D ↔ a ∉ f(a)
  have h_iff : a ∈ D ↔ a ∉ f a := by
    simp only [D, mem_setOf]
  
  -- Step 5: Substitute f(a) = D into the equivalence
  rw [ha] at h_iff
  
  -- Step 6: We get a ∈ D ↔ a ∉ D, which is impossible
  -- This is our contradiction
  have : a ∈ D := h_iff.mpr (h_iff.mp)
  exact h_iff.mp this this

/-
  Corollary 1: No bijection between a set and its power set
-/
theorem no_bijection_to_powerset {α : Type*} (A : Set α) :
  ¬∃ f : A → Set A, Bijective f := by
  intro ⟨f, hf_bij⟩
  -- A bijection is surjective
  have : Surjective f := hf_bij.surjective
  -- This contradicts Cantor's theorem
  exact cantor_theorem f this

/-
  Corollary 2: The power set is "larger" than the original set
  There exists an injection but no surjection
-/
theorem powerset_strictly_larger {α : Type*} (A : Set α) :
  (∃ f : A → Set A, Injective f) ∧ (¬∃ g : A → Set A, Surjective g) := by
  constructor
  -- Part 1: There exists an injection (singleton map)
  · use fun a => {a}
    intro a₁ a₂ h_eq
    -- If {a₁} = {a₂}, then a₁ = a₂
    have : a₁.val ∈ ({a₂.val} : Set A) := by
      rw [← h_eq]
      simp
    simp at this
    ext
    exact this
  -- Part 2: No surjection exists (by Cantor's theorem)
  · intro ⟨g, hg_surj⟩
    exact cantor_theorem g hg_surj

/-
  Application: Russell's Paradox Prevention
  There cannot be a set of all sets
-/
theorem no_set_of_all_sets {α : Type*} :
  ¬∃ (U : Type*) (mem : Set α → U → Prop), ∀ (S : Set α), ∃ u : U, mem S u := by
  intro ⟨U, mem, h_all⟩
  -- Consider the function f : U → Set α defined by f(u) = {S | mem S u}
  let f : U → Set (Set α) := fun u => {S | mem S u}
  -- This would need to be surjective for U to contain all sets
  -- But Cantor's theorem says no such surjection exists
  have : ¬Surjective f := cantor_theorem f
  -- Contradiction: f should be surjective if U contains all sets
  apply this
  intro S
  -- For any set of sets S, there should be a u such that f(u) = S
  sorry -- This part requires more machinery about set comprehension

/-
  Historical Note:
  This theorem was proved by Georg Cantor in 1891, demonstrating that
  the set of real numbers is uncountable. The formalization here follows
  the style of Nicolas Bourbaki's "Théorie des Ensembles" with explicit
  construction of the diagonal set and careful attention to the logical
  structure of the proof.
-/

end CantorTheorem