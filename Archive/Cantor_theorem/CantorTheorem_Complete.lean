/-
  Cantor's Theorem - Complete Proof
  Following Bourbaki's axiomatic approach with ZFC
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Basic

namespace CantorTheorem

open Set Function

section MainTheorem

variable {α : Type*}

/- 
  Cantor's Theorem: 
  For any set A, there is no surjection from A to its power set 𝒫(A)
  
  Proof by diagonal argument
-/
theorem cantor_theorem (f : α → Set α) : 
  ¬Surjective f :=
by
  -- Define the diagonal set D = {x : α | x ∉ f(x)}
  let D := {x : α | x ∉ f x}
  
  -- Assume f is surjective (for contradiction)
  intro hsurj
  
  -- Since f is surjective, there exists a : α such that f(a) = D
  obtain ⟨a, ha⟩ := hsurj D
  
  -- Now we derive a contradiction: a ∈ D ↔ a ∉ D
  have : a ∈ D ↔ a ∉ f a := by simp [D]
  
  -- Substitute f(a) = D
  rw [ha] at this
  
  -- We have: a ∈ D ↔ a ∉ D, which is a contradiction
  exact absurd (this.mp) (not_not.mpr this.mpr)

/- 
  Alternative formulation: No bijection from A to 𝒫(A)
-/
theorem cantor_no_bijection (A : Set α) :
  ¬∃ f : A → Set A, Bijective f :=
by
  intro ⟨f, hbij⟩
  -- Extract surjectivity from bijectivity
  have hsurj := hbij.2
  -- Apply Cantor's theorem
  exact cantor_theorem f hsurj

/- 
  Corollary: 𝒫(A) has strictly larger cardinality than A
  (There exists an injection from A to 𝒫(A) but no surjection)
-/
theorem cantor_strict_inequality (A : Set α) :
  (∃ f : A → Set A, Injective f) ∧ (¬∃ g : A → Set A, Surjective g) :=
by
  constructor
  · -- The singleton map is injective
    use fun a => {a.val}
    intro a₁ a₂ h
    simp at h
    ext
    exact h
  · -- No surjection exists by Cantor's theorem
    intro ⟨g, hsurj⟩
    exact cantor_theorem g hsurj

/- 
  Russell's Paradox Prevention:
  There is no universal set containing all sets
-/
theorem no_universal_set : 
  ¬∃ (U : Set (Set α)), ∀ (S : Set α), S ∈ U :=
by
  intro ⟨U, hU⟩
  -- Form the Russell set R = {x ∈ U | x ∉ x}
  let R := {S ∈ U | S ∉ S}
  -- R is a set, so R ∈ U
  have hR : R ∈ U := hU R
  -- Derive contradiction: R ∈ R ↔ R ∉ R
  have : R ∈ R ↔ R ∉ R := by
    simp [R]
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨hR, h⟩
  -- This is impossible
  exact absurd (this.mp) (not_not.mpr this.mpr)

end MainTheorem

section ZFCContext

/- 
  ZFC Axioms (selected relevant ones)
-/

variable {α : Type*}

-- Axiom of Extensionality
theorem extensionality {A B : Set α} : 
  (∀ x, x ∈ A ↔ x ∈ B) → A = B :=
  Set.ext

-- Axiom of Power Set
theorem power_set_exists (A : Set α) : 
  ∃ (P : Set (Set α)), ∀ B, B ∈ P ↔ B ⊆ A :=
  ⟨powerset A, fun _ => Iff.rfl⟩

-- Axiom of Specification
theorem specification (A : Set α) (P : α → Prop) : 
  ∃ (B : Set α), ∀ x, x ∈ B ↔ (x ∈ A ∧ P x) :=
  ⟨{x ∈ A | P x}, fun _ => by simp⟩

end ZFCContext

end CantorTheorem