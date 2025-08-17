/-
  Power Set Theory
  Following Bourbaki's formalization
  Fixed version
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Lattice

namespace CantorTheorem

open Set

section PowerSet

variable {α : Type*}

/- Definition: Power Set -/
def PowerSet (A : Set α) : Set (Set α) := Set.powerset A

notation "𝒫(" A ")" => PowerSet A

/- Basic Properties of Power Set -/

theorem mem_powerset {A B : Set α} : B ∈ 𝒫(A) ↔ B ⊆ A :=
  Iff.rfl

theorem empty_mem_powerset (A : Set α) : ∅ ∈ 𝒫(A) :=
  Set.empty_subset A

theorem self_mem_powerset (A : Set α) : A ∈ 𝒫(A) :=
  Subset.rfl

theorem powerset_mono {A B : Set α} (h : A ⊆ B) : 𝒫(A) ⊆ 𝒫(B) :=
  fun _ hC => Subset.trans hC h

/- Cardinality Properties -/

theorem no_surjection_to_powerset (A : Set α) :
  ¬∃ f : α → Set α, Function.Surjective f ∧ (∀ a ∈ A, f a ∈ 𝒫(A)) :=
by
  intro ⟨f, hsurj, _⟩
  let D := {x ∈ A | x ∉ f x}
  have hD : D ∈ 𝒫(A) := by
    rw [mem_powerset]
    intro x hx
    simp at hx
    exact hx.1
  obtain ⟨a, ha⟩ := hsurj D
  by_cases h : a ∈ A
  · have : a ∈ D ↔ a ∉ f a := by
      simp [D]
      exact ⟨fun h => h.2, fun h' => ⟨h, h'⟩⟩
    rw [← ha] at this
    exact absurd (this.mpr) (not_not.mpr (this.mp))
  · sorry -- Handle case when a ∉ A

/- Union and Intersection with Power Set -/

theorem powerset_union (A B : Set α) :
  𝒫(A) ∪ 𝒫(B) ⊆ 𝒫(A ∪ B) :=
by
  intro X hX
  rw [mem_powerset]
  rw [mem_union] at hX
  cases hX with
  | inl hA => 
    rw [mem_powerset] at hA
    exact subset_union_of_subset_left hA B
  | inr hB =>
    rw [mem_powerset] at hB
    exact subset_union_of_subset_right hB A

theorem powerset_inter (A B : Set α) :
  𝒫(A ∩ B) = 𝒫(A) ∩ 𝒫(B) :=
by
  ext X
  simp only [mem_powerset, mem_inter_iff]
  constructor
  · intro h
    exact ⟨Subset.trans h (inter_subset_left),
           Subset.trans h (inter_subset_right)⟩
  · intro ⟨hA, hB⟩
    exact subset_inter hA hB

end PowerSet

end CantorTheorem