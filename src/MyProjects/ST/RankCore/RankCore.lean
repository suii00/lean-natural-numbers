import Mathlib

namespace ST

universe u v

/-- Minimal core: a ranked object is just a type with a rank function. -/
structure Ranked (α : Type v) (X : Type u) where
  rank : X → α

namespace Ranked

variable {α : Type v} {X : Type u}

/-- Standard "layer" induced by rank: elements of rank ≤ n. -/
def layer [Preorder α] (R : Ranked α X) (n : α) : Set X :=
  {x | R.rank x ≤ n}

@[simp] theorem mem_layer_iff [Preorder α] (R : Ranked α X) (n : α) (x : X) :
    x ∈ R.layer n ↔ R.rank x ≤ n := Iff.rfl

/-- Monotonicity of layers: n ≤ m ⇒ layer n ⊆ layer m. -/
theorem layer_mono [Preorder α] (R : Ranked α X) {n m : α} (hnm : n ≤ m) :
    R.layer n ⊆ R.layer m := by
  intro x hx
  exact le_trans hx hnm

/-
  Bridge to your existing `StructureTowerWithMin` (placeholder).

  The intended construction is:

  carrier := X
  Index   := α
  layer n := {x | rank x ≤ n}
  minLayer := rank
-/
-- def toTowerWithMin (R : Ranked α X) : StructureTowerWithMin := by
--   -- TODO: adapt to your actual record fields
--   sorry

end Ranked

end ST
