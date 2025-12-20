import Mathlib

/-!
# RankCore (T1 skeleton)

This file introduces the **Rank-first** core interface.

* A ranked object is just a type `X` equipped with a rank function `rank : X → α`.
* The induced layer at index `n : α` is `{x | rank x ≤ n}` when `[Preorder α]`.

Design intent (pivot): `Ranked` is the *source of truth*; towers are reconstructed from ranks.
-/

namespace ST

universe u v

/-- Minimal core: a ranked object is a carrier `X` with a rank function `X → α`. -/
structure Ranked (α : Type v) (X : Type u) where
  rank : X → α

namespace Ranked

variable {α : Type v} {X : Type u}

/-- The induced layer at `n` consists of elements of rank `≤ n`. -/
def layer [Preorder α] (R : Ranked α X) (n : α) : Set X :=
  {x | R.rank x ≤ n}

@[simp] theorem mem_layer_iff [Preorder α] (R : Ranked α X) (n : α) (x : X) :
    x ∈ R.layer n ↔ R.rank x ≤ n := Iff.rfl

/-- Layers are monotone in the index. -/
theorem layer_mono [Preorder α] (R : Ranked α X) {n m : α} (hnm : n ≤ m) :
    R.layer n ⊆ R.layer m := by
  intro x hx
  exact le_trans hx hnm

end Ranked

end ST
