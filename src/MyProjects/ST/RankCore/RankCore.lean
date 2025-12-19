import Mathlib
import MyProjects.ST.Rank.P3.RankTower

/-!
Ranked objects and their layers.

Key defs: `Ranked`, `Ranked.layer`, `Ranked.layer_mono`, `Ranked.toNatTowerWithMin`.
Example: `x ∈ (Ranked.toNatTowerWithMin R).layer (R.rank x)`.
-/

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

/-- RankTower版（添字=ℕ固定）の構造塔へ（Nat.find不要・computable寄り） -/
def toNatTowerWithMin (R : Ranked Nat X) : StructureTowerWithMin where
  carrier := X
  layer n := {x : X | R.rank x ≤ n}
  covering := by
    intro x
    refine ⟨R.rank x, ?_⟩
    simp
  monotone := by
    intro i j hij x hx
    exact le_trans hx hij
  minLayer := R.rank
  minLayer_mem := by
    intro x
    simp
  minLayer_minimal := by
    intro x i hx
    exact hx

example (R : Ranked Nat X) (x : X) :
    x ∈ (toNatTowerWithMin R).layer (R.rank x) := by
  exact (toNatTowerWithMin R).minLayer_mem x

end Ranked

end ST
