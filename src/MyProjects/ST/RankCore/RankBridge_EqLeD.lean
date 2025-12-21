import MyProjects.ST.RankCore.RankHomLe

/-!
# B3 Bridge skeleton: Eq → Le → D (no Category instances yet)

WBS B3:
- `RankHomEq` (equality lane) → `RankHomLe` (≤-lane)
- `RankHomLe` → `RankHomD` (existence lane)

Dependencies:
- B1 (`RankHomLe` with `id/comp`)

DoD:
- Bridge functions are defined.
- Minimal simp-lemmas for the bridges typecheck.

Notes:
- Adjust the import path above if your repository uses a different module name.
- This file intentionally avoids `Category` instances; those belong to a later WBS item.
-/

namespace ST

universe u v w

/-- Equality lane morphism between ranked structures.

This is the “strongest” data lane: the rank is preserved by equality up to an `indexMap`. -/
structure RankHomEq {α : Type v} {β : Type w} {X : Type u} {Y : Type u}
    [Preorder α] [Preorder β] (R : Ranked α X) (S : Ranked β Y) where
  /-- underlying map on carriers -/
  map : X → Y
  /-- index map between rank values -/
  indexMap : α → β
  /-- monotonicity of the index map (kept so we can bridge into `RankHomLe`) -/
  mono : Monotone indexMap
  /-- rank is preserved by equality (lax commutativity as equality) -/
  rank_eq : ∀ x, S.rank (map x) = indexMap (R.rank x)

/-- Existence lane morphism between ranked structures.

This is the “weakest” lane: for each bound `n` in the source, there exists a bound `m` in the target
such that the image of `layer n` lands in `layer m`. -/
structure RankHomD {α : Type v} {β : Type w} {X : Type u} {Y : Type u}
    [Preorder α] [Preorder β] (R : Ranked α X) (S : Ranked β Y) where
  /-- underlying map on carriers -/
  map : X → Y
  /-- existence-style layer bound transport -/
  map_layer : ∀ n : α, ∃ m : β, ∀ x : X, R.rank x ≤ n → S.rank (map x) ≤ m

namespace RankHomEq

variable [Preorder α] [Preorder β]
variable {R : Ranked α X} {S : Ranked β Y}

/-- Bridge: equality lane → ≤-lane. -/
def toLe (f : RankHomEq (R := R) (S := S)) : RankHomLe R S where
  map := f.map
  indexMap := f.indexMap
  mono := f.mono
  rank_le := by
    intro x
    exact le_of_eq (f.rank_eq x)

@[simp] lemma toLe_map (f : RankHomEq (R := R) (S := S)) :
    (f.toLe).map = f.map := rfl

@[simp] lemma toLe_indexMap (f : RankHomEq (R := R) (S := S)) :
    (f.toLe).indexMap = f.indexMap := rfl

end RankHomEq

namespace RankHomLe

variable [Preorder α] [Preorder β]
variable {R : Ranked α X} {S : Ranked β Y}

/-- Bridge: ≤-lane → existence lane. -/
def toD (f : RankHomLe R S) : RankHomD R S where
  map := f.map
  map_layer := by
    intro n
    refine ⟨f.indexMap n, ?_⟩
    intro x hx
    -- S.rank (f.map x) ≤ f.indexMap (R.rank x) ≤ f.indexMap n
    exact le_trans (f.rank_le x) (f.mono hx)

/-- The chosen witness for `toD` is `indexMap n`. -/
lemma toD_bound (f : RankHomLe R S) (n : α) :
    ∀ x, R.rank x ≤ n → S.rank (f.map x) ≤ f.indexMap n := by
  intro x hx
  exact le_trans (f.rank_le x) (f.mono hx)

@[simp] lemma toD_map (f : RankHomLe R S) :
    (f.toD).map = f.map := rfl

end RankHomLe

namespace RankHomD

variable [Preorder α] [Preorder β]
variable {R : Ranked α X} {S : Ranked β Y}

@[simp] lemma map_layer_witness (f : RankHomD R S) (n : α) :
    ∃ m : β, ∀ x : X, R.rank x ≤ n → S.rank (f.map x) ≤ m :=
  f.map_layer n

/-- `map_layer` expressed as `Set.MapsTo` on layers. -/
lemma map_layer_layer (f : RankHomD R S) (n : α) :
    ∃ m : β, Set.MapsTo f.map (R.layer n) (S.layer m) := by
  rcases f.map_layer n with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  intro x hx
  have hx' : R.rank x ≤ n := (Ranked.mem_layer_iff (R := R) (n := n) (x := x)).1 hx
  have hx'' : S.rank (f.map x) ≤ m := hm x hx'
  exact (Ranked.mem_layer_iff (R := S) (n := m) (x := f.map x)).2 hx''

lemma mapsTo_layer (f : RankHomD R S) (n : α) :
    ∃ m : β, Set.MapsTo f.map (R.layer n) (S.layer m) :=
  map_layer_layer (f := f) n

end RankHomD

/-! ## Optional convenience: Eq → D via the two-step bridge -/
namespace RankHomEq

variable [Preorder α] [Preorder β]
variable {R : Ranked α X} {S : Ranked β Y}

/-- Bridge: equality lane → existence lane (via `toLe` then `toD`). -/
def toD (f : RankHomEq (R := R) (S := S)) : RankHomD R S :=
  (f.toLe).toD

@[simp] lemma toD_map (f : RankHomEq (R := R) (S := S)) :
    (f.toD).map = f.map := rfl

end RankHomEq

end ST
