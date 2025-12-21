import MyProjects.ST.CAT2_complete
import MyProjects.ST.RankCore.Basic
import MyProjects.ST.RankCore.RankHomLe
import MyProjects.ST.RankCore.RankBridge_EqLeD

/-!
# B4 Bridge: from the old `Cat_*` families to the Rank lane (non-destructive)

Goal (WBS B4):
- Do **not** replace the old files.
- Provide an *explainable connection* showing that the new Rank lane is the canonical one.
- Keep this bridge lightweight: avoid committing to global refactors of the old `Cat_*` modules.

This file focuses on the two most important connections:

1. `Cat_WithMin` / `homeq`  →  Rank `Eq` lane (`RankHomEq`)
   Objects: `StructureTowerWithMin`  ↦  `Ranked Index carrier` via `rank := minLayer`.

2. (Optional adapter) old `Cat_le`-style morphisms (layer-preserving + monotone `indexMap`)
   on *WithMin objects*  →  Rank `Le` lane (`RankHomLe`).
   This explains why `Le` is canonical on the Rank side.

Notes:
- The bridge is intentionally **object-wise**. The old tower categories have varying index types,
  while `RankCatLe α` is fixed-index. Category-level functors can be added later if needed.
- Naming is conservative. Adjust namespaces / import paths to match your repository layout.
-/

namespace ST

universe u v

open Ranked

/-- Old objects (WithMin lane). -/
abbrev TowerWithMin := _root_.StructureTowerWithMin

/-- Old morphisms in the WithMin lane (`homeq`). -/
abbrev homeq (T T' : TowerWithMin) : Type _ :=
  _root_.StructureTowerWithMin.Hom (T := T) (T' := T')

namespace Rank

namespace Bridge

/-! ## 1) Objects: `StructureTowerWithMin` → `Ranked` -/

/-- View a `StructureTowerWithMin` as a ranked object by taking `rank := minLayer`. -/
def rankedOfWithMin (T : TowerWithMin.{u, v}) : Ranked T.Index T.carrier where
  rank := T.minLayer

@[simp] lemma rankedOfWithMin_rank (T : TowerWithMin.{u, v}) (x : T.carrier) :
    (rankedOfWithMin T).rank x = T.minLayer x := rfl

/-- The tower-layer equals the rank-induced layer. -/
theorem layer_eq_rankLayer (T : TowerWithMin.{u, v}) (i : T.Index) :
    T.layer i = (rankedOfWithMin T).layer i := by
  ext x
  constructor
  · intro hx
    -- x ∈ layer i ⇒ minLayer x ≤ i
    exact T.minLayer_minimal x i hx
  · intro hx
    -- minLayer x ≤ i ⇒ x ∈ layer (minLayer x) ⊆ layer i
    have hx0 : x ∈ T.layer (T.minLayer x) := T.minLayer_mem x
    exact (T.monotone hx) hx0

/-! ## 2) Morphisms: `homeq` → Rank `Eq` lane -/

namespace WithMin

variable {T T' : TowerWithMin.{u, v}}

/-- Convert an old `homeq` morphism into a Rank `Eq`-lane morphism. -/
def toRankHomEq (f : homeq T T') :
    RankHomEq (R := rankedOfWithMin T) (S := rankedOfWithMin T') where
  map := f.map
  indexMap := f.indexMap
  mono := by
    intro i j hij
    exact f.indexMap_mono hij
  rank_eq := by
    intro x
    -- minLayer preservation is exactly rank preservation for `rank := minLayer`.
    simpa [rankedOfWithMin] using (f.minLayer_preserving x)

@[simp] lemma toRankHomEq_map (f : homeq T T') :
    (toRankHomEq (T := T) (T' := T') f).map = f.map := rfl

@[simp] lemma toRankHomEq_indexMap (f : homeq T T') :
    (toRankHomEq (T := T) (T' := T') f).indexMap = f.indexMap := rfl

/-- Via B3: `homeq` → Rank `Le` lane. -/
def toRankHomLe (f : homeq T T') :
    RankHomLe (rankedOfWithMin T) (rankedOfWithMin T') :=
  (toRankHomEq (T := T) (T' := T') f).toLe

/-- Via B3: `homeq` → Rank `D` lane. -/
def toRankHomD (f : homeq T T') :
    RankHomD (rankedOfWithMin T) (rankedOfWithMin T') :=
  (toRankHomEq (T := T) (T' := T') f).toD

end WithMin

/-! ## 3) Optional adapter: old `Cat_le`-style morphisms on WithMin objects → Rank `Le`

The old `Cat_le` notion (minLayer-free) typically defines morphisms by:
- a carrier map `map`
- a monotone index map `indexMap`
- layer preservation: `x ∈ layer i → map x ∈ layer (indexMap i)`

Even without a `minLayer_preserving` axiom, if the *objects* have `minLayer`,
this implies the Rank `Le` inequality:
`minLayer (map x) ≤ indexMap (minLayer x)`.

We capture this as a small interface `OldHomLe`. If you already have an old type (e.g. `TowerD.HomLe`),
you can provide a constructor `OldHomLe.ofCatLe` and reuse `OldHomLe.toRankHomLe`.
-/

/-- Interface matching the old `Cat_le` morphism shape, specialized to WithMin objects. -/
structure OldHomLe (T T' : TowerWithMin.{u, v}) where
  map : T.carrier → T'.carrier
  indexMap : T.Index → T'.Index
  mono : Monotone indexMap
  layer_preserving : ∀ (i : T.Index) (x : T.carrier),
    x ∈ T.layer i → map x ∈ T'.layer (indexMap i)

namespace OldHomLe

variable {T T' : TowerWithMin.{u, v}}

/-- The key bridge: old `Cat_le`-style morphism ⇒ Rank `Le` lane (on `rank := minLayer`). -/
def toRankHomLe (f : OldHomLe T T') :
    RankHomLe (rankedOfWithMin T) (rankedOfWithMin T') where
  map := f.map
  indexMap := f.indexMap
  mono := f.mono
  rank_le := by
    intro x
    -- x ∈ layer (minLayer x)
    have hx : x ∈ T.layer (T.minLayer x) := T.minLayer_mem x
    -- map x ∈ layer (indexMap (minLayer x))
    have hy : f.map x ∈ T'.layer (f.indexMap (T.minLayer x)) :=
      f.layer_preserving (T.minLayer x) x hx
    -- minimality in target gives the inequality
    exact T'.minLayer_minimal (f.map x) (f.indexMap (T.minLayer x)) hy

end OldHomLe

end Bridge

end Rank

end ST
