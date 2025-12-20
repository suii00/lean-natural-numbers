import Mathlib
import MyProjects.ST.RankCore.Basic

/-!
# RankHomLe (T1 skeleton)

Data-lane morphisms between ranked objects.

A morphism from `R : Ranked α X` to `S : Ranked β Y` carries:

* `map : X → Y`
* `indexMap : α → β`
* `mono : Monotone indexMap`
* `rank_le : ∀ x, S.rank (map x) ≤ indexMap (R.rank x)`

This is the recommended "source of truth" lane for the Rank pivot.

Only the minimal operations needed for T1 are included:

* identity morphism
* composition
-/

namespace ST

universe u v w

open scoped Classical

/-- Data-lane morphisms between ranked objects. -/
structure RankHomLe {α : Type v} {β : Type w} {X : Type u} {Y : Type u}
    [Preorder α] [Preorder β]
    (R : Ranked α X) (S : Ranked β Y) where
  map      : X → Y
  indexMap : α → β
  mono     : Monotone indexMap
  rank_le  : ∀ x : X, S.rank (map x) ≤ indexMap (R.rank x)

namespace RankHomLe

variable {α : Type v} {β : Type w} {γ : Type*}
variable {X : Type u} {Y : Type u} {Z : Type u}
variable [Preorder α] [Preorder β] [Preorder γ]

/-- Identity morphism in the data lane. -/
def id (R : Ranked α X) : RankHomLe R R where
  map := _root_.id
  indexMap := _root_.id
  mono := by
    intro a b hab
    exact hab
  rank_le := by
    intro x
    -- `R.rank (id x) ≤ id (R.rank x)`
    exact le_rfl

/-- Composition of data-lane morphisms. -/
def comp {R : Ranked α X} {S : Ranked β Y} {T : Ranked γ Z}
    (f : RankHomLe R S) (g : RankHomLe S T) : RankHomLe R T where
  map := g.map ∘ f.map
  indexMap := g.indexMap ∘ f.indexMap
  mono := g.mono.comp f.mono
  rank_le := by
    intro x
    have hf : S.rank (f.map x) ≤ f.indexMap (R.rank x) := f.rank_le x
    have hg : T.rank (g.map (f.map x)) ≤ g.indexMap (S.rank (f.map x)) := g.rank_le (f.map x)
    -- Push `hf` through monotonicity of `g.indexMap` and chain.
    exact le_trans hg (g.mono hf)

end RankHomLe

end ST
