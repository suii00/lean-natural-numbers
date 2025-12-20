import Mathlib.CategoryTheory.Category.Basic
import MyProjects.ST.RankCore.RankHomLe

/-!
# RankCatLe (B2 skeleton)

This file packages the data-lane morphisms `ST.RankHomLe` into a category.

## WBS: B2
- Objects: `Σ X, ST.Ranked α X`
- Morphisms: `ST.RankHomLe` (with `indexMap : α → α`)
- Category laws: proved by `cases`/`ext` (no rank reasoning required)

## DoD
`#check (𝟙 T ≫ f = f)` etc. should typecheck.
-/

namespace ST

open CategoryTheory

universe u v

/-- Objects of the Rank data-lane category at index type `α`.

An object is a type `X : Type u` equipped with a rank function `X → α`. -/
abbrev RankCatLe.{u1, v1} (α : Type v1) : Type (max (u1 + 1) v1) :=
  Σ X : Type u1, Ranked α X

namespace RankCatLe

variable {α : Type v} [Preorder α]

/-- Projection: the underlying carrier type. -/
abbrev carrier (T : RankCatLe (α := α)) : Type u := T.1

/-- Projection: the ranked structure on the carrier. -/
abbrev ranked (T : RankCatLe (α := α)) : Ranked α (carrier T) := T.2

/-- Ext lemma for morphisms in the data lane (useful for rewriting). -/
@[ext]
lemma hom_ext {T U : RankCatLe (α := α)}
    {f g : RankHomLe (ranked T) (ranked U)}
    (hmap : f.map = g.map) (hind : f.indexMap = g.indexMap) : f = g := by
  -- `mono` and `rank_le` are Prop-fields, so it suffices to match the data fields.
  cases f
  cases g
  cases hmap
  cases hind
  rfl

/-- Category instance on `RankCatLe α` with `RankHomLe` morphisms. -/
instance : Category (RankCatLe (α := α)) where
  Hom T U := RankHomLe (ranked T) (ranked U)
  id T := RankHomLe.id (ranked T)
  -- comp f g = f ≫ g (first f, then g)
  comp f g := RankHomLe.comp f g
  id_comp := by
    intro T U f
    -- definitional equality after destructing `f`
    cases f
    rfl
  comp_id := by
    intro T U f
    cases f
    rfl
  assoc := by
    intro T U V W f g h
    cases f
    cases g
    cases h
    rfl

section DoD

variable {T U V : RankCatLe (α := α)}
variable (f : T ⟶ U) (g : U ⟶ V)

-- Basic sanity checks (should typecheck).
#check (𝟙 T ≫ f = f)
#check (f ≫ 𝟙 U = f)
#check ((f ≫ g) ≫ (𝟙 V) = f ≫ (g ≫ (𝟙 V)))

end DoD

end RankCatLe

end ST
