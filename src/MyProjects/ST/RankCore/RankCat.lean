import Mathlib
import MyProjects.ST.RankCore.Basic

namespace ST

universe u v w

open CategoryTheory

/-- Rank-hom (Exists lane): "each bounded layer goes to some bounded layer". -/
structure RankHomD {α : Type v} {β : Type w} {X : Type u} {Y : Type u}
    [Preorder α] [Preorder β]
    (R : Ranked α X) (S : Ranked β Y) where
  map : X → Y
  layer_map_exists :
    ∀ a : α, ∃ b : β, ∀ x : X, R.rank x ≤ a → S.rank (map x) ≤ b

/-- Rank-hom (Data lane): explicit monotone indexMap bounding ranks. -/
structure RankHomLe {α : Type v} {β : Type w} {X : Type u} {Y : Type u}
    [Preorder α] [Preorder β]
    (R : Ranked α X) (S : Ranked β Y) where
  map      : X → Y
  indexMap : α → β
  mono     : Monotone indexMap
  rank_le  : ∀ x : X, S.rank (map x) ≤ indexMap (R.rank x)

/-- Rank-hom (Eq lane): strict equality of rank along an indexMap. -/
structure RankHomEq {α : Type v} {β : Type w} {X : Type u} {Y : Type u}
    [Preorder α] [Preorder β]
    (R : Ranked α X) (S : Ranked β Y) where
  map      : X → Y
  indexMap : α → β
  mono     : Monotone indexMap
  rank_eq  : ∀ x : X, S.rank (map x) = indexMap (R.rank x)

namespace RankHomLe

variable {α : Type v} {β : Type w} {γ : Type*}
variable {X : Type u} {Y : Type u} {Z : Type u}
variable [Preorder α] [Preorder β] [Preorder γ]
variable (R : Ranked α X) (S : Ranked β Y) (T : Ranked γ Z)

def id : RankHomLe R R where
  map := _root_.id
  indexMap := _root_.id
  mono := by intro a b hab; exact hab
  rank_le := by intro x; exact le_rfl

def comp (f : RankHomLe R S) (g : RankHomLe S T) : RankHomLe R T where
  map := g.map ∘ f.map
  indexMap := g.indexMap ∘ f.indexMap
  mono := g.mono.comp f.mono
  rank_le := by
    intro x
    -- S.rank (f.map x) ≤ f.indexMap (R.rank x) then apply g.rank_le and monotonicity
    have h1 : S.rank (f.map x) ≤ f.indexMap (R.rank x) := f.rank_le x
    have h2 : T.rank (g.map (f.map x)) ≤ g.indexMap (S.rank (f.map x)) := g.rank_le (f.map x)
    exact le_trans h2 (g.mono h1)

@[ext]
lemma ext {R : Ranked α X} {S : Ranked β Y} {f g : RankHomLe R S}
    (hmap : f.map = g.map) (hindex : f.indexMap = g.indexMap) : f = g := by
  cases f; cases g; cases hmap; cases hindex; rfl

end RankHomLe

/-- Category of ranked objects with RankHomLe morphisms. -/
def RankCatLe (α : Type v) [Preorder α] : Type (max (u+1) v) :=
  Σ X : Type u, Ranked α X

namespace RankCatLe

variable {α : Type v} [Preorder α]

instance : CoeSort (RankCatLe α) (Type u) where
  coe T := T.1

def ranked (T : RankCatLe α) : Ranked α T := T.2

/-- Hom in RankCatLe. -/
abbrev Hom (T U : RankCatLe α) :=
  RankHomLe (ranked T) (ranked U)

instance : Category (RankCatLe α) where
  Hom T U := Hom T U
  id T := RankHomLe.id (ranked T)
  comp f g := RankHomLe.comp (R := ranked _) (S := ranked _) (T := ranked _) f g
  id_comp := by
    intro T U f
    apply RankHomLe.ext <;> rfl
  comp_id := by
    intro T U f
    apply RankHomLe.ext <;> rfl
  assoc := by
    intro A B C D f g h
    cases f; cases g; cases h; rfl

end RankCatLe

/-
  Forgetful / comparison functors (skeleton):

  RankHomEq → RankHomLe: use rank_eq ⇒ rank_le by rewriting and le_rfl
  RankHomLe → RankHomD : choose b := indexMap a
-/

namespace Bridges

open CategoryTheory

variable {α : Type v} {X : Type u} [Preorder α]

-- Example: RankHomLe → RankHomD
def leToD {Y : Type u} (R : Ranked α X) (S : Ranked α Y) :
    RankHomLe R S → RankHomD R S := fun f =>
  { map := f.map
    layer_map_exists := by
      intro a
      refine ⟨f.indexMap a, ?_⟩
      intro x hx
      have : S.rank (f.map x) ≤ f.indexMap (R.rank x) := f.rank_le x
      exact le_trans this (f.mono hx)
  }

end Bridges

end ST
