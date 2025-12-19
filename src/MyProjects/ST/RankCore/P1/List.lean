import Mathlib

/-!
Core ranked structure for lists.

Key defs: `Core`, `RankHomLe`, `RankHomD`, `layer`, `listCore`, `mapHom`.
Example: `listCore.rank [1, 2, 3] = 3`.
-/

-- RankCore/List.lean
namespace RankCore

structure Core (α : Type*) where
  rank : α → ℕ

def layer {α : Type*} (C : Core α) (n : ℕ) : Set α :=
  {x | C.rank x ≤ n}

@[simp] lemma mem_layer_iff {α : Type*} (C : Core α) (n : ℕ) (x : α) :
    x ∈ layer C n ↔ C.rank x ≤ n := Iff.rfl

/-- Rank-non-increasing morphism between cores. -/
structure RankHomLe {α β : Type*} (C : Core α) (D : Core β) where
  map : α → β
  indexMap : ℕ → ℕ
  indexMap_mono : ∀ {i j : ℕ}, i ≤ j → indexMap i ≤ indexMap j
  rank_le : ∀ x, D.rank (map x) ≤ indexMap (C.rank x)

theorem RankHomLe.layer_preserving {α β : Type*} {C : Core α} {D : Core β}
    (f : RankHomLe C D) (n : ℕ) :
    Set.image f.map (layer C n) ⊆ layer D (f.indexMap n) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact le_trans (f.rank_le x) (f.indexMap_mono hx)

/-- Rank-structure with existential layer bounds. -/
structure RankHomD {α β : Type*} (C : Core α) (D : Core β) where
  map : α → β
  layer_map_exists : ∀ n : ℕ, ∃ m : ℕ, Set.image map (layer C n) ⊆ layer D m

def listCore {β : Type*} : Core (List β) where
  rank := List.length

example : ([1, 2, 3] : List Nat) ∈ layer (listCore (β := Nat)) 3 := by
  simp [layer, listCore]

-- 計算例（最重要）
#eval listCore.rank [1, 2, 3]  -- 3
#eval listCore.rank ([] : List Nat)  -- 0

-- HomLeの構成
def mapHom {β γ : Type*} (f : β → γ) :
    RankHomLe (listCore (β := β)) (listCore (β := γ)) where
  map := List.map f
  indexMap := id
  indexMap_mono := by
    intro i j hij
    exact hij
  rank_le := by
    intro xs
    simp [listCore, List.length_map]
