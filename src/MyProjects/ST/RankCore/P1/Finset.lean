import MyProjects.ST.RankCore.P1.List

/-!
Finset rank examples.

Key defs: `finsetCore`, `card_image_le`, `bij_preserves_card`,
`mapHomLe`, `mapHomEq`, `forgetIndexMap`.
Example: `finsetCore` ranks by cardinality.
-/

-- RankCore/Finset.lean
namespace RankCore

def finsetCore {α : Type*} [DecidableEq α] : Core (Finset α) where
  rank := fun s => s.card

-- 全単射なら等号（Eqレーンへの道）
lemma bij_preserves_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Bijective f) (s : Finset α) :
    (s.image f).card = s.card := by
  exact Finset.card_image_of_injective s hf.1

-- 一般版：単射不要で ≤ が成り立つ
lemma card_image_le {α β : Type*} [DecidableEq β] (f : α → β) (s : Finset α) :
    (s.image f).card ≤ s.card := by
  simpa using (Finset.card_image_le (f := f) (s := s))

def mapHomLe {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β) :
    RankHomLe (finsetCore (α := α)) (finsetCore (α := β)) where
  map := fun s => s.image f
  indexMap := id
  indexMap_mono := by
    intro i j hij
    exact hij
  rank_le := by
    intro s
    simpa [finsetCore] using card_image_le (f := f) s

def mapHomEq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) :
    RankHomLe (finsetCore (α := α)) (finsetCore (α := β)) where
  map := fun s => s.image f
  indexMap := id
  indexMap_mono := by
    intro i j hij
    exact hij
  rank_le := by
    intro s
    exact le_of_eq (Finset.card_image_of_injective s hf)

-- ブリッジ：Le → D
def forgetIndexMap {α β : Type*} {T : Core α} {T' : Core β} (f : RankHomLe T T') :
    RankHomD T T' where
  map := f.map
  layer_map_exists := fun n => ⟨f.indexMap n, by
    simpa using f.layer_preserving n
  ⟩

example {α : Type*} [DecidableEq α] (s : Finset α) :
    s ∈ layer (finsetCore (α := α)) s.card := by
  simp [layer, finsetCore]

#eval finsetCore.rank ({1, 2, 3} : Finset Nat)  -- 3
#eval finsetCore.rank (∅ : Finset Nat)  -- 0

-- ボーナス：image による射の計算例
def natSuccFinset : Finset ℕ → Finset ℕ :=
  fun s => s.image Nat.succ

#eval natSuccFinset {0, 1, 2}  -- {1, 2, 3}
#eval finsetCore.rank (natSuccFinset {0, 1, 2})  -- 3

#eval (({0, 1, 2, 3} : Finset Nat).image (fun n => n % 2)).card  -- 2

end RankCore
