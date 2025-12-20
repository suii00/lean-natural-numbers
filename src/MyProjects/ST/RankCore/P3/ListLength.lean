import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Lattice
import MyProjects.ST.RankCore.Basic
import MyProjects.ST.RankCore.Bridge.ToTowerWithMin
import MyProjects.ST.RankCore.RankHomLe
import MyProjects.ST.RankCore.P3.FinsetCard

/-!
# ListLength - リストの長さによるRanked構造

## 概要
リストの長さ `List.length` を rank 関数とする Ranked 構造の例。
layer n は「長さが n 以下のすべてのリスト」を表す。

## 数学的意義
- rank : List α → ℕ は List.length
- layer n = {l : List α | l.length ≤ n}
- minLayer l = l.length（自然な最小構造選択）

## 典型的な使用例
- 空リスト [] の rank = 0
- 単一要素リスト [x] の rank = 1
- n 要素リスト の rank = n
-/

namespace ST

universe u v

/-! ## Ranked インスタンス定義 -/

/-- リストの長さを rank 関数とする Ranked インスタンス -/
instance instRankedList {α : Type u} : Ranked ℕ (List α) where
  rank := List.length

/-! ## 基本性質 -/

variable {α : Type u}

/-- layer定義の具体化 -/
lemma list_layer_iff (n : ℕ) (l : List α) :
    l ∈ (instRankedList : Ranked ℕ (List α)).layer n ↔ l.length ≤ n := by
  rfl

/-- 単調性の確認 -/
lemma list_layer_mono {m n : ℕ} (h : m ≤ n) :
    (instRankedList : Ranked ℕ (List α)).layer m ⊆
    (instRankedList : Ranked ℕ (List α)).layer n := by
  exact Ranked.layer_mono (R := instRankedList) h

/-- 空リストは layer 0 に属する -/
lemma nil_in_layer_zero :
    ([] : List α) ∈ (instRankedList : Ranked ℕ (List α)).layer 0 := by
  simp [Ranked.layer, instRankedList]

/-- n 要素リストは layer n に属する -/
lemma list_in_layer_self (l : List α) :
    l ∈ (instRankedList : Ranked ℕ (List α)).layer l.length := by
  simp [Ranked.layer, instRankedList]

/-! ## 計算可能な例 -/

-- 空リストの rank
example : (instRankedList : Ranked ℕ (List ℕ)).rank [] = 0 := rfl

-- 単一要素リストの rank
example : (instRankedList : Ranked ℕ (List ℕ)).rank [1] = 1 := rfl

-- 2要素リストの rank
example : (instRankedList : Ranked ℕ (List ℕ)).rank [1, 2] = 2 := rfl

-- 3要素リストの rank
example : (instRankedList : Ranked ℕ (List ℕ)).rank [1, 2, 3] = 3 := rfl

-- 5要素リストの rank
example : (instRankedList : Ranked ℕ (List ℕ)).rank [1, 2, 3, 4, 5] = 5 := rfl

-- #eval での動作確認
#eval (instRankedList : Ranked ℕ (List ℕ)).rank []
#eval (instRankedList : Ranked ℕ (List ℕ)).rank [1]
#eval (instRankedList : Ranked ℕ (List ℕ)).rank [1, 2, 3]
#eval (instRankedList : Ranked ℕ (List String)).rank ["a", "b", "c", "d"]

/-! ## StructureTower変換 -/

/-- TowerWithMinへの変換（List用） -/
def listAsStructureTower {α : Type u} : StructureTowerWithMin :=
  toNatTowerWithMin (instRankedList : Ranked ℕ (List α))

/-- 変換後の層が元の層と一致 -/
lemma list_tower_layer_eq (n : ℕ) :
    listAsStructureTower.layer n =
    (instRankedList : Ranked ℕ (List α)).layer n := by
  rfl

/-- 変換後の minLayer が rank と一致 -/
lemma list_tower_minLayer_eq (l : List α) :
    listAsStructureTower.minLayer l = l.length := by
  rfl

/-! ## RankHomLe: List → Finset -/

/-- 重複除去で濃度が減るので、`List` から `Finset` への RankHomLe。 -/
def listToFinsetRankHomLe (α : Type u) [DecidableEq α] :
    RankHomLe (instRankedList : Ranked ℕ (List α))
              (instRankedFinset : Ranked ℕ (Finset α)) where
  map := List.toFinset
  indexMap := id
  mono := by
    intro a b hab
    exact hab
  rank_le := by
    intro l
    simpa [instRankedList, instRankedFinset] using (List.toFinset_card_le (l := l))

end ST
