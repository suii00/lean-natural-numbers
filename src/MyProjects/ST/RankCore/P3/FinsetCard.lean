import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Powerset
import MyProjects.ST.RankCore.Basic
import MyProjects.ST.RankCore.Bridge.ToTowerWithMin

/-!
# FinsetCard - 有限集合の濃度によるRanked構造

## 概要
有限集合の濃度 `Finset.card` を rank 関数とする Ranked 構造の例。
layer n は「濃度が n 以下のすべての有限集合」を表す。

## 数学的意義
- rank : Finset α → ℕ は Finset.card
- layer n = {S : Finset α | S.card ≤ n}
- minLayer S = S.card（自然な最小構造選択）

## 典型的な使用例
- 空集合 ∅ の rank = 0
- 単元集合 {x} の rank = 1
- n 元集合 の rank = n

## 応用
- 組合せ論における集合の階層構造
- マトロイドの rank 関数の離散版
- 計算複雑性の階層分類
-/

namespace ST

universe u v

/-! ## Ranked インスタンス定義 -/

/-- 有限集合の濃度を rank 関数とする Ranked インスタンス -/
instance instRankedFinset {α : Type u} : Ranked ℕ (Finset α) where
  rank := Finset.card

/-! ## 基本性質 -/

variable {α : Type u}

/-- layer定義の具体化 -/
lemma finset_layer_iff (n : ℕ) (S : Finset α) :
    S ∈ (instRankedFinset : Ranked ℕ (Finset α)).layer n ↔ S.card ≤ n := by
  rfl

/-- 単調性の確認 -/
lemma finset_layer_mono {m n : ℕ} (h : m ≤ n) :
    (instRankedFinset : Ranked ℕ (Finset α)).layer m ⊆
    (instRankedFinset : Ranked ℕ (Finset α)).layer n := by
  exact Ranked.layer_mono (R := instRankedFinset) h

/-- 空集合は layer 0 に属する -/
lemma empty_in_layer_zero :
    (∅ : Finset α) ∈ (instRankedFinset : Ranked ℕ (Finset α)).layer 0 := by
  simp [Ranked.layer, instRankedFinset]

/-- n 元集合は layer n に属する -/
lemma finset_in_layer_self (S : Finset α) :
    S ∈ (instRankedFinset : Ranked ℕ (Finset α)).layer S.card := by
  simp [Ranked.layer, instRankedFinset]

/-- 部分集合のrankは小さい -/
lemma rank_subset {S T : Finset α} (h : S ⊆ T) :
    (instRankedFinset : Ranked ℕ (Finset α)).rank S ≤
    (instRankedFinset : Ranked ℕ (Finset α)).rank T := by
  simpa using (Finset.card_le_card h)

/-! ## 計算可能な例 -/

-- 空集合の rank
example : (instRankedFinset : Ranked ℕ (Finset ℕ)).rank ∅ = 0 := rfl

-- 単元集合の rank
example : (instRankedFinset : Ranked ℕ (Finset ℕ)).rank {1} = 1 := rfl

-- 2元集合の rank
example : (instRankedFinset : Ranked ℕ (Finset ℕ)).rank {1, 2} = 2 := rfl

-- 3元集合の rank
example : (instRankedFinset : Ranked ℕ (Finset ℕ)).rank {1, 2, 3} = 3 := rfl

-- 4元集合の rank
example : (instRankedFinset : Ranked ℕ (Finset ℕ)).rank {1, 2, 3, 4} = 4 := rfl

-- layer membership check
example : ({1, 2} : Finset ℕ) ∈ (instRankedFinset : Ranked ℕ (Finset ℕ)).layer 2 := by
  simp [Ranked.layer, instRankedFinset]

-- #eval での動作確認
#eval (instRankedFinset : Ranked ℕ (Finset ℕ)).rank ∅
#eval (instRankedFinset : Ranked ℕ (Finset ℕ)).rank {1}
#eval (instRankedFinset : Ranked ℕ (Finset ℕ)).rank {1, 2, 3}
#eval (instRankedFinset : Ranked ℕ (Finset ℕ)).rank {5, 10, 15, 20}

/-! ## StructureTower変換 -/

/-- TowerWithMinへの変換（Finset用） -/
def finsetAsStructureTower {α : Type u} : StructureTowerWithMin :=
  toNatTowerWithMin (instRankedFinset : Ranked ℕ (Finset α))

/-- 変換後の層が元の層と一致 -/
lemma finset_tower_layer_eq (n : ℕ) :
    finsetAsStructureTower.layer n =
    (instRankedFinset : Ranked ℕ (Finset α)).layer n := by
  rfl

/-- 変換後の minLayer が rank と一致 -/
lemma finset_tower_minLayer_eq (S : Finset α) :
    finsetAsStructureTower.minLayer S = S.card := by
  rfl

/-! ## 組合せ論的性質 -/

/-- Rank bound for `List.toFinset`, used in the `ListLength → FinsetCard` RankHomLe. -/
lemma toFinset_rank_le_length [DecidableEq α] (l : List α) :
    (instRankedFinset : Ranked ℕ (Finset α)).rank l.toFinset ≤ l.length := by
  simpa [instRankedFinset] using (List.toFinset_card_le (l := l))

/-- 層 n には高々 C(|α|, 0) + ... + C(|α|, n) 個の要素しかない（α が有限のとき） -/
lemma layer_finite_when_base_finite [Fintype α] (n : ℕ) :
    Set.Finite ((instRankedFinset : Ranked ℕ (Finset α)).layer n) := by
  refine (Set.finite_univ.subset ?_)
  intro S hS
  exact Set.mem_univ S

end ST
