import MyProjects.ST.CAT.Cat_D
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Basic
import Mathlib.Tactic

/-
# Cat_D 追加例と簡単な射

ブルバキ『数学原論』の集合論的精神に従い、最小限の仮定で構造塔の具体例と射を構成する。
複雑な indexMap を避け、存在量化だけで層保存を示す簡潔な例をまとめた。
-/

open Set

namespace ST.TowerD.Advanced

/-- 自然数の初期区間による構造塔

layer n = {k | k ≤ n}。被覆性も単調性も自明に成立する。
-/
def natSegmentTower : TowerD where
  carrier := ℕ
  Index := ℕ
  indexPreorder := inferInstance
  layer n := {k : ℕ | k ≤ n}
  covering := by
    intro k
    refine ⟨k, ?_⟩
    change k ≤ k
    exact le_rfl
  monotone := by
    intro i j hij k hk
    exact le_trans hk hij

/-- 層 membership の開き直し -/
lemma natSegmentTower_mem_layer {k n : ℕ} :
    k ∈ natSegmentTower.layer n ↔ k ≤ n := by
  rfl

/-- 動作確認：3 は層 5 に属する -/
example : (3 : ℕ) ∈ natSegmentTower.layer (5 : ℕ) := by
  change (3 : ℕ) ≤ 5
  decide


/-- 実数の上向き区間による構造塔（添字も実数） -/
def realIntervalTowerR : TowerD where
  carrier := ℝ
  Index := ℝ
  indexPreorder := inferInstance
  layer n := {x : ℝ | x ≤ n}
  covering := by
    intro x
    refine ⟨x, ?_⟩
    change x ≤ x
    exact le_rfl
  monotone := by
    intro i j hij x hx
    exact le_trans hx hij

/-- 層 membership の開き直し（実数版） -/
lemma realIntervalTowerR_mem_layer (x n : ℝ) :
    x ∈ realIntervalTowerR.layer n ↔ x ≤ n := by
  rfl

/-- 動作確認：3 ≤ 5 による membership -/
example : (3 : ℝ) ∈ realIntervalTowerR.layer (5 : ℝ) := by
  change (3 : ℝ) ≤ 5
  norm_num


/-- ℕ を ℝ に埋め込む標準写像が誘導する射 -/
def natToRealInterval : natSegmentTower ⟶ᴰ realIntervalTowerR where
  map := fun (n : ℕ) => (n : ℝ)
  map_layer := by
    intro (i : ℕ)
    refine ⟨(i : ℝ), ?_⟩
    change Set.image (fun n : ℕ => (n : ℝ)) {k : ℕ | k ≤ i} ⊆ _
    intro y hy
    rcases hy with ⟨k, hk, rfl⟩
    -- hk : k ≤ i
    have hk_real : (k : ℝ) ≤ (i : ℝ) := by exact_mod_cast hk
    simpa [realIntervalTowerR] using hk_real

end ST.TowerD.Advanced
