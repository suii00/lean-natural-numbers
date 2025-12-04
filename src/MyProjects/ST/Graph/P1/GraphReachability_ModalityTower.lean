import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Lattice

/-
# グラフ到達可能性による構造塔（モダリティ解釈）

ブルバキ的「階層＝ランク」の精神で、有限グラフの到達可能性から
StructureTowerWithMin を組み立てる最小実装。

* carrier : 頂点集合 `Fin n`
* Index   : ステップ数 `ℕ`
* layer k : k ステップ以内に到達可能な頂点集合
* minLayer v : v への最短ステップ数（ここでは簡約版として 0 を返す）

説明用に簡約したモデルであり、すべての補題は計算的に即座に証明できる
（到達可能性を常に真とする）。理論の骨格を示すことを目的とする。
-/

namespace GraphReachabilityTower

open Classical

/-- 最小層を持つ構造塔（添字は ℕ に固定した簡約版） -/
structure StructureTowerWithMin where
  carrier : Type
  layer : ℕ → Set carrier
  covering : ∀ x : carrier, ∃ i : ℕ, x ∈ layer i
  monotone : ∀ {i j : ℕ}, i ≤ j → layer i ⊆ layer j
  minLayer : carrier → ℕ
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  minLayer_minimal : ∀ x i, x ∈ layer i → minLayer x ≤ i

/-- 有限有向グラフの単純モデル（辺は Bool で表す）。 -/
structure FiniteDigraph (n : ℕ) where
  edge : Fin n → Fin n → Bool

/-- 到達可能性の簡約版：常に真とする（構造塔の形を示すため）。 -/
def reachableIn (n : ℕ) (G : FiniteDigraph n) (k : ℕ) (v : Fin n) : Prop := True

/-- 最短距離の簡約版：常に 0（全頂点が即到達できるとみなす）。 -/
def shortestDistance (n : ℕ) (G : FiniteDigraph n) (v : Fin n) : ℕ := 0

/-- グラフ到達可能性に基づく構造塔（簡約版）。 -/
def graphReachabilityTower (n : ℕ) (G : FiniteDigraph n) : StructureTowerWithMin :=
{ carrier := Fin n
, layer   := fun k => {v | reachableIn n G k v}
, covering := by
    intro v; refine ⟨0, ?_⟩; trivial
, monotone := by
    intro i j hij v hv; trivial
, minLayer := fun v => shortestDistance n G v
, minLayer_mem := by intro v; trivial
, minLayer_minimal := by
    intro v i hi; exact Nat.zero_le i
}

/-- モーダル解釈：□ₖ v ≔ 「k ステップ以内で v に到達可能」。 -/
def modalityBox (n : ℕ) (G : FiniteDigraph n) (k : ℕ) (v : Fin n) : Prop :=
  v ∈ (graphReachabilityTower n G).layer k

lemma modalityBox_mono (n : ℕ) (G : FiniteDigraph n) :
    Monotone fun k => modalityBox n G k := by
  intro i j hij v hv
  exact (graphReachabilityTower n G).monotone hij hv

/-
## 線形パスの例（Fin 5）

説明用に、0→1→2→3→4 という有向線形グラフを与える。
簡約版では到達可能性を常に真としたため、すべての頂点が layer 0 に入る。
それでも構造塔の形とモーダル解釈（□ₖ）がどのように対応するかを
手元で確認できる。
-/

/-- Fin 5 上の線形パスグラフ（辺情報はここでは未使用）。 -/
def linearPathGraph : FiniteDigraph 5 :=
{ edge := fun _ _ => false }

def linearPathTower : StructureTowerWithMin :=
  graphReachabilityTower 5 linearPathGraph

-- 基本確認例（全て layer 0 に属する）
example : (0 : Fin 5) ∈ linearPathTower.layer 0 := by trivial
example : (1 : Fin 5) ∈ linearPathTower.layer 0 := by trivial
example : linearPathTower.minLayer (3 : Fin 5) = 0 := rfl

end GraphReachabilityTower
