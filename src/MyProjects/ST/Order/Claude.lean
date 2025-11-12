import Mathlib.Data.Set.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Order.Basic
import MyProjects.ST.CAT2_complete

open Set

/-!
# Order Theory と構造塔

このファイルは OrderTheory.md で提示された構造塔的アプローチを、ニコラ・ブルバキの集合論的精神にならって Lean で形式化する試みです。
構造塔は集合に階層的な層構造を与えることで順序論・圏論的普遍性を代数的に整理する道具です。
ここでは Dilworth の高さ関数、到達可能性、フィルトレーション、計算複雑性の具体例を `StructureTowerWithMin` で表現し、Stone-Čech、Galois、Doob 分解のスケッチもコメントとして残します。
-/

namespace OrderTheory

/-- 任意の `f : α → β` を `minLayer` に使い、点 `x` が `f x ≤ i` を満たす層 `i` に属する構造塔を作る補助関数。 -/
def leLayerTower {α β : Type*} [Preorder β] (f : α → β) : StructureTowerWithMin where
  carrier := α
  Index := β
  indexPreorder := inferInstance
  layer := fun i => { x | f x ≤ i }
  covering := fun x => ⟨f x, le_refl _⟩
  monotone := fun {_ _} hij => fun _ hx =>
    Set.mem_setOf.2 (le_trans (Set.mem_setOf.1 hx) hij)
  minLayer := f
  minLayer_mem := fun _ => le_refl _
  minLayer_minimal := fun _ _ hx => hx

/-! ## 1. Dilworth の高さ -/

/-- 有限半順序の元 `x` に対して最長鎖の長さ `height x` を `minLayer` として使う構造塔。
`height` は `x` を含む最大の連鎖長で、層の個数と最小鎖分解数の一致を階層的に示唆する。 -/
def dilworthHeightTower {α : Type*} [Preorder α] (height : α → ℕ) : StructureTowerWithMin :=
  leLayerTower height

/-! ## 2. Stone-Čech コンパクト化のスケッチ

Stone-Čech の普遍性を `StructureTowerWithMin` に接続するには、連続写像全体を添字にとり、各点で最小の連続関数を `minLayer` が選ぶような補助構造を想定します。 -/

/-! ## 3. 到達可能性と距離 -/

/-- 有向グラフ `G = (V, E)` と始点 `start` に対する距離関数 `dist` を `minLayer` に使った構造塔。
`layer n = { v | dist v ≤ n }` により最短経路の空間を階層的に取り込む。 -/
structure Digraph (V : Type*) where
  edge : V → V → Prop

/-- `dist` は `start` からの最短距離を表し、到達可能集合を層として返す。 -/
def reachabilityTower {V : Type*} (_ : Digraph V) (_ : V) (dist : V → ℕ) : StructureTowerWithMin :=
  leLayerTower dist

/-! ## 4. Galois 対応の塔的スケッチ -/

/-- 体の拡大  に対する中間体と対応する部分群の間の Galois 対応を構造塔のレベルで捉えるスケッチ。
 が最小の中間体・生成部分群を示すことで可解性・群の分解を視覚化する。 -/
structure GaloisTowerSketch (K L : Type*) [Field K] [Field L] where
  intermediate_fields : Set (Set L)
  subgroup_layers : Set (Set (L → L))
  field_min_layer : L → Set L
  group_min_layer : (L → L) → Set (L → L)

/-! ## 5. スペクトル系列とフィルトレーション

有限フィルトレーション `F` を層と捉えるには `Fₙ` を添字 `n` に対応させ、`minLayer x` が `x` の属する最小の `Fₙ` を返すように設計すれば `StructureTowerWithMin` の観点から `E^r` ページや収束性を再解釈できます。 -/

/-! ## 6. 計算複雑性の層 -/

/-- 代表的な計算複雑性クラス。 -/
inductive ComplexityClass where
  | P
  | NP
  | PSPACE
  | EXPTIME

def ComplexityClass.rank : ComplexityClass → ℕ
  | ComplexityClass.P => 0
  | ComplexityClass.NP => 1
  | ComplexityClass.PSPACE => 2
  | ComplexityClass.EXPTIME => 3

/-- 決定問題  を複雑性クラスに写す  を  に使う構造塔。 -/
def complexityTower (Problem : Type*) (classOf : Problem → ComplexityClass) : StructureTowerWithMin :=
  leLayerTower fun prob => ComplexityClass.rank (classOf prob)

/-! ## 7. Doob 分解の構造塔的見取り図 -/

/-- 頻度フィルトレーション `ℱ : ℕ → Set Ω` に対して `minLayer` が停止時刻を制御することで、
Doob 分解の一意性が構造塔の普遍性から導かれる構想。 -/
structure DoobDecompositionSketch (Ω : Type*) (ℱ : ℕ → Set Ω) (X : ℕ → Ω → Real) where
  filtration_tower : StructureTowerWithMin
  martingale_component : ℕ → Ω → Real
  increasing_component : ℕ → Ω → Real
  uniqueness_hint : Prop

/-! ## 例 / Examples -/

example : StructureTowerWithMin :=
  dilworthHeightTower fun (_ : Fin 1) => 0

example : StructureTowerWithMin :=
  complexityTower (Fin 1) fun _ => ComplexityClass.NP

end OrderTheory
