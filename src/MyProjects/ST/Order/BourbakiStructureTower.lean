import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic
import Mathlib.Topology.Basic
import MyProjects.ST.CAT2_complete

/-!
# Bourbaki-Style Structure Towers

Lean でニコラ・ブルバキの集合論的な構造の精神にしたがって、
Claude.md で提案された構造塔的な例題を `StructureTowerWithMin` の上で
書き下したモジュールです。各節は「層を与える関数」さえ渡せば構造塔が
自動で組み上がる簡潔さを大切にし、構造塔の最小層 `minLayer` によって
具体例（Dilworth、Stone-Čech、到達可能性、Galois、スペクトル系列、計算複雑性、
Doob 分解）がどのように「束ねられるか」のナラティブを維持します。

`CAT2_complete.lean` の `StructureTowerWithMin` を中心に据え、
それぞれの例で想定される `minLayer` 関数を `leLayerTower` で束ねるとともに、
各種のスケッチ `structure` で補助的なフィールドを保持します。
-/

namespace BourbakiStructureTower

open StructureTowerWithMin

/-- `f : α → β` を `StructureTowerWithMin` に変換する商用ビルディングブロック。 -/
def leLayerTower {α β : Type*} [Preorder β] (f : α → β) : StructureTowerWithMin where
  carrier := α
  Index := β
  indexPreorder := inferInstance
  layer := fun i => { x | f x ≤ i }
  covering := fun x => ⟨f x, le_refl (f x)⟩
  monotone := fun {_ _} hij _ hx => le_trans hx hij
  minLayer := f
  minLayer_mem := fun _ => le_refl _
  minLayer_minimal := fun _ _ hx => hx

/-! ## 1. Dilworth の高さ関数 -/

/-- 有限半順序に `height` を与えると、`minLayer` をそのまま高さとみなす構造塔。 -/
def dilworthHeightTower {α : Type*} [Preorder α] (height : α → ℕ) : StructureTowerWithMin :=
  leLayerTower height

theorem dilworthHeightTower_minLayer {α : Type*} [Preorder α] (height : α → ℕ) (x : α) :
    (dilworthHeightTower height).minLayer x = height x := rfl

/-! ## 2. Stone-Čech コンパクト化のスケッチ -/

/-- Stone-Čech コンパクト化を構造塔として見るときのスケッチ。 -/
structure StoneCechTowerSketch (X βX : Type*) [TopologicalSpace X] [TopologicalSpace βX] where
  /-- 基底空間として Stone-Čech が持つ構造塔本体。 -/
  tower : StructureTowerWithMin
  /-- `βX` の各点に連続関数を対応させる添字空間の同型。 -/
  index_iso : tower.Index ≃ { f : X → βX // Continuous f }
  /-- 各点に対応する「最小の」連続関数。 -/
  choose : tower.carrier → { f : X → βX // Continuous f }
  /-- `minLayer` がまさにその連続関数を選ぶ。 -/
  minLayer_def : ∀ b, tower.minLayer b = index_iso.symm (choose b)
  /-- キャリアは `βX` と一致させている。 -/
  carrier_eq : tower.carrier = βX

/-! ## 3. 到達可能性と有向グラフ -/

/-- 有向グラフ。 -/
structure Digraph (V : Type*) where
  edge : V → V → Prop

/-- 与えられた距離 `dist` で構造塔を構成する。 -/
def reachabilityTower {V : Type*} (dist : V → ℕ) : StructureTowerWithMin := leLayerTower dist

theorem reachabilityTower_minLayer {V : Type*} (dist : V → ℕ) (v : V) :
    (reachabilityTower dist).minLayer v = dist v := rfl

/-! ## 4. Galois 対応のスケッチ -/

/-- 中間体と部分群の塔を構造塔的に保持するスケッチ。 -/
structure GaloisTowerSketch (K L : Type*) [Field K] [Field L] where
  tower : StructureTowerWithMin
  intermediate_fields : Set (Set L)
  subgroup_layers : Set (Set (L → L))
  field_minLayer : L → Set L
  group_minLayer : (L → L) → Set (L → L)
  /-- `field_minLayer` が各元の最小中間体を返すという直感的プロパティ。 -/
  field_minLayer_mem : ∀ x, x ∈ field_minLayer x

/-! ## 5. スペクトル系列とフィルトレーション -/

/-- フィルトレーション `F` と `minLayer` を用いて構造塔を確認するためのデータ。 -/
structure FiltrationTowerSketch (C : Type*) (F : ℕ → Set C) where
  min_layer : C → ℕ
  min_layer_mem : ∀ x, x ∈ F (min_layer x)
  min_layer_minimal : ∀ x n, x ∈ F n → min_layer x ≤ n
  /-- フィルトレーション由来の構造塔（`minLayer` をそのまま投げる）。 -/
  tower : StructureTowerWithMin := leLayerTower min_layer

/-! ## 6. 計算複雑性理論の塔 -/

/-- 代表的な複雑性クラス。 -/
inductive ComplexityClass where
  | P
  | NP
  | PSPACE
  | EXPTIME

/-! Convert to natural numbers for ordering. -/
def ComplexityClass.rank : ComplexityClass → ℕ
  | ComplexityClass.P => 0
  | ComplexityClass.NP => 1
  | ComplexityClass.PSPACE => 2
  | ComplexityClass.EXPTIME => 3

instance : Preorder ComplexityClass where
  le := fun c d => ComplexityClass.rank c ≤ ComplexityClass.rank d
  le_refl := fun _ => le_rfl
  le_trans := fun _ _ _ h₁ h₂ => le_trans h₁ h₂

/-- 問題を複雑性クラスに対応させる `StructureTowerWithMin`。 -/
def complexityTower (Problem : Type*) (classOf : Problem → ComplexityClass) : StructureTowerWithMin :=
  leLayerTower classOf

theorem complexityTower_minLayer {Problem : Type*} (classOf : Problem → ComplexityClass)
    (x : Problem) :
    (complexityTower Problem classOf).minLayer x = classOf x := rfl

/-- P と NP の順序。 -/
example : ComplexityClass.rank ComplexityClass.P ≤ ComplexityClass.rank ComplexityClass.NP := by
  dsimp [ComplexityClass.rank]
  decide
/-! ## 7. Doob 分解のスケッチ -/

/-- 停止時刻を `minLayer` として持つ分解スケッチ。 -/
structure DoobDecompositionSketch (Ω : Type*) where
  filtration : ℕ → Set Ω
  stopping_time : Ω → ℕ
  stopping_mem : ∀ ω, ω ∈ filtration (stopping_time ω)
  stopping_minimal : ∀ ω n, ω ∈ filtration n → stopping_time ω ≤ n
  tower : StructureTowerWithMin := leLayerTower stopping_time

theorem DoobDecompositionSketch_minLayer {Ω : Type*} (sk : DoobDecompositionSketch Ω) :
    (leLayerTower sk.stopping_time).minLayer = sk.stopping_time := rfl

/-! ## 補助データ -/

/-- Stone-Čech のようなスケッチと `filtration` をまとめて格納する poetica な中間構成体。 -/
structure BourbakiPortfolio (X βX : Type*) [TopologicalSpace X] [TopologicalSpace βX] where
  stone_cech : StoneCechTowerSketch X βX
  galois : GaloisTowerSketch ℝ ℝ
  filtration : FiltrationTowerSketch ℝ fun n => Set.univ

end BourbakiStructureTower
