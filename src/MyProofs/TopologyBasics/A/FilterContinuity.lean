import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Order.Filter.Basic

/-!
# フィルターを用いた連続性の現代的定義

ブルバキ流の位相空間論における最も洗練された視点：
フィルターによる連続性の特徴付け

## 数学的背景
位相空間論の現代的展開において、フィルターは最も基本的かつ強力な概念である。
ブルバキの「位相」において、この概念は収束と連続性を統一的に扱う道具として導入される。
-/

namespace TopologyBasics.FilterContinuity

open Topology Filter Set

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- 近傍フィルターによる連続性の基本的特徴付け -/
theorem filter_continuous_basic (f : X → Y) (x : X) :
    ContinuousAt f x ↔ Tendsto f (𝓝 x) (𝓝 (f x)) := by
  rfl

/-- フィルターの視点から見た連続写像の合成 -/
theorem filter_continuous_comp {f : X → Y} {g : Y → Z} 
    (hf : Continuous f) (hg : Continuous g) (x : X) :
    Tendsto (g ∘ f) (𝓝 x) (𝓝 ((g ∘ f) x)) := by
  have : ContinuousAt (g ∘ f) x := ContinuousAt.comp (hg.continuousAt) (hf.continuousAt)
  rw [← filter_continuous_basic]
  exact this

/-- 恒等写像のフィルター連続性 -/
theorem filter_continuous_id (x : X) :
    Tendsto id (𝓝 x) (𝓝 x) := by
  exact tendsto_id

/-- 定数写像のフィルター連続性 -/
theorem filter_continuous_const (y : Y) (x : X) :
    Tendsto (fun _ => y) (𝓝 x) (𝓝 y) := by
  exact tendsto_const_nhds

/-- 連続性とフィルター収束の同値性 -/
theorem continuous_iff_filter (f : X → Y) :
    Continuous f ↔ ∀ x, Tendsto f (𝓝 x) (𝓝 (f x)) := by
  simp only [continuous_iff_continuousAt, filter_continuous_basic]

/-- 写像の連続性の逆像による特徴付けとフィルターの関係 -/
theorem continuous_iff_preimage_and_filter (f : X → Y) :
    Continuous f ↔ 
    (∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U)) ∧
    (∀ x : X, Tendsto f (𝓝 x) (𝓝 (f x))) := by
  constructor
  · intro hf
    have h1 : ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := fun U hU => hf.isOpen_preimage U hU
    have h2 : ∀ x : X, Tendsto f (𝓝 x) (𝓝 (f x)) := by
      intro x
      rw [← filter_continuous_basic]
      exact hf.continuousAt
    exact ⟨h1, h2⟩
  · intro ⟨h_open, _⟩
    rw [continuous_def]
    exact h_open

end TopologyBasics.FilterContinuity