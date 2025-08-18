/-
  ブルバキ流集合論・写像理論
  一般位相空間における連続写像の合成定理
  
  Nicolas Bourbaki "Éléments de mathématique" 
  - Livre I: Théorie des ensembles, Chapitre II: Éléments de la théorie des ensembles
  - Livre III: Topologie générale, Chapitre I: Structures topologiques
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Continuous
import Mathlib.Data.Set.Basic

namespace BourbakiTopology

/-- 位相空間の定義（ブルバキ第3巻第1章）-/
structure BourbakiTopologicalSpace (X : Type*) where
  IsOpen : Set X → Prop
  isOpen_univ : IsOpen Set.univ
  isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  isOpen_sUnion : ∀ S, (∀ s ∈ S, IsOpen s) → IsOpen (⋃₀ S)

/-- 連続写像の定義 -/
def BourbakiContinuous {X Y : Type*} (τX : BourbakiTopologicalSpace X) (τY : BourbakiTopologicalSpace Y)
    (f : X → Y) : Prop :=
  ∀ U, τY.IsOpen U → τX.IsOpen (f ⁻¹' U)

/-- 連続写像の合成定理 -/
theorem bourbaki_continuous_comp {X Y Z : Type*}
    (τX : BourbakiTopologicalSpace X)
    (τY : BourbakiTopologicalSpace Y)
    (τZ : BourbakiTopologicalSpace Z)
    {f : X → Y} {g : Y → Z}
    (hf : BourbakiContinuous τX τY f)
    (hg : BourbakiContinuous τY τZ g) :
    BourbakiContinuous τX τZ (g ∘ f) := by
  intro W hW
  -- Wが開集合である
  -- g⁻¹(W)が開集合であることを示す（gの連続性から）
  have h1 : τY.IsOpen (g ⁻¹' W) := hg W hW
  -- f⁻¹(g⁻¹(W))が開集合であることを示す（fの連続性から）
  have h2 : τX.IsOpen (f ⁻¹' (g ⁻¹' W)) := hf (g ⁻¹' W) h1
  -- (g ∘ f)⁻¹(W) = f⁻¹(g⁻¹(W))を示す
  have h3 : (g ∘ f) ⁻¹' W = f ⁻¹' (g ⁻¹' W) := by
    ext x
    simp [Set.preimage, Function.comp]
  -- 結論
  rw [h3]
  exact h2

end BourbakiTopology

section MathlibVersion

open Topology

/-- Mathlib版：連続写像の合成定理 -/
theorem continuous_comp_mathlib {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous (g ∘ f) := by
  -- Mathlibの標準ライブラリにある定理を使用
  exact Continuous.comp hg hf

/-- 手動証明版：連続写像の合成定理 -/
theorem continuous_comp_manual {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous (g ∘ f) := by
  -- 連続性の定義から証明
  apply Continuous.comp
  · exact hg
  · exact hf

end MathlibVersion