/-
  ブルバキ流測度論基礎
  σ-代数の性質と可測写像の合成
  
  Nicolas Bourbaki "Éléments de mathématique" 
  - Livre I: Théorie des ensembles, Chapitre II: Éléments de la théorie des ensembles
  - Livre III: Topologie générale, Chapitre IX: Usage des nombres réels en topologie générale
-/

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic

namespace BourbakiMeasure

section BourbakiDefinitions

/-- σ-代数の定義（ブルバキ第3巻第9章） -/
structure BourbakiMeasurableSpace (Ω : Type*) where
  MeasurableSet : Set Ω → Prop
  measurableSet_empty : MeasurableSet ∅
  measurableSet_compl : ∀ s, MeasurableSet s → MeasurableSet sᶜ
  measurableSet_iUnion : ∀ f : ℕ → Set Ω,
    (∀ i, MeasurableSet (f i)) → MeasurableSet (⋃ i, f i)

/-- 可測写像の定義 -/
def BourbakiMeasurable {Ω₁ Ω₂ : Type*} (τ₁ : BourbakiMeasurableSpace Ω₁) (τ₂ : BourbakiMeasurableSpace Ω₂)
    (f : Ω₁ → Ω₂) : Prop :=
  ∀ s, τ₂.MeasurableSet s → τ₁.MeasurableSet (f ⁻¹' s)

end BourbakiDefinitions

section MathlibVersion

/-- Mathlib版：可測写像の合成定理 -/
theorem measurable_comp_mathlib {Ω₁ Ω₂ Ω₃ : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
    {f : Ω₁ → Ω₂} {g : Ω₂ → Ω₃}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (g ∘ f) := by
  -- Mathlibの標準定理を使用
  exact Measurable.comp hg hf

/-- 手動証明版：可測写像の合成定理 -/
theorem measurable_comp_manual {Ω₁ Ω₂ Ω₃ : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
    {f : Ω₁ → Ω₂} {g : Ω₂ → Ω₃}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (g ∘ f) := by
  -- 可測性の定義から証明
  intro s hs
  -- sがΩ₃の可測集合
  -- g⁻¹(s)がΩ₂の可測集合（gの可測性から）
  have h1 : MeasurableSet (g ⁻¹' s) := hg hs
  -- f⁻¹(g⁻¹(s))がΩ₁の可測集合（fの可測性から）
  have h2 : MeasurableSet (f ⁻¹' (g ⁻¹' s)) := hf h1
  -- (g ∘ f)⁻¹(s) = f⁻¹(g⁻¹(s))
  have h3 : (g ∘ f) ⁻¹' s = f ⁻¹' (g ⁻¹' s) := by
    ext x
    simp only [Set.mem_preimage, Function.comp_apply]
  -- 結論
  rwa [h3]

end MathlibVersion

section BourbakiProof

/-- ブルバキ流証明：可測写像の合成定理 -/
theorem bourbaki_measurable_comp {Ω₁ Ω₂ Ω₃ : Type*}
    (τ₁ : BourbakiMeasurableSpace Ω₁)
    (τ₂ : BourbakiMeasurableSpace Ω₂)
    (τ₃ : BourbakiMeasurableSpace Ω₃)
    {f : Ω₁ → Ω₂} {g : Ω₂ → Ω₃}
    (hf : BourbakiMeasurable τ₁ τ₂ f)
    (hg : BourbakiMeasurable τ₂ τ₃ g) :
    BourbakiMeasurable τ₁ τ₃ (g ∘ f) := by
  -- 可測性の定義から
  intro s hs
  -- sがΩ₃の可測集合のとき、(g ∘ f)⁻¹(s)がΩ₁の可測集合であることを示す
  -- まず (g ∘ f)⁻¹(s) = f⁻¹(g⁻¹(s))
  have h_eq : (g ∘ f) ⁻¹' s = f ⁻¹' (g ⁻¹' s) := by
    ext x
    simp only [Set.mem_preimage, Function.comp_apply]
  -- g⁻¹(s)がΩ₂の可測集合（gの可測性から）
  have h1 : τ₂.MeasurableSet (g ⁻¹' s) := hg s hs
  -- f⁻¹(g⁻¹(s))がΩ₁の可測集合（fの可測性から）
  have h2 : τ₁.MeasurableSet (f ⁻¹' (g ⁻¹' s)) := hf (g ⁻¹' s) h1
  -- 結論
  rwa [h_eq]

end BourbakiProof

section SigmaAlgebraProperties

variable {Ω : Type*} [MeasurableSpace Ω]

/-- σ-代数の基本性質：2つの集合の和集合 -/
theorem measurableSet_union {s t : Set Ω} 
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (s ∪ t) := by
  -- 2つの集合の和集合
  exact MeasurableSet.union hs ht

/-- σ-代数の基本性質：2つの集合の積集合 -/
theorem measurableSet_inter {s t : Set Ω} 
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (s ∩ t) := by
  -- 2つの集合の積集合
  exact MeasurableSet.inter hs ht

/-- σ-代数の基本性質：可算積集合 -/
theorem measurableSet_iInter_concept {f : ℕ → Set Ω} 
    (h : ∀ i, MeasurableSet (f i)) :
    MeasurableSet (⋂ i, f i) := by
  -- De Morganの法則によるMathlibの定理
  apply MeasurableSet.iInter
  exact h

end SigmaAlgebraProperties

section Applications

/-- 応用：定数関数の可測性 -/
theorem measurable_const_concept {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] 
    (c : Ω₂) : Measurable (fun _ : Ω₁ => c) := by
  -- 定数関数は常に可測
  exact measurable_const

/-- 応用：恒等関数の可測性 -/
theorem measurable_identity_concept {Ω : Type*} [MeasurableSpace Ω] :
    Measurable (fun x : Ω => x) := by
  -- 恒等関数は常に可測
  exact measurable_id

end Applications

end BourbakiMeasure