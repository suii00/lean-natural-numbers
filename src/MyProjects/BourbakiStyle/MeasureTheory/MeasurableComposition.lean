/-
  Module     : MyProjects.BourbakiStyle.MeasureTheory.MeasurableComposition
  Overview   : Bourbaki-style σ-structures and measurability morphisms
  Reference  : Nicolas Bourbaki, Éléments de mathématique

  We model σ-structures as sets of subsets (ordered-pair viewpoint) and
  measurable morphisms as ordered pairs (function, structural proof).
  The composition of morphisms remains a morphism, matching Mathlib''s
  `Measurable.comp`.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Data.Set.Lattice

open Set

namespace MyProjects
namespace BourbakiStyle
namespace MeasureTheory

universe u v w

/-- Bourbaki-style σ-structure: a set of subsets closed under the σ-algebra axioms. -/
structure BourbakiSigmaStructure (Ω : Type u) : Type u where
  carrier : Set (Set Ω)
  empty_mem : (∅ : Set Ω) ∈ carrier
  compl_mem : ∀ ⦃s : Set Ω⦄, s ∈ carrier → sᶜ ∈ carrier
  iUnion_mem : ∀ f : ℕ → Set Ω, (∀ n, f n ∈ carrier) → (⋃ n, f n) ∈ carrier

namespace BourbakiSigmaStructure

variable {Ω : Type u}

@[simp] theorem mem_carrier {τ : BourbakiSigmaStructure Ω} {s : Set Ω} :
    s ∈ τ.carrier ↔ s ∈ τ.carrier := Iff.rfl

end BourbakiSigmaStructure

/-- Helper predicate: a subset is measurable when it belongs to the σ-structure. -/
def BourbakiMeasurableSet {Ω : Type u} (τ : BourbakiSigmaStructure Ω)
    (s : Set Ω) : Prop := s ∈ τ.carrier

/-- Bourbaki-style morphisms: ordered pairs `(f, proof)` preserving measurability. -/
structure BourbakiMorphism {Ω₁ : Type u} {Ω₂ : Type v}
    (τ₁ : BourbakiSigmaStructure Ω₁) (τ₂ : BourbakiSigmaStructure Ω₂) : Type (max u v) where
  toFun : Ω₁ → Ω₂
  isMeasurable : ∀ ⦃s : Set Ω₂⦄, s ∈ τ₂.carrier → (preimage toFun s) ∈ τ₁.carrier

namespace BourbakiMorphism

section

variable {Ω₁ : Type u} {Ω₂ : Type v} {Ω₃ : Type w}
variable {τ₁ : BourbakiSigmaStructure Ω₁}
variable {τ₂ : BourbakiSigmaStructure Ω₂}
variable {τ₃ : BourbakiSigmaStructure Ω₃}

instance : CoeFun (BourbakiMorphism τ₁ τ₂) (fun _ => Ω₁ → Ω₂) where
  coe f := f.toFun

@[simp] lemma coe_mk (f : Ω₁ → Ω₂)
    (hf : ∀ ⦃s : Set Ω₂⦄, s ∈ τ₂.carrier → f ⁻¹' s ∈ τ₁.carrier) :
    ((BourbakiMorphism.mk f hf : BourbakiMorphism τ₁ τ₂) : Ω₁ → Ω₂) = f := rfl

/-- Identity morphism. -/
def id (τ : BourbakiSigmaStructure Ω₁) : BourbakiMorphism τ τ where
  toFun := fun x => x
  isMeasurable := by
    intro s hs
    simpa [Set.preimage_id] using hs

/-- Composition of Bourbaki morphisms. -/
def comp (g : BourbakiMorphism τ₂ τ₃) (f : BourbakiMorphism τ₁ τ₂) :
    BourbakiMorphism τ₁ τ₃ where
  toFun := g.toFun ∘ f.toFun
  isMeasurable := by
    intro s hs
    have hg : g ⁻¹' s ∈ τ₂.carrier := g.isMeasurable hs
    have hf₀ : f ⁻¹' (g ⁻¹' s) ∈ τ₁.carrier := f.isMeasurable hg
    have hf : (g.toFun ∘ f.toFun) ⁻¹' s ∈ τ₁.carrier := by
      simpa [Set.preimage_preimage, Function.comp] using hf₀
    exact hf

@[simp] lemma comp_toFun (g : BourbakiMorphism τ₂ τ₃)
    (f : BourbakiMorphism τ₁ τ₂) :
    (comp g f).toFun = g.toFun ∘ f.toFun := rfl

@[simp] lemma comp_apply (g : BourbakiMorphism τ₂ τ₃)
    (f : BourbakiMorphism τ₁ τ₂) (x : Ω₁) :
    comp g f x = g (f x) := rfl

/-- Composition remains a Bourbaki morphism (formal statement). -/
def bourbaki_morphism_comp (f : BourbakiMorphism τ₁ τ₂)
    (g : BourbakiMorphism τ₂ τ₃) : BourbakiMorphism τ₁ τ₃ :=
  comp g f

end

end BourbakiMorphism

/-- Convert a Bourbaki σ-structure into a Mathlib `MeasurableSpace`. -/
def toMeasurableSpace {Ω : Type u} (τ : BourbakiSigmaStructure Ω) :
    MeasurableSpace Ω where
  MeasurableSet' := fun s => s ∈ τ.carrier
  measurableSet_empty := τ.empty_mem
  measurableSet_compl := by intro s hs; exact τ.compl_mem hs
  measurableSet_iUnion := τ.iUnion_mem

@[simp] theorem measurableSet_toMeasurableSpace {Ω : Type u}
    (τ : BourbakiSigmaStructure Ω) {s : Set Ω} :
    @MeasurableSet Ω (toMeasurableSpace τ) s ↔ s ∈ τ.carrier := Iff.rfl

/-- Convert a Mathlib measurable space back into a Bourbaki σ-structure. -/
def ofMeasurableSpace {Ω : Type u} (m : MeasurableSpace Ω) :
    BourbakiSigmaStructure Ω where
  carrier := {s | @MeasurableSet Ω m s}
  empty_mem := (MeasurableSet.empty : @MeasurableSet Ω m ∅)
  compl_mem := by intro s hs; exact (MeasurableSet.compl hs)
  iUnion_mem := by intro f hf; exact (MeasurableSet.iUnion hf)

namespace BourbakiMorphism

section

variable {Ω₁ : Type u} {Ω₂ : Type v} {Ω₃ : Type w}
variable {τ₁ : BourbakiSigmaStructure Ω₁}
variable {τ₂ : BourbakiSigmaStructure Ω₂}
variable {τ₃ : BourbakiSigmaStructure Ω₃}

/-- A Bourbaki morphism induces a Mathlib measurable function. -/
theorem measurable_of_morphism (f : BourbakiMorphism τ₁ τ₂) :
    @Measurable Ω₁ Ω₂ (toMeasurableSpace τ₁) (toMeasurableSpace τ₂) f.toFun := by
  intro s hs
  have hs' : s ∈ τ₂.carrier :=
    (measurableSet_toMeasurableSpace (τ := τ₂) (s := s)).mp hs
  have hpre : f ⁻¹' s ∈ τ₁.carrier := f.isMeasurable hs'
  exact (measurableSet_toMeasurableSpace (τ := τ₁) (s := f ⁻¹' s)).mpr hpre

/-- Mathlib measurability yields a Bourbaki morphism between induced structures. -/
def ofMeasurable {Ω₁ : Type u} {Ω₂ : Type v}
    [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {f : Ω₁ → Ω₂} (hf : Measurable f) :
    BourbakiMorphism (ofMeasurableSpace m₁) (ofMeasurableSpace m₂) where
  toFun := f
  isMeasurable := by
    intro s hs
    exact hf hs

/-- Compatibility with Mathlib''s `Measurable.comp`. -/
theorem measurable_comp_mathlib
    {Ω₁ : Type u} {Ω₂ : Type v} {Ω₃ : Type w}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
    {f : Ω₁ → Ω₂} {g : Ω₂ → Ω₃}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (g ∘ f) :=
  Measurable.comp hg hf

/-- Composition remains measurable after translating to Mathlib. -/
theorem measurable_comp_of_morphisms (f : BourbakiMorphism τ₁ τ₂)
    (g : BourbakiMorphism τ₂ τ₃) :
    @Measurable Ω₁ Ω₃ (toMeasurableSpace τ₁) (toMeasurableSpace τ₃)
        (BourbakiMorphism.comp g f).toFun :=
  measurable_of_morphism (BourbakiMorphism.comp g f)

end

end BourbakiMorphism

section Examples

variable {Ω : Type u}

/-- Identity function is measurable in the Bourbaki model. -/
example (τ : BourbakiSigmaStructure Ω) :
    BourbakiMorphism τ τ :=
  BourbakiMorphism.id τ

/-- Constant functions are measurable in the Mathlib world, hence also Bourbaki. -/
example {Ω₁ : Type u} {Ω₂ : Type v} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    (c : Ω₂) :
    BourbakiMorphism (ofMeasurableSpace m₁) (ofMeasurableSpace m₂) := by
  refine BourbakiMorphism.ofMeasurable (Ω₁ := Ω₁) (Ω₂ := Ω₂)
      (m₁ := m₁) (m₂ := m₂) (f := fun _ : Ω₁ => c) ?_
  exact measurable_const

end Examples

end MeasureTheory
end BourbakiStyle
end MyProjects


