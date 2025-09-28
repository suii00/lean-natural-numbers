/-
  Module     : MyProjects.BourbakiStyle.Topology.ContinuousComposition
  Overview   : Bourbaki-style topological structures and continuous morphisms
  Reference  : Nicolas Bourbaki, Éléments de mathématique

  We package open-set data as ordered pairs and view continuous morphisms as
  arrows whose components are functions together with structure-preserving
  proofs. Composition inherits continuity, parallel to Mathlib's `Continuous.comp`.
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Continuous

open Set

namespace MyProjects
namespace BourbakiStyle
namespace Topology

universe u v w

/-- Bourbaki-style topology: a family of subsets closed under the topology axioms. -/
structure BourbakiTopology (X : Type u) : Type u where
  carrier : Set (Set X)
  empty_mem : (∅ : Set X) ∈ carrier
  univ_mem : (Set.univ : Set X) ∈ carrier
  inter_mem : ∀ ⦃U V : Set X⦄, U ∈ carrier → V ∈ carrier → (U ∩ V) ∈ carrier
  sUnion_mem : ∀ 𝒰 : Set (Set X), 𝒰 ⊆ carrier → ⋃₀ 𝒰 ∈ carrier

namespace BourbakiTopology

variable {X : Type u}

@[simp] theorem mem_carrier {τ : BourbakiTopology X} {U : Set X} :
    U ∈ τ.carrier ↔ U ∈ τ.carrier := Iff.rfl

/-- Predicate expressing that a set is Bourbaki-open. -/
def IsOpen (τ : BourbakiTopology X) (U : Set X) : Prop :=
  U ∈ τ.carrier

@[simp] lemma isOpen_iff {τ : BourbakiTopology X} {U : Set X} :
    IsOpen τ U ↔ U ∈ τ.carrier := Iff.rfl

end BourbakiTopology

/-- Bourbaki-style morphisms: ordered pairs `(f, proof)` preserving openness. -/
structure BourbakiMorphism {X : Type u} {Y : Type v}
    (τX : BourbakiTopology X) (τY : BourbakiTopology Y) : Type (max u v) where
  toFun : X → Y
  isContinuous : ∀ ⦃U : Set Y⦄, U ∈ τY.carrier → (preimage toFun U) ∈ τX.carrier


namespace BourbakiMorphism

section

variable {X : Type u} {Y : Type v} {Z : Type w}
variable {τX : BourbakiTopology X}
variable {τY : BourbakiTopology Y}
variable {τZ : BourbakiTopology Z}

instance : CoeFun (BourbakiMorphism τX τY) (fun _ => X → Y) where
  coe f := f.toFun

@[simp] lemma coe_mk (f : X → Y)
    (hf : ∀ ⦃U : Set Y⦄, U ∈ τY.carrier → f ⁻¹' U ∈ τX.carrier) :
    ((BourbakiMorphism.mk f hf : BourbakiMorphism τX τY) : X → Y) = f := rfl

/-- Identity morphism in the Bourbaki category of topological spaces. -/
def id (τ : BourbakiTopology X) : BourbakiMorphism τ τ where
  toFun := fun x => x
  isContinuous := by
    intro U hU
    simpa [Set.preimage_id] using hU

/-- Composition of Bourbaki morphisms. -/
def comp (g : BourbakiMorphism τY τZ) (f : BourbakiMorphism τX τY) :
    BourbakiMorphism τX τZ where
  toFun := g.toFun ∘ f.toFun
  isContinuous := by
    intro U hU
    have hg : g ⁻¹' U ∈ τY.carrier := g.isContinuous hU
    have hf : f ⁻¹' (g ⁻¹' U) ∈ τX.carrier := f.isContinuous hg
    simpa [Set.preimage_preimage, Function.comp] using hf

@[simp] lemma comp_toFun (g : BourbakiMorphism τY τZ)
    (f : BourbakiMorphism τX τY) :
    (comp g f).toFun = g.toFun ∘ f.toFun := rfl

@[simp] lemma comp_apply (g : BourbakiMorphism τY τZ)
    (f : BourbakiMorphism τX τY) (x : X) :
    comp g f x = g (f x) := rfl

/-- Rebranded composition to highlight ordered-pair morphisms. -/
def bourbaki_morphism_comp (f : BourbakiMorphism τX τY)
    (g : BourbakiMorphism τY τZ) : BourbakiMorphism τX τZ :=
  comp g f

end

end BourbakiMorphism

/-- Convert a Bourbaki topology into Mathlib's `TopologicalSpace`. -/
def toTopologicalSpace {X : Type u} (τ : BourbakiTopology X) : TopologicalSpace X where
  IsOpen := fun U => U ∈ τ.carrier
  isOpen_univ := τ.univ_mem
  isOpen_inter := by
    intro U V hU hV
    simpa using τ.inter_mem hU hV
  isOpen_sUnion := by
    intro 𝒰 h𝒰
    refine τ.sUnion_mem 𝒰 ?_
    intro U hU
    exact h𝒰 U hU

@[simp] theorem isOpen_toTopologicalSpace {X : Type u}
    (τ : BourbakiTopology X) {U : Set X} :
    @IsOpen X (toTopologicalSpace τ) U ↔ U ∈ τ.carrier := Iff.rfl

/-- Convert a Mathlib `TopologicalSpace` back into a Bourbaki topology. -/
def ofTopologicalSpace {X : Type u} (t : TopologicalSpace X) : BourbakiTopology X := by
  classical
  refine
    { carrier := {U : Set X | t.IsOpen U}
      empty_mem := ?_
      univ_mem := by simpa using t.isOpen_univ
      inter_mem := by
        intro U V hU hV
        simpa using t.isOpen_inter U V hU hV
      sUnion_mem := by
        intro 𝒰 h𝒰
        have h' : ∀ U ∈ 𝒰, t.IsOpen U := by
          intro U hU
          exact h𝒰 hU
        simpa using t.isOpen_sUnion 𝒰 h' }
  have h := t.isOpen_sUnion (s := (∅ : Set (Set X))) (by intro U hU; cases hU)
  simpa [Set.sUnion_empty] using h

namespace BourbakiTopology

variable {X : Type u}

@[simp] lemma of_toTopologicalSpace (τ : BourbakiTopology X) :
    ofTopologicalSpace (toTopologicalSpace τ) = τ := by
  classical
  cases τ with
  | mk carrier empty_mem univ_mem inter_mem sUnion_mem =>
      simp [toTopologicalSpace, ofTopologicalSpace]

end BourbakiTopology

@[simp] lemma to_ofTopologicalSpace {X : Type u}
    (t : TopologicalSpace X) :
    toTopologicalSpace (ofTopologicalSpace t) = t := by
  classical
  ext U
  rfl

namespace BourbakiMorphism

section

variable {X : Type u} {Y : Type v} {Z : Type w}
variable {τX : BourbakiTopology X}
variable {τY : BourbakiTopology Y}
variable {τZ : BourbakiTopology Z}

/-- A Bourbaki morphism is continuous for the induced Mathlib topology. -/
theorem continuous_of_morphism (f : BourbakiMorphism τX τY) :
    @Continuous X Y (toTopologicalSpace τX) (toTopologicalSpace τY) f.toFun := by
  classical
  let _ : TopologicalSpace X := toTopologicalSpace τX
  let _ : TopologicalSpace Y := toTopologicalSpace τY
  refine (continuous_def.mpr ?_)
  intro U hU
  have hU' : U ∈ τY.carrier :=
    (isOpen_toTopologicalSpace (τ := τY) (U := U)).mp hU
  have : f ⁻¹' U ∈ τX.carrier := f.isContinuous hU'
  exact (isOpen_toTopologicalSpace (τ := τX) (U := f ⁻¹' U)).mpr this

/-- Mathlib continuity yields a Bourbaki morphism between induced structures. -/
def ofContinuous {X : Type u} {Y : Type v}
    [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) :
    BourbakiMorphism (ofTopologicalSpace tX) (ofTopologicalSpace tY) where
  toFun := f
  isContinuous := by
    intro U hU
    have hf' := (continuous_def.mp hf)
    change tX.IsOpen (f ⁻¹' U)
    simpa using hf' U hU

/-- Compatibility with Mathlib's `Continuous.comp`. -/
theorem continuous_comp_mathlib
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} {g : Y → Z}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (g ∘ f) :=
  by
    simpa [Function.comp] using hg.comp hf

/-- Composition remains continuous after translating to Mathlib. -/
theorem continuous_comp_of_morphisms (f : BourbakiMorphism τX τY)
    (g : BourbakiMorphism τY τZ) :
    @Continuous X Z (toTopologicalSpace τX) (toTopologicalSpace τZ)
        (BourbakiMorphism.comp g f).toFun :=
  continuous_of_morphism (BourbakiMorphism.comp g f)

end

end BourbakiMorphism

section Examples

variable {X : Type u}

/-- Identity morphism is continuous in the Bourbaki model. -/
example (τ : BourbakiTopology X) :
    BourbakiMorphism τ τ :=
  BourbakiMorphism.id τ

/-- Constant functions are continuous in Mathlib and hence Bourbaki. -/
example {X : Type u} {Y : Type v} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    (y₀ : Y) :
    BourbakiMorphism (ofTopologicalSpace tX) (ofTopologicalSpace tY) := by
  refine BourbakiMorphism.ofContinuous (X := X) (Y := Y)
      (tX := tX) (tY := tY) (f := fun _ : X => y₀) ?_
  exact continuous_const

end Examples

end Topology
end BourbakiStyle
end MyProjects
