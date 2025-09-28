/-
  Module     : MyProjects.BourbakiStyle.MeasureTheory.ProbabilityBridge
  Overview   : Bridge C.md pattern B into Lean: random variables as Bourbaki morphisms
               and distributions as pushforward measures.
  Key defs   : RandomVariable, RandomVariable.compContinuous, distribution
  Example    : Identity random variable preserves the underlying probability measure.
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Basic
import Mathlib.Topology.Continuous
import Mathlib.MeasureTheory.Measure.Map
import MyProjects.BourbakiStyle.MeasureTheory.BorelBridge
import MyProjects.BourbakiStyle.MeasureTheory.MeasurableComposition

open MeasureTheory
open scoped MeasureTheory

noncomputable section

namespace MyProjects
namespace BourbakiStyle
namespace MeasureTheory

universe u v w

variable {Ω : Type u}

@[simp] lemma toMeasurableSpace_ofMeasurableSpace
    (m : MeasurableSpace Ω) :
    toMeasurableSpace (ofMeasurableSpace m) = m := by
  ext s; rfl

@[simp] lemma toMeasurableSpace_borelSigmaStructure (X : Type v)
    [TopologicalSpace X] :
    toMeasurableSpace (borelSigmaStructure X) = borel X := by
  simpa [borelSigmaStructure, toMeasurableSpace_ofMeasurableSpace]

/-- Bourbaki-style random variables: measurable maps into Borel sigma-structures. -/
structure RandomVariable (τΩ : BourbakiSigmaStructure Ω)
    (X : Type v) [TopologicalSpace X] : Type (max u v) where
  toMorphism : BourbakiMorphism τΩ (borelSigmaStructure X)

namespace RandomVariable

variable {τΩ : BourbakiSigmaStructure Ω}
variable {X : Type v} [TopologicalSpace X]

instance : CoeFun (RandomVariable τΩ X) (fun _ => Ω → X) where
  coe ξ := ξ.toMorphism

@[simp] lemma coe_toMorphism (ξ : RandomVariable τΩ X) :
    (ξ.toMorphism : Ω → X) = ξ := rfl

/-- Random variables are measurable in the Mathlib sense. -/
lemma measurable (ξ : RandomVariable τΩ X) :
    @Measurable Ω X (toMeasurableSpace τΩ) (borel X) ξ := by
  classical
  let _ : MeasurableSpace Ω := toMeasurableSpace τΩ
  let _ : MeasurableSpace X := toMeasurableSpace (borelSigmaStructure X)
  simpa [coe_toMorphism, toMeasurableSpace_borelSigmaStructure]
    using BourbakiMorphism.measurable_of_morphism ξ.toMorphism

/-- A continuous post-composition of a random variable remains a random variable. -/
noncomputable def compContinuous {Y : Type w} [TopologicalSpace Y]
    (ξ : RandomVariable τΩ X) {g : X → Y} (hg : Continuous g) :
    RandomVariable τΩ Y :=
  ⟨BourbakiMorphism.comp
      (continuous_implies_borel_measurable (f := g) hg)
      ξ.toMorphism⟩

@[simp] lemma compContinuous_coe {Y : Type w} [TopologicalSpace Y]
    (ξ : RandomVariable τΩ X) {g : X → Y} (hg : Continuous g) :
    (ξ.compContinuous hg : Ω → Y) = g ∘ ξ := rfl

end RandomVariable

/-- Distribution of a random variable: pushforward of a measure along its function. -/
noncomputable def distribution {τΩ : BourbakiSigmaStructure Ω}
    {X : Type v} [TopologicalSpace X]
    (μ : @Measure Ω (toMeasurableSpace τΩ))
    (ξ : RandomVariable τΩ X) : @Measure X (borel X) :=
by
  classical
  let _ : MeasurableSpace Ω := toMeasurableSpace τΩ
  let _ : MeasurableSpace X := borel X
  simpa using Measure.map ξ μ

/-- Pushing forward a probability measure along a random variable yields a probability measure. -/
lemma distribution_isProbability {τΩ : BourbakiSigmaStructure Ω}
    {X : Type v} [TopologicalSpace X]
    (μ : @Measure Ω (toMeasurableSpace τΩ)) [IsProbabilityMeasure μ]
    (ξ : RandomVariable τΩ X) :
    IsProbabilityMeasure (distribution μ ξ) :=
by
  classical
  let _ : MeasurableSpace Ω := toMeasurableSpace τΩ
  let _ : MeasurableSpace X := borel X
  have hξ : AEMeasurable ξ μ := (RandomVariable.measurable (τΩ := τΩ) (ξ := ξ)).aemeasurable
  simpa [distribution] using isProbabilityMeasure_map (μ := μ) (f := ξ) hξ

/-- Continuous transformations of random variables act on distributions by pushforward. -/
lemma distribution_compContinuous {τΩ : BourbakiSigmaStructure Ω}
    {X : Type v} [TopologicalSpace X]
    {Y : Type w} [TopologicalSpace Y]
    (μ : @Measure Ω (toMeasurableSpace τΩ)) (ξ : RandomVariable τΩ X)
    {g : X → Y} (hg : Continuous g) :
    distribution μ (RandomVariable.compContinuous ξ hg) =
      @Measure.map X Y (borel X) (borel Y) g (distribution μ ξ) :=
by
  classical
  let _ : MeasurableSpace Ω := toMeasurableSpace τΩ
  let _ : MeasurableSpace X := borel X
  let _ : MeasurableSpace Y := borel Y
  have hξ : Measurable ξ := RandomVariable.measurable ξ
  have hg' : Measurable g := by
    simpa [toMeasurableSpace_borelSigmaStructure]
      using hg.borel_measurable
  have h_left : distribution μ (RandomVariable.compContinuous ξ hg)
        = Measure.map (g ∘ ξ) μ := by
    simp [distribution, RandomVariable.compContinuous_coe]
  have h_right : @Measure.map X Y (borel X) (borel Y) g (distribution μ ξ)
        = Measure.map (g ∘ ξ) μ := by
    simpa [distribution] using (Measure.map_map (μ := μ) hg' hξ)
  exact h_left.trans h_right.symm

section Examples

variable {X : Type v} [TopologicalSpace X]

/-- Identity map viewed as a random variable preserves the original measure. -/
example (μ : @Measure X (toMeasurableSpace (borelSigmaStructure X))) :
    distribution (τΩ := borelSigmaStructure X) μ
        (RandomVariable.mk (τΩ := borelSigmaStructure X)
          (X := X)
          (BourbakiMorphism.id (τ := borelSigmaStructure X))) = μ := by
  classical
  let _ : MeasurableSpace X := borel X
  calc
    distribution (τΩ := borelSigmaStructure X) μ
        (RandomVariable.mk (τΩ := borelSigmaStructure X)
          (X := X)
          (BourbakiMorphism.id (τ := borelSigmaStructure X)))
          = Measure.map (fun x : X => x) μ := by
      simp [distribution, BourbakiMorphism.id]
    _ = μ := by
      simpa using Measure.map_id (μ := μ)

end Examples

end MeasureTheory
end BourbakiStyle
end MyProjects

end
