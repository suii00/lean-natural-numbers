/-
  Module     : MyProjects.BourbakiStyle.MeasureTheory.BorelBridge
  Overview   : Bridge B.md pattern B into Lean: Borel sigma-structures and continuity.
  Key defs   : borelSigmaStructure, continuous_implies_borel_measurable
  Example    : Identity map yields a Bourbaki morphism.
-/

import Mathlib.Topology.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Continuous
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import MyProjects.BourbakiStyle.MeasureTheory.MeasurableComposition

open Set

noncomputable section

namespace MyProjects
namespace BourbakiStyle
namespace MeasureTheory

universe u v

variable {Ω : Type u}

/-- Borel sigma-structure in the Bourbaki style, generated from a topological space. -/
def borelSigmaStructure (Ω : Type u) [TopologicalSpace Ω] :
    BourbakiSigmaStructure Ω :=
  ofMeasurableSpace (borel Ω)

@[simp] lemma mem_borelSigmaStructure {Ω : Type u} [TopologicalSpace Ω]
    {s : Set Ω} : s ∈ (borelSigmaStructure Ω).carrier ↔ @MeasurableSet Ω (borel Ω) s :=
  Iff.rfl

/-- Continuous maps between topological spaces become Bourbaki morphisms on Borel structures. -/
noncomputable def continuous_implies_borel_measurable
    {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) :
    BourbakiMorphism (borelSigmaStructure X) (borelSigmaStructure Y) :=
by
  classical
  let mX : MeasurableSpace X := borel X
  let mY : MeasurableSpace Y := borel Y
  have hf_meas : @Measurable X Y mX mY f := by
    simpa [mX, mY] using hf.borel_measurable
  refine BourbakiMorphism.ofMeasurable (Ω₁ := X) (Ω₂ := Y)
    (m₁ := mX) (m₂ := mY) (f := f) hf_meas

section Examples

/-- Continuous identity yields a Bourbaki morphism on Borel sigma-structures. -/
example {X : Type u} [TopologicalSpace X] :
    BourbakiMorphism (borelSigmaStructure X) (borelSigmaStructure X) :=
by
  simpa using
    continuous_implies_borel_measurable (X := X) (Y := X)
      (f := fun x : X => x) (hf := by simpa using continuous_id)

end Examples

end MeasureTheory
end BourbakiStyle
end MyProjects
