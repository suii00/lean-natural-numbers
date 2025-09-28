/-
  Module     : MyProjects.BourbakiStyle.MeasureTheory.ExpectationBridge
  Overview   : Bridge D.md into Lean by packaging integrable random variables
               as Bourbaki-style ordered pairs and defining expectations.
  Key defs   : IntegrableRandomVariable, IntegrableRandomVariable.expectation,
               IntegrableRandomVariable.const
  Example    : Expectation of a constant Bourbaki random variable equals the constant.
-/
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import MyProjects.BourbakiStyle.MeasureTheory.BorelBridge
import MyProjects.BourbakiStyle.MeasureTheory.ProbabilityBridge

open MeasureTheory
open scoped MeasureTheory

noncomputable section

namespace MyProjects
namespace BourbakiStyle
namespace MeasureTheory

universe u

variable {Ω : Type u}

/--
A Bourbaki-style integrable random variable is an ordered pair consisting of a
random variable (a morphism toward a Borel σ-structure) together with the
structural proof of integrability with respect to a fixed measure.
-/
structure IntegrableRandomVariable (τΩ : BourbakiSigmaStructure Ω)
    (μ : @Measure Ω (toMeasurableSpace τΩ)) : Type u where
  toRandomVariable : RandomVariable τΩ ℝ
  integrable : Integrable (toRandomVariable : Ω → ℝ) μ

namespace IntegrableRandomVariable

variable {τΩ : BourbakiSigmaStructure Ω}
variable {μ : @Measure Ω (toMeasurableSpace τΩ)}

instance : CoeFun (IntegrableRandomVariable τΩ μ) (fun _ => Ω → ℝ) where
  coe ξ := ξ.toRandomVariable

@[simp] lemma coe_toRandomVariable (ξ : IntegrableRandomVariable τΩ μ) :
    (ξ.toRandomVariable : Ω → ℝ) = ξ := rfl

@[simp] lemma integrable_coe (ξ : IntegrableRandomVariable τΩ μ) :
    Integrable (ξ : Ω → ℝ) μ := by
  simpa using ξ.integrable

/-- Expectation of a Bourbaki integrable random variable. -/
noncomputable def expectation (ξ : IntegrableRandomVariable τΩ μ) : ℝ :=
  ∫ ω, ξ ω ∂μ

@[simp] lemma expectation_eq_integral
    (ξ : IntegrableRandomVariable τΩ μ) :
    expectation ξ = ∫ ω, ξ ω ∂μ := rfl

/--
Constant Bourbaki random variables become integrable whenever the underlying
measure is finite.
-/
noncomputable def const (τΩ : BourbakiSigmaStructure Ω)
    (μ : @Measure Ω (toMeasurableSpace τΩ)) [IsFiniteMeasure μ] (c : ℝ) :
    IntegrableRandomVariable τΩ μ :=
by
  classical
  refine ⟨⟨BourbakiMorphism.ofMeasurable (Ω₁ := Ω) (Ω₂ := ℝ)
    (m₁ := toMeasurableSpace τΩ) (m₂ := borel ℝ) (f := fun _ : Ω => c)
    (hf := by simpa using measurable_const)⟩, ?_⟩
  change Integrable (fun _ : Ω => c) μ
  simpa using (integrable_const (μ := μ) (c := c))

@[simp] lemma const_coe (c : ℝ) [IsFiniteMeasure μ] :
    (const (τΩ := τΩ) (μ := μ) c : Ω → ℝ) = fun _ => c := rfl

@[simp] lemma expectation_const (c : ℝ)
    [IsProbabilityMeasure μ] :
    expectation (const (τΩ := τΩ) (μ := μ) c) = c :=
by
  classical
  simpa [expectation, const_coe, measureReal_univ_eq_one (μ := μ), smul_eq_mul]
    using (integral_const (μ := μ) (α := Ω) (c := c))

@[simp] lemma expectation_zero [IsProbabilityMeasure μ] :
    expectation (const (τΩ := τΩ) (μ := μ) (0 : ℝ)) = 0 := by
  simpa using (expectation_const (τΩ := τΩ) (μ := μ) (c := (0 : ℝ)))

end IntegrableRandomVariable

section Examples

variable {τΩ : BourbakiSigmaStructure Ω}
variable {μ : @Measure Ω (toMeasurableSpace τΩ)}

open IntegrableRandomVariable

/-- Expectation of a constant Bourbaki random variable on a probability space. -/
example [IsProbabilityMeasure μ] (c : ℝ) :
    expectation (const (τΩ := τΩ) (μ := μ) c) = c :=
  expectation_const (τΩ := τΩ) (μ := μ) (c := c)

/-- Dirac probability measure yields the same constant expectation. -/
example (c : ℝ) :
    expectation (const (τΩ := borelSigmaStructure ℝ)
      (μ := (Measure.dirac (0 : ℝ))) c) = c := by
  classical
  have : IsProbabilityMeasure (Measure.dirac (0 : ℝ)) :=
    inferInstance
  simpa using (expectation_const (τΩ := borelSigmaStructure ℝ)
    (μ := (Measure.dirac (0 : ℝ))) (c := c))

end Examples

end MeasureTheory
end BourbakiStyle
end MyProjects
