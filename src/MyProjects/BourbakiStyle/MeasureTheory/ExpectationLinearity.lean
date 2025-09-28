/-
  Module     : MyProjects.BourbakiStyle.MeasureTheory.ExpectationLinearity
  Overview   : Translate E.md into Lean by installing linear operations on
               Bourbaki integrable random variables and proving expectation is
               linear over ℝ.
  Key defs   : BourbakiMorphism.ofMeasurable', IntegrableRandomVariable.smul,
               IntegrableRandomVariable.add, IntegrableRandomVariable.expectation_linear
  Example    : Expectation of a linear combination of Bourbaki constant random
               variables matches the expected scalar combination.
-/
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Continuous
import MyProjects.BourbakiStyle.MeasureTheory.ExpectationBridge

open MeasureTheory
open scoped MeasureTheory

noncomputable section

namespace MyProjects
namespace BourbakiStyle
namespace MeasureTheory

universe u

variable {Ω : Type u}

namespace BourbakiMorphism

/--
A measurable function between the Mathlib incarnations of two Bourbaki
σ-structures induces a Bourbaki morphism. This is the ordered-pair lift used to
build algebraic structure on random variables.
-/
noncomputable def ofMeasurable'
    {Ω₁ Ω₂ : Type*}
    (τ₁ : BourbakiSigmaStructure Ω₁) (τ₂ : BourbakiSigmaStructure Ω₂)
    {f : Ω₁ → Ω₂}
    (hf : @Measurable Ω₁ Ω₂ (toMeasurableSpace τ₁)
        (toMeasurableSpace τ₂) f) :
    BourbakiMorphism τ₁ τ₂ :=
by
  classical
  refine ⟨f, ?_⟩
  intro s hs
  have hs' :
      @MeasurableSet Ω₂ (toMeasurableSpace τ₂) s :=
    (measurableSet_toMeasurableSpace (τ := τ₂) (s := s)).mpr hs
  have hpre :
      @MeasurableSet Ω₁ (toMeasurableSpace τ₁) (f ⁻¹' s) := hf hs'
  exact (measurableSet_toMeasurableSpace (τ := τ₁)
      (s := f ⁻¹' s)).mp hpre

end BourbakiMorphism

namespace IntegrableRandomVariable

variable {τΩ : BourbakiSigmaStructure Ω}
variable {μ : @Measure Ω (toMeasurableSpace τΩ)}

/-- Scalar multiplication of Bourbaki integrable random variables. -/
noncomputable def smul (a : ℝ) (ξ : IntegrableRandomVariable τΩ μ) :
    IntegrableRandomVariable τΩ μ :=
by
  classical
  let _ : MeasurableSpace Ω := toMeasurableSpace τΩ
  have hξ : Measurable fun ω => ξ ω :=
    RandomVariable.measurable (τΩ := τΩ) (ξ := ξ.toRandomVariable)
  refine ⟨⟨BourbakiMorphism.ofMeasurable' τΩ (borelSigmaStructure ℝ)
    (f := fun ω => a * ξ ω)
    (hf := hξ.const_mul a)⟩, ?_⟩
  change Integrable (fun ω => a * ξ ω) μ
  simpa [Pi.smul_apply, smul_eq_mul] using (ξ.integrable_coe.smul a)

/-- Addition of Bourbaki integrable random variables. -/
noncomputable def add (ξ η : IntegrableRandomVariable τΩ μ) :
    IntegrableRandomVariable τΩ μ :=
by
  classical
  let _ : MeasurableSpace Ω := toMeasurableSpace τΩ
  have hξ : Measurable fun ω => ξ ω :=
    RandomVariable.measurable (τΩ := τΩ) (ξ := ξ.toRandomVariable)
  have hη : Measurable fun ω => η ω :=
    RandomVariable.measurable (τΩ := τΩ) (ξ := η.toRandomVariable)
  refine ⟨⟨BourbakiMorphism.ofMeasurable' τΩ (borelSigmaStructure ℝ)
    (f := fun ω => ξ ω + η ω)
    (hf := hξ.add hη)⟩, ?_⟩
  change Integrable (fun ω => ξ ω + η ω) μ
  simpa [Pi.add_apply] using (ξ.integrable_coe.add η.integrable_coe)

noncomputable instance instSMul : SMul ℝ (IntegrableRandomVariable τΩ μ) :=
  ⟨smul (τΩ := τΩ) (μ := μ)⟩

noncomputable instance instAdd : Add (IntegrableRandomVariable τΩ μ) :=
  ⟨add (τΩ := τΩ) (μ := μ)⟩

@[simp] lemma coe_smul_apply (a : ℝ) (ξ : IntegrableRandomVariable τΩ μ)
    (ω : Ω) :
    ((a • ξ : IntegrableRandomVariable τΩ μ) : Ω → ℝ) ω = a * ξ ω :=
by
  classical
  let _ : MeasurableSpace Ω := toMeasurableSpace τΩ
  simpa [coe_toRandomVariable]
    using (show ((a • ξ : IntegrableRandomVariable τΩ μ) : Ω → ℝ) ω
        = a * (ξ.toRandomVariable ω) from rfl)

@[simp] lemma coe_add_apply (ξ η : IntegrableRandomVariable τΩ μ)
    (ω : Ω) :
    ((ξ + η : IntegrableRandomVariable τΩ μ) : Ω → ℝ) ω = ξ ω + η ω :=
by
  classical
  let _ : MeasurableSpace Ω := toMeasurableSpace τΩ
  simpa [coe_toRandomVariable]
    using (show ((ξ + η : IntegrableRandomVariable τΩ μ) : Ω → ℝ) ω
        = ξ.toRandomVariable ω + η.toRandomVariable ω from rfl)

@[simp] lemma coe_smul (a : ℝ) (ξ : IntegrableRandomVariable τΩ μ) :
    ((a • ξ : IntegrableRandomVariable τΩ μ) : Ω → ℝ)
        = fun ω => a * ξ ω :=
by
  funext ω
  simpa using coe_smul_apply (τΩ := τΩ) (μ := μ) (a := a) (ξ := ξ) ω

@[simp] lemma coe_add (ξ η : IntegrableRandomVariable τΩ μ) :
    ((ξ + η : IntegrableRandomVariable τΩ μ) : Ω → ℝ)
        = fun ω => ξ ω + η ω :=
by
  funext ω
  simpa using coe_add_apply (τΩ := τΩ) (μ := μ) (ξ := ξ) (η := η) ω

lemma expectation_add (ξ η : IntegrableRandomVariable τΩ μ) :
    expectation (ξ + η) = expectation ξ + expectation η :=
by
  classical
  let _ : MeasurableSpace Ω := toMeasurableSpace τΩ
  simpa [expectation, coe_add, Pi.add_apply]
    using integral_add (ξ.integrable_coe) (η.integrable_coe)

lemma expectation_smul (a : ℝ) (ξ : IntegrableRandomVariable τΩ μ) :
    expectation (a • ξ) = a * expectation ξ :=
by
  classical
  let _ : MeasurableSpace Ω := toMeasurableSpace τΩ
  simpa [expectation, coe_smul, Pi.smul_apply, smul_eq_mul]
    using (integral_const_mul (μ := μ) (r := a) (f := fun ω => ξ ω))

lemma expectation_linear (ξ η : IntegrableRandomVariable τΩ μ)
    (a b : ℝ) :
    expectation (a • ξ + b • η)
        = a * expectation ξ + b * expectation η :=
by
  classical
  let _ : MeasurableSpace Ω := toMeasurableSpace τΩ
  have hξsmul : Integrable (fun ω => a * ξ ω) μ :=
    by simpa [Pi.smul_apply, smul_eq_mul] using (ξ.integrable_coe.smul a)
  have hηsmul : Integrable (fun ω => b * η ω) μ :=
    by simpa [Pi.smul_apply, smul_eq_mul] using (η.integrable_coe.smul b)
  have h_add :=
    integral_add (μ := μ) (hf := hξsmul) (hg := hηsmul)
  have hξint :=
    integral_const_mul (μ := μ) (r := a) (f := fun ω => ξ ω)
  have hηint :=
    integral_const_mul (μ := μ) (r := b) (f := fun ω => η ω)
  have hx : ∫ ω, a * ξ ω ∂μ = a * expectation ξ := by
    simpa [expectation] using hξint
  have hy : ∫ ω, b * η ω ∂μ = b * expectation η := by
    simpa [expectation] using hηint
  calc
    expectation (a • ξ + b • η)
        = ∫ ω, (a • ξ + b • η : IntegrableRandomVariable τΩ μ) ω ∂μ := rfl
    _ = ∫ ω, (a * ξ ω + b * η ω) ∂μ := by
      simp [coe_add, coe_smul, Pi.add_apply]
    _ = ∫ ω, a * ξ ω ∂μ + ∫ ω, b * η ω ∂μ := by
      simpa [coe_smul, Pi.smul_apply, smul_eq_mul, coe_add, Pi.add_apply]
        using h_add
    _ = a * expectation ξ + b * expectation η := by
      simpa [hx, hy]

end IntegrableRandomVariable

section Examples

variable {τΩ : BourbakiSigmaStructure Ω}
variable {μ : @Measure Ω (toMeasurableSpace τΩ)}

open IntegrableRandomVariable

/-- Expectation respects linear combinations of Bourbaki constant random variables. -/
example [IsProbabilityMeasure μ] (a b c d : ℝ) :
    expectation (a • const (τΩ := τΩ) (μ := μ) c
      + b • const (τΩ := τΩ) (μ := μ) d)
        = a * c + b * d :=
by
  classical
  simpa [expectation_linear]
    using (IntegrableRandomVariable.expectation_linear
      (τΩ := τΩ) (μ := μ)
      (ξ := const (τΩ := τΩ) (μ := μ) c)
      (η := const (τΩ := τΩ) (μ := μ) d)
      (a := a) (b := b))

end Examples

end MeasureTheory
end BourbakiStyle
end MyProjects

end
