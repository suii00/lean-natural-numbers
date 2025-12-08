/-
Advanced analysis statements collected in the spirit of Bourbaki.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Module.HahnBanach
import MyProjects.Set.Bourbaki_Lean_Guide

open scoped BigOperators ENNReal Topology
open Filter MeasureTheory Set

namespace Bourbaki
namespace Analysis

/-!
## Section 1: sigma-algebras and measures
-/
section SigmaAlgebra

variable {α : Type*} [MeasurableSpace α]

/-- Countable unions of measurable sets indexed by ℕ are measurable. -/
lemma measurable_iUnion_structural {s : ℕ → Set α} (hs : ∀ n, MeasurableSet (s n)) :
    MeasurableSet (⋃ n, s n) := by
  classical
  simpa using MeasurableSet.iUnion hs

/-- A measure is σ-additive on pairwise disjoint measurable families indexed by ℕ. -/
lemma measure_iUnion_structural {μ : Measure α}
    {s : ℕ → Set α} (hs : ∀ n, MeasurableSet (s n))
    (hdisj : Pairwise fun m n => Disjoint (s m) (s n)) :
    μ (⋃ n, s n) = ∑' n, μ (s n) := by
  classical
  simpa using MeasureTheory.measure_iUnion hdisj hs

end SigmaAlgebra

/-!
## Section 2: integration principles
-/
section Integration

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Monotone convergence for non-negative measurable functions. -/
lemma monotone_convergence_lintegral {f : ℕ → α → ℝ≥0∞}
    (hf : ∀ n, Measurable (f n)) (hmono : Monotone f) :
    ∫⁻ x, ⨆ n, f n x ∂μ = ⨆ n, ∫⁻ x, f n x ∂μ := by
  simpa using MeasureTheory.lintegral_iSup (μ := μ) hf hmono

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The dominated convergence theorem (sequence version). -/
lemma dominated_convergence_integral {F : ℕ → α → G} {f : α → G} {bound : α → ℝ}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hbound : Integrable bound μ)
    (hdom : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  simpa using
    MeasureTheory.tendsto_integral_of_dominated_convergence (μ := μ)
      (F := F) (f := f) (bound := bound) hF hbound hdom hlim

end Integration

/-!
## Section 3: L^p geometry
-/
section LpGeometry

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- Holder's inequality for non-negative measurable functions. -/
lemma holder_inequality_nnreal {p q : ℝ} {f g : α → ℝ≥0∞}
    (hpq : p.HolderConjugate q) (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, (f x * g x) ∂μ) ≤
      (∫⁻ x, f x ^ p ∂μ) ^ (1 / p) * (∫⁻ x, g x ^ q ∂μ) ^ (1 / q) := by
  simpa using ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := μ) hpq hf hg

/-- Minkowski's inequality for L^p-seminorms with exponent p ≥ 1. -/
lemma minkowski_inequality_nnreal {p : ℝ} {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hp : 1 ≤ p) :
    (∫⁻ x, (f x + g x) ^ p ∂μ) ^ (1 / p) ≤
      (∫⁻ x, f x ^ p ∂μ) ^ (1 / p) + (∫⁻ x, g x ^ p ∂μ) ^ (1 / p) := by
  simpa using ENNReal.lintegral_Lp_add_le (μ := μ) hf hg hp

end LpGeometry

/-!
## Section 4: functional analysis
-/
section FunctionalAnalysis

variable {ι E F 𝕜 𝕜₂ : Type*}
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F]
  {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂] [CompleteSpace E]

/-- The uniform boundedness principle (Banach-Steinhaus). -/
lemma uniform_boundedness_principle (g : ι → E →SL[σ₁₂] F)
    (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) : ∃ C', ∀ i, ‖g i‖ ≤ C' := by
  classical
  simpa using (_root_.banach_steinhaus (g := g) h)

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Hahn-Banach extension preserving the operator norm. -/
lemma hahn_banach_extension_norm_eq (p : Subspace ℝ E) (f : p →L[ℝ] ℝ) :
    ∃ g : E →L[ℝ] ℝ, (∀ x : p, g x = f x) ∧ ‖g‖ = ‖f‖ :=
  Real.exists_extension_norm_eq p f

end FunctionalAnalysis

/-!
## Example: Holder for constant functions
-/
section Examples

variable {α : Type*} [MeasurableSpace α]

example (μ : Measure α) :
    (∫⁻ x, (1 : α → ℝ≥0∞) x * (1 : α → ℝ≥0∞) x ∂μ) ≤
      (∫⁻ x, (1 : α → ℝ≥0∞) x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫⁻ x, (1 : α → ℝ≥0∞) x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
  have h_const : AEMeasurable (fun _ : α => (1 : ℝ≥0∞)) μ :=
    (measurable_const : Measurable fun _ : α => (1 : ℝ≥0∞)).aemeasurable
  have h_conj : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  simpa using holder_inequality_nnreal (μ := μ)
    (p := (2 : ℝ)) (q := (2 : ℝ)) h_conj h_const h_const

end Examples

end Analysis
end Bourbaki
