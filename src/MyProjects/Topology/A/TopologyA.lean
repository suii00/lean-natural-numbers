/-
  Topology A — Bourbaki-style structuration via ordered pairs and morphisms

  Source: src/MyProjects/Topology/A/claude_topologyA_en.md

  Implemented tracks (chosen):
  - A. Product universal property via projections (π₁, π₂)
  - B. Structural continuity theorems for ring homomorphisms

  Notes:
  - We reuse π₁, π₂ from `MyProjects.Topology.BourbakiProductAndHom` to keep projections unified.
  - Proofs emphasize composition with projections and structural morphisms.
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Instances.Real.Lemmas

-- Reuse Bourbaki projections and supporting lemmas
import MyProjects.Topology.BourbakiProductAndHom

namespace Bourbaki
open scoped Topology
open ContinuousMap

/-
  A. Product universal property
  Characterization: continuity into a product is equivalent to continuity of
  its components via the projections.
-/
section UniversalProperty

variable {X Y Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem product_universal_property (f : Z → X) (g : Z → Y) :
    Continuous (fun z => (f z, g z)) ↔ Continuous f ∧ Continuous g := by
  constructor
  · intro h
    exact ⟨continuous_fst.comp h, continuous_snd.comp h⟩
  · intro h
    rcases h with ⟨hf, hg⟩
    simpa using hf.prodMk hg

/-- Diagrammatic form: composing with projections yields continuous components. -/
lemma product_diagram_commutes (h : Z → X × Y) (hc : Continuous h) :
    Continuous (π₁ ∘ h) ∧ Continuous (π₂ ∘ h) := by
  constructor
  · simpa [Function.comp, π₁] using (continuous_fst.comp hc)
  · simpa [Function.comp, π₂] using (continuous_snd.comp hc)

/--
  Equivalence form: continuity into a product iff both projections are continuous.

  Usage pattern:
  - To split `Continuous h` into components, apply `.mp` to obtain
    `⟨Continuous (π₁ ∘ h), Continuous (π₂ ∘ h)⟩`.
  - To build `Continuous h` from component proofs, apply `.mpr` and finish with
    `hf.prodMk hg`.
-/
theorem continuous_iff_proj_continuous (h : Z → X × Y) :
    Continuous h ↔ Continuous (π₁ ∘ h) ∧ Continuous (π₂ ∘ h) := by
  constructor
  · intro hc
    exact product_diagram_commutes (X:=X) (Y:=Y) (Z:=Z) h hc
  · rintro ⟨h₁, h₂⟩
    have hc1 : Continuous fun z => (h z).1 := by
      simpa [Function.comp, π₁] using h₁
    have hc2 : Continuous fun z => (h z).2 := by
      simpa [Function.comp, π₂] using h₂
    simpa using hc1.prodMk hc2

end UniversalProperty

/-
  B. Structural theorems for continuous homomorphisms in topological rings
  If `f : R →+* S` is continuous, composition with continuous algebraic
  operations (addition, multiplication) yields continuous maps.
-/
section TopologicalRingHom

variable {R S : Type*}
variable [TopologicalSpace R] [Ring R] [IsTopologicalRing R]
variable [TopologicalSpace S] [Ring S]

theorem topological_ring_hom_continuous
    (f : R →+* S) (hf : Continuous f) :
    Continuous (fun r : R => f (r + r)) ∧
    Continuous (fun p : R × R => f (p.1 * p.2)) := by
  -- continuity of r ↦ r + r in a topological ring
  have h_add : Continuous fun r : R => r + r := by
    simpa using (continuous_id.add continuous_id)
  -- continuity of (p₁, p₂) ↦ p₁ * p₂ in a topological ring
  have h_mul : Continuous fun p : R × R => p.1 * p.2 := by
    simpa using (continuous_fst.mul continuous_snd)
  exact ⟨hf.comp h_add, hf.comp h_mul⟩

end TopologicalRingHom

/-
  C. Exponential law and evaluation continuity
  We use mathlib's compact-open topology results:
  - `Homeomorph.curry` yields `C(X × Y, Z) ≃ₜ C(X, C(Y, Z))` when `X, Y` are locally compact.
  - `ContinuousEval` instance gives continuity of evaluation when `(Y, Z)` is a locally compact pair.
-/
section Exponential

variable {X Y Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Exponential law: currying as a homeomorphism (requires local compactness of both factors). -/
noncomputable def exponential_law
    [LocallyCompactSpace X] [LocallyCompactSpace Y] :
    C(X × Y, Z) ≃ₜ C(X, C(Y, Z)) :=
  Homeomorph.curry (X:=X) (Y:=Y) (Z:=Z)

/-- `curry`/`uncurry` reduce on evaluation. -/
@[simp] lemma exponential_law_toEquiv_apply
    [LocallyCompactSpace X] [LocallyCompactSpace Y]
    (F : C(X × Y, Z)) (x : X) (y : Y) :
    (exponential_law (X:=X) (Y:=Y) (Z:=Z)).toEquiv F x y = F (x, y) := rfl

@[simp] lemma exponential_law_symm_toEquiv_apply
    [LocallyCompactSpace X] [LocallyCompactSpace Y]
    (G : C(X, C(Y, Z))) (p : X × Y) :
    (exponential_law (X:=X) (Y:=Y) (Z:=Z)).symm.toEquiv G p = G p.1 p.2 := rfl

/-- Coercion form of the β-rule: `exponential_law` as a bundled continuous map. -/
@[simp] lemma exponential_law_apply
    [LocallyCompactSpace X] [LocallyCompactSpace Y]
    (F : C(X × Y, Z)) (x : X) (y : Y) :
    (exponential_law (X:=X) (Y:=Y) (Z:=Z)) F x y = F (x, y) := rfl

/-- Coercion form of the β-rule for the inverse equivalence. -/
@[simp] lemma exponential_law_symm_apply
    [LocallyCompactSpace X] [LocallyCompactSpace Y]
    (G : C(X, C(Y, Z))) (p : X × Y) :
    (exponential_law (X:=X) (Y:=Y) (Z:=Z)).symm G p = G p.1 p.2 := rfl

/-- Continuity of the evaluation map `(f, y) ↦ f y` under the compact-open topology. -/
theorem continuous_eval
    [LocallyCompactPair Y Z] :
    Continuous (fun p : C(Y, Z) × Y => p.1 p.2) := by
  simpa using (ContinuousEval.continuous_eval :
    Continuous (fun p : C(Y, Z) × Y => p.1 p.2))

@[simp] lemma eval_apply (f : C(Y, Z)) (y : Y) :
    (fun p : C(Y, Z) × Y => p.1 p.2) (f, y) = f y := rfl

/--
  `prodMap` evaluates pointwise as expected; helpful for `simp` chains
  around precomposition on products.
-/
@[simp] lemma prodMap_apply {X' Y' : Type*}
    [TopologicalSpace X'] [TopologicalSpace Y']
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : C(X', X)) (ψ : C(Y', Y)) (x : X') (y : Y') :
    ContinuousMap.prodMap φ ψ (x, y) = (φ x, ψ y) := rfl

/-
  Partial evaluation: fixing one variable yields a continuous map in the other.
-/
lemma continuous_partial_right (F : C(X × Y, Z)) (y : Y) :
    Continuous (fun x : X => F (x, y)) := by
  have hx : Continuous fun x : X => (x, y) :=
    continuous_id.prodMk continuous_const
  exact F.continuous.comp hx

/-- Left partial evaluation: fixing the left variable preserves continuity. -/
lemma continuous_partial_left (F : C(X × Y, Z)) (x : X) :
    Continuous (fun y : Y => F (x, y)) := by
  have hy : Continuous fun y : Y => (x, y) :=
    continuous_const.prodMk continuous_id
  exact F.continuous.comp hy

/-
  Compatibility of currying with precomposition on the first variable.
-/
lemma curry_comp {X' : Type*} [TopologicalSpace X']
    [LocallyCompactSpace X] [LocallyCompactSpace X'] [LocallyCompactSpace Y]
    (φ : C(X', X)) (F : C(X × Y, Z)) :
    (exponential_law (X:=X') (Y:=Y) (Z:=Z)).toEquiv
        (F.comp (ContinuousMap.prodMap φ (ContinuousMap.id _)))
    = ((exponential_law (X:=X) (Y:=Y) (Z:=Z)).toEquiv F).comp φ := by
  ext x y; rfl

/--
  Pointwise form of “right-variable precomposition” through currying.
  This is often enough for rewriting inside larger goals with `simp`.
-/
@[simp] lemma curry_comp_right_apply {Y' : Type*}
    [TopologicalSpace Y']
    [LocallyCompactSpace X] [LocallyCompactSpace Y] [LocallyCompactSpace Y']
    (ψ : C(Y', Y)) (F : C(X × Y, Z)) (x : X) (y : Y') :
    ((exponential_law (X:=X) (Y:=Y') (Z:=Z)).toEquiv
        (F.comp (ContinuousMap.prodMap (ContinuousMap.id _) ψ)) x) y
    = ((exponential_law (X:=X) (Y:=Y) (Z:=Z)).toEquiv F x) (ψ y) := by
  -- both sides reduce by the β-rules and `comp_apply`/`prodMap_apply`
  simp

/-
  Bundled form of “right-variable precomposition” through currying.
  The right-hand side uses the canonical continuous precomposition map
  `ContinuousMap.compRightContinuousMap`.
-/
lemma curry_comp_right {Y' : Type*}
    [TopologicalSpace Y']
    [LocallyCompactSpace X] [LocallyCompactSpace Y] [LocallyCompactSpace Y']
    (ψ : C(Y', Y)) (F : C(X × Y, Z)) :
    (exponential_law (X:=X) (Y:=Y') (Z:=Z)).toEquiv
        (F.comp (ContinuousMap.prodMap (ContinuousMap.id _) ψ))
    = (ContinuousMap.compRightContinuousMap (X:=Y') (Y:=Y) (Z:=Z) ψ).comp
        ((exponential_law (X:=X) (Y:=Y) (Z:=Z)).toEquiv F) := by
  -- both sides are bundled maps `C(X, C(Y', Z))`; compare pointwise
  ext x y
  simp

end Exponential

section RealExamples
variable [LocallyCompactSpace ℝ]

-- Simple sanity checks on ℝ × ℝ
noncomputable example (F : C(ℝ × ℝ, ℝ)) (x y : ℝ) :
    (exponential_law (X:=ℝ) (Y:=ℝ) (Z:=ℝ)).toEquiv F x y = F (x, y) := by
  simp

noncomputable example (G : C(ℝ, C(ℝ, ℝ))) (p : ℝ × ℝ) :
    (exponential_law (X:=ℝ) (Y:=ℝ) (Z:=ℝ)).symm.toEquiv G p = G p.1 p.2 := by
  simp

example (F : C(ℝ × ℝ, ℝ)) (y : ℝ) :
    Continuous (fun x : ℝ => F (x, y)) := by
  simpa using (continuous_partial_right (X:=ℝ) (Y:=ℝ) (Z:=ℝ) F y)

end RealExamples

end Bourbaki
