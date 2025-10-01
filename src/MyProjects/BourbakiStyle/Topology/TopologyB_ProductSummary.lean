/-
Topology B — Product and Exponential summaries

This module packages the key universal-property statements in a standalone
form, inspired by `TopologyB_Bourbaki2.lean` but without importing the archive
file. It emphasizes Bourbaki's ordered-pair viewpoint on products as well as
currying for spaces of continuous maps.

Sections
* `ProductUniversalSummary`: bundles continuity of projections, the
  componentwise continuity test, and the universal mediating map of products.
* `ExponentialSummary`: records the exponential homeomorphism and its
  β/η rules.

Two short examples at the end act as smoke tests mirroring the Bourbaki
intuition for ℝ.
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.Basic

namespace Bourbaki.TopologyB

open scoped Topology

/-! ### Product basics (ordered-pair viewpoint) -/

section ProductBasics

variable {T X Y : Type*}
variable [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace Y]

/-- First projection from a product, viewed as an ordered pair. -/
def π₁ : X × Y → X := fun p => p.1

/-- Second projection from a product, viewed as an ordered pair. -/
def π₂ : X × Y → Y := fun p => p.2

lemma continuous_π₁ : Continuous (π₁ : X × Y → X) := by
  simpa [π₁] using continuous_fst

lemma continuous_π₂ : Continuous (π₂ : X × Y → Y) := by
  simpa [π₂] using continuous_snd

/-- Continuity into a product is equivalent to continuity of the components. -/
theorem continuous_iff_proj (h : T → X × Y) :
    Continuous h ↔
      Continuous (fun t => (h t).1) ∧ Continuous (fun t => (h t).2) := by
  constructor
  · intro hh
    exact ⟨continuous_fst.comp hh, continuous_snd.comp hh⟩
  · rintro ⟨h₁, h₂⟩
    have : Continuous fun t => (h t).1 := h₁
    have : Continuous fun t => (h t).2 := h₂
    -- Assemble the mediating map via `Continuous.prodMk`.
    simpa using h₁.prodMk h₂

/--
Existence and uniqueness of the mediating map into a product: any two
continuous components assemble into a unique continuous map to `X × Y` whose
projections recover the components.
-/
theorem exists_unique_lift_to_prod {f : T → X} {g : T → Y}
    (hf : Continuous f) (hg : Continuous g) :
    ∃! h : T → X × Y,
      Continuous h ∧ (∀ t, (h t).1 = f t) ∧ (∀ t, (h t).2 = g t) := by
  refine ⟨fun t => (f t, g t), ?exist, ?uniq⟩
  · refine And.intro ?hcont ?hproj
    · simpa using hf.prodMk hg
    · exact ⟨fun t => rfl, fun t => rfl⟩
  · intro h hh
    rcases hh with ⟨_hc, hfst, hsnd⟩
    ext t <;> [simpa using hfst t, simpa using hsnd t]

end ProductBasics

/-! ### Exponential direction (currying for continuous maps) -/

section ExponentialBasics

variable {X Y Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Currying for plain functions. -/
def curry (f : X × Y → Z) : X → Y → Z := fun x y => f (x, y)

/-- Uncurrying for plain functions. -/
def uncurry (g : X → Y → Z) : X × Y → Z := fun p => g p.1 p.2

@[simp] lemma curry_uncurry (g : X → Y → Z) : curry (uncurry g) = g := rfl
@[simp] lemma uncurry_curry (f : X × Y → Z) : uncurry (curry f) = f := by
  funext p; cases p; rfl

variable [LocallyCompactSpace X] [LocallyCompactSpace Y]

/-- Exponential law as a homeomorphism between spaces of continuous maps. -/
noncomputable def exponential_homeo :
    ContinuousMap (X × Y) Z ≃ₜ ContinuousMap X (ContinuousMap Y Z) :=
  Homeomorph.curry (X:=X) (Y:=Y) (Z:=Z)

@[simp] lemma exponential_homeo_apply
    (F : ContinuousMap (X × Y) Z) (x : X) (y : Y) :
    exponential_homeo (X:=X) (Y:=Y) (Z:=Z) F x y = F (x, y) := rfl

@[simp] lemma exponential_homeo_symm_apply
    (G : ContinuousMap X (ContinuousMap Y Z)) (p : X × Y) :
    (exponential_homeo (X:=X) (Y:=Y) (Z:=Z)).symm G p = G p.1 p.2 := rfl

end ExponentialBasics

/-!
`ProductUniversalSummary` and `ExponentialSummary` collect these facts into
compact records that expose the Bourbaki-flavoured structure.
-/

structure ProductUniversalSummary (X Y : Type*)
    [TopologicalSpace X] [TopologicalSpace Y] where
  continuous_proj₁ : Continuous (π₁ : X × Y → X)
  continuous_proj₂ : Continuous (π₂ : X × Y → Y)
  continuous_iff :
    ∀ {T : Type*} [TopologicalSpace T] (h : T → X × Y),
      Continuous h ↔
        Continuous (fun t => (h t).1) ∧ Continuous (fun t => (h t).2)
  lift_exists_unique :
    ∀ {T : Type*} [TopologicalSpace T] {f : T → X} {g : T → Y},
      Continuous f → Continuous g →
        ∃! h : T → X × Y,
          Continuous h ∧ (∀ t, (h t).1 = f t) ∧ (∀ t, (h t).2 = g t)

noncomputable def productUniversalSummary (X Y : Type*)
    [TopologicalSpace X] [TopologicalSpace Y] :
    ProductUniversalSummary X Y :=
{ continuous_proj₁ := continuous_π₁ (X:=X) (Y:=Y)
, continuous_proj₂ := continuous_π₂ (X:=X) (Y:=Y)
, continuous_iff := by
    intro T _ h
    simpa using
      (continuous_iff_proj (T:=T) (X:=X) (Y:=Y) (h:=h))
, lift_exists_unique := by
    intro T _ f g hf hg
    simpa using
      (exists_unique_lift_to_prod (T:=T) (X:=X) (Y:=Y) (f:=f) (g:=g) hf hg)
}

structure ExponentialSummary (X Y Z : Type*)
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [LocallyCompactSpace X] [LocallyCompactSpace Y] where
  homeo : ContinuousMap (X × Y) Z ≃ₜ ContinuousMap X (ContinuousMap Y Z)
  apply_rule :
    ∀ (F : ContinuousMap (X × Y) Z) (x : X) (y : Y),
      homeo F x y = F (x, y)
  symm_apply_rule :
    ∀ (G : ContinuousMap X (ContinuousMap Y Z)) (p : X × Y),
      homeo.symm G p = G p.1 p.2

noncomputable def exponentialSummary (X Y Z : Type*)
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [LocallyCompactSpace X] [LocallyCompactSpace Y] :
    ExponentialSummary X Y Z :=
{ homeo := exponential_homeo (X:=X) (Y:=Y) (Z:=Z)
, apply_rule := by
    intro F x y
    simpa using
      (exponential_homeo_apply (X:=X) (Y:=Y) (Z:=Z) F x y)
, symm_apply_rule := by
    intro G p
    simpa using
      (exponential_homeo_symm_apply (X:=X) (Y:=Y) (Z:=Z) G p)
}

section Examples

open scoped Real

example : Continuous fun x : ℝ => (x, x) := by
  have h :=
    (productUniversalSummary (X:=ℝ) (Y:=ℝ)).continuous_iff (T:=ℝ)
      (h := fun x : ℝ => (x, x))
  exact (h).mpr ⟨continuous_id, continuous_id⟩

noncomputable example :
    (exponentialSummary (X:=ℝ) (Y:=ℝ) (Z:=ℝ)).homeo
        ⟨(fun xy : ℝ × ℝ => xy.1 + xy.2), by
          simpa using (continuous_fst.add continuous_snd)⟩ 2 3 = 5 := by
  have h :=
    (exponentialSummary (X:=ℝ) (Y:=ℝ) (Z:=ℝ)).apply_rule
      ⟨(fun xy : ℝ × ℝ => xy.1 + xy.2), by
        simpa using (continuous_fst.add continuous_snd)⟩ 2 3
  simpa using h

end Examples

end Bourbaki.TopologyB
