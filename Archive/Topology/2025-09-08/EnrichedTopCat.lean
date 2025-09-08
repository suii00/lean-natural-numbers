/-
  Topology C — Track A (Enriched categories)

  Bourbaki-style: structure via ordered pairs and morphisms (projections),
  packaged as data on hom-sets and continuity of composition.

  This is a lightweight scaffold from src/MyProjects/Topology/C/claude.md.
  It states a record capturing “hom objects are topological spaces” and that
  composition is continuous, and postulates a tensor–internal-Hom adjunction.

  Notes
  - Keep the API minimal and free of project-local dependencies.
  - Replace `axiom` declarations with concrete constructions when ready.
-/

import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.Adjunction.Basic

set_option autoImplicit true

noncomputable section

namespace MyProjects.Topology.C.A

open scoped Topology
open CategoryTheory

/-
Enrichment data for `TopCat`:
• For objects `X Y : TopCat`, the hom-set is the space `C(X, Y)` with its
  compact–open topology (provided in mathlib).
• Composition is a continuous map from the product of hom spaces to a hom space.
-/
structure EnrichedTopCat where
  homSpace : ∀ (X Y : TopCat), TopologicalSpace (C(X, Y))
  /-- Composition continuity for compact-open hom spaces. Requires local compactness
      of the middle–target pair, in line with Bourbaki (Topologie, X§3, no.4). -/
  composition_continuous : ∀ {X Y Z : TopCat}, [LocallyCompactPair Y Z] →
    Continuous (fun p : C(Y, Z) × C(X, Y) => p.1.comp p.2)

/-
Tensor and internal-Hom functors on `TopCat` (postulated interface).
These objects express the spirit “morphisms determine structure”, allowing
adjunctions to be phrased purely via maps and their projection laws.
-/
/- Cartesian tensor: product with a fixed space. -/
def tensorWith (Y : TopCat) : TopCat ⥤ TopCat where
  obj X := TopCat.of (X × Y)
  map {X X'} (f : X ⟶ X') :=
    TopCat.ofHom ⟨
      (fun p : X × Y => (f.hom p.1, p.2)),
      (Continuous.prodMk (f.hom.continuous.comp continuous_fst) continuous_snd)⟩

/- Internal Hom functor: `X ↦ C(Y, X)` with compact–open topology.
   On morphisms, act by postcomposition. -/
def internalHom (Y : TopCat) : TopCat ⥤ TopCat where
  obj X := TopCat.of C(Y, X)
  map {X X'} (f : X ⟶ X') :=
    TopCat.ofHom ⟨
      (fun g : C(Y, X) => f.hom.comp g),
      by
        -- continuity of postcomposition in the compact–open topology
        simpa using
          (ContinuousMap.continuous_postcomp (X:=Y) (Y:=X) (Z:=X') (g:=f.hom))⟩

/-
Adjunction between “tensor with Y” and “internal Hom Y”.
Replace the axiom by a construction once the concrete tensor/internal-Hom
functors are chosen (e.g. product and `C(Y, ·)` under local compactness).
-/
/-
Local exponential law (hom-set equivalence) via currying. As Top is not
cartesian closed, this equivalence requires local compactness hypotheses.
We expose it as a concrete equivalence of hom-objects; packaging as a global
`Adjunction` would require restricting to a locally compact subcategory.
-/
def homEquiv_curry {X Y Z : TopCat} [LocallyCompactSpace X] [LocallyCompactSpace Y] :
    C(X × Y, Z) ≃ C(X, C(Y, Z)) :=
  (Homeomorph.curry (X:=X) (Y:=Y) (Z:=Z)).toEquiv

/-- Composition is continuous on hom spaces with respect to compact–open;
    this is obtained from `ContinuousMap.continuous_comp'` and symmetry of products. -/
lemma composition_continuous' {X Y Z : TopCat} [LocallyCompactPair Y Z] :
    Continuous (fun p : C(Y, Z) × C(X, Y) => p.1.comp p.2) := by
  -- mathlib has continuity for the swapped order `(C(X,Y) × C(Y,Z))`.
  have h : Continuous (fun q : C(X, Y) × C(Y, Z) => q.2.comp q.1) :=
    (ContinuousMap.continuous_comp' (X:=X) (Y:=Y) (Z:=Z))
  -- precompose with the product-commuting homeomorphism
  exact h.comp ((Homeomorph.prodComm (C(Y, Z)) (C(X, Y))).continuous_toFun)

/-!
Tensor–internal Hom adjunction (fixed locally compact `Y`).
We provide the hom-set equivalence using `curry/uncurry`, then package it as
an adjunction. We also add minimal `[simp]` lemmas for unit/counit.
-/

namespace TensorInternal

variable (Y : TopCat)

@[simp] lemma curry_apply {X Z : TopCat} (f : C(X × Y, Z)) (x : X) (y : Y) :
    ContinuousMap.curry (X:=X) (Y:=Y) (Z:=Z) f x y = f (x, y) := rfl

@[simp] lemma uncurry_apply {X Z : TopCat} [LocallyCompactSpace Y]
    (g : C(X, C(Y, Z))) (x : X) (y : Y) :
    ContinuousMap.uncurry (X:=X) (Y:=Y) (Z:=Z) g (x, y) = g x y := rfl

def homEquiv (X Z : TopCat) [LocallyCompactSpace Y] :
    ((tensorWith Y).obj X ⟶ Z) ≃ (X ⟶ (internalHom Y).obj Z) :=
  { toFun := fun h =>
      TopCat.ofHom (ContinuousMap.curry (X:=X) (Y:=Y) (Z:=Z) h.hom)
    , invFun := fun k =>
      TopCat.ofHom (ContinuousMap.uncurry (X:=X) (Y:=Y) (Z:=Z) k.hom)
    , left_inv := by
        intro h; apply TopCat.ext; intro p; cases p; rfl
    , right_inv := by
        intro k; apply TopCat.ext; intro x; apply ContinuousMap.ext; intro y; rfl }

def adjunction [LocallyCompactSpace Y] :
    CategoryTheory.Adjunction (tensorWith Y) (internalHom Y) := by
  classical
  refine CategoryTheory.Adjunction.mkOfHomEquiv ?data
  refine
    { homEquiv := fun X Z => homEquiv (Y:=Y) X Z
    , homEquiv_naturality_left_symm := ?nleft
    , homEquiv_naturality_right := ?nright }
  · intro X' X Z f h
    -- both sides are morphisms `(X' × Y) ⟶ Z`; compare on pairs.
    apply TopCat.ext; intro p; cases p with
    | _ => rfl
  · intro X Z Z' g h
    -- both sides are morphisms `X ⟶ C(Y, Z')`; compare by pointwise eval.
    apply TopCat.ext; intro x; apply ContinuousMap.ext; intro y; rfl

end TensorInternal

/-!  Unit/Counit evaluation forms (TopCat on the outside, LCH displayed on Hom).
These simplify evaluation to the expected `(x, y)` and `(f, y) ↦ f y` shapes.
This adjunction remains on `TopCat`; for LCH, we “display” hom-topology and
composition-continuity via `enrichedTopCat`. -/
-- TODO(unit/counit eval): Add `[simp]` evaluation rules for `unit.app` and
-- `counit.app` once we pin down a light-weight expansion path for
-- `Adjunction.mkOfHomEquiv`. For now, use the triangle lemmas below and the
-- `curry/uncurry` evaluation rules as needed.

/- Triangle identities as named simp-lemmas (reassoc). -/

/-!  Unit/Counit evaluation forms (TopCat on the outside, LCH displayed on Hom).
These simplify evaluation to the expected `(x, y)` and `(f, y) ↦ f y` shapes.
This adjunction remains on `TopCat`; for LCH, we “display” hom-topology and
composition-continuity via `enrichedTopCat`. -/
-- TODO: add explicit `[simp]` evaluation rules for unit/counit built via
-- `Adjunction.mkOfUnitCounit` (using `curry id` and `uncurry id`) to make
-- rewriting pointwise completely automatic across product notation.

/- Triangle identities as named simp-lemmas (reassoc). -/
section TriangleSimp

variable {Y : TopCat} [LocallyCompactSpace Y]

@[simp, reassoc]
lemma tensorInternal_triangle_left (X : TopCat) :
    ((tensorWith Y).map ((TensorInternal.adjunction (Y:=Y)).unit.app X)) ≫
      ((TensorInternal.adjunction (Y:=Y)).counit.app ((tensorWith Y).obj X))
    = 𝟙 ((tensorWith Y).obj X) := by
  simp

@[simp, reassoc]
lemma tensorInternal_triangle_right (Z : TopCat) :
    ((TensorInternal.adjunction (Y:=Y)).unit.app ((internalHom Y).obj Z)) ≫
      ((internalHom Y).map ((TensorInternal.adjunction (Y:=Y)).counit.app Z))
    = 𝟙 ((internalHom Y).obj Z) := by
  simp

end TriangleSimp

-- (Unit/counit simp) Optional: can be added on demand once more API is fixed.

/- Minimal compact–open naturality helpers (curry side). -/
section CompactOpenNaturality

variable {X X' Y Z W : Type*}
variable [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y]
variable [TopologicalSpace Z] [TopologicalSpace W]

@[simp] lemma curry_precomp_left_apply (f : C(X × Y, Z)) (φ : C(X', X))
    (x' : X') (y : Y) :
    ContinuousMap.curry (f.comp (ContinuousMap.prodMap φ (ContinuousMap.id _))) x' y
      = ContinuousMap.curry f (φ x') y := rfl

@[simp] lemma curry_postcomp_apply (f : C(X × Y, Z)) (ψ : C(Z, W)) (x : X) (y : Y) :
    ContinuousMap.curry (ψ.comp f) x y = ψ (ContinuousMap.curry f x y) := rfl

end CompactOpenNaturality

/- Package as an enrichment witness. -/
def enrichedTopCat : EnrichedTopCat where
  homSpace _ _ := by infer_instance
  composition_continuous := by
    intro X Y Z _
    simpa using composition_continuous' (X:=X) (Y:=Y) (Z:=Z)

end MyProjects.Topology.C.A


