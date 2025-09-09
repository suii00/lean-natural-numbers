-- Natural-in-X packaging for the compact–open exponential law, in `ContinuousMap`/`Homeomorph` land.
-- No TopCat mixing; pointwise `@[simp]` lemmas; proofs via `rfl`/`ext`.

import Mathlib.Topology.CompactOpen
import MyProjects.Topology.B.ExpLawCO

noncomputable section
open scoped Topology

namespace MyProjects.Topology.B

/-- A tiny "NatIso-like" record for a family of homeomorphisms natural in `X`.
We intentionally avoid `CategoryTheory.NatIso` to keep this independent of `TopCat`. -/
structure NatHomeoInX (Y Z : Type*)
    [TopologicalSpace Y] [TopologicalSpace Z] [LocallyCompactSpace Y] where
  app : ∀ (X : Type*) [TopologicalSpace X] [LocallyCompactSpace X],
    C(X × Y, Z) ≃ₜ C(X, C(Y, Z))

variable {X X' Y Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Z]
variable [LocallyCompactSpace X] [LocallyCompactSpace X'] [LocallyCompactSpace Y]

/-- A thin alias exposing the app as `expLawCO_natIso_X.app _`. -/
def expLawCO_natIso_X
  (Y Z : Type*) [TopologicalSpace Y] [TopologicalSpace Z] [LocallyCompactSpace Y] :
  NatHomeoInX Y Z :=
{ app := fun X _ _ => expLawCOHomeo (X:=X) (Y:=Y) (Z:=Z) }

-- Convenience simp lemmas (pointwise)

@[simp] lemma expLawCO_natIso_X_apply
  [TopologicalSpace X] [LocallyCompactSpace X]
  [TopologicalSpace Y] [LocallyCompactSpace Y] [TopologicalSpace Z]
  (f : C(X × Y, Z)) (x : X) (y : Y) :
  (expLawCO_natIso_X (Y:=Y) (Z:=Z)).app X f x y = f (x, y) := rfl

@[simp] lemma expLawCO_natIso_X_symm_apply
  [TopologicalSpace X] [LocallyCompactSpace X]
  [TopologicalSpace Y] [LocallyCompactSpace Y] [TopologicalSpace Z]
  (g : C(X, C(Y, Z))) (x : X) (y : Y) :
  ((expLawCO_natIso_X (Y:=Y) (Z:=Z)).app X).symm g (x, y) = g x y := rfl

/-- Naturality in `X` (precomposition) — pointwise form, `@[simp]` friendly. -/
@[simp] lemma expLawCO_natIso_X_precomp_left_apply
  [TopologicalSpace X] [TopologicalSpace X'] [LocallyCompactSpace X] [LocallyCompactSpace X']
  [TopologicalSpace Y] [LocallyCompactSpace Y] [TopologicalSpace Z]
  (φ : C(X', X)) (f : C(X × Y, Z)) (x' : X') (y : Y) :
  ((expLawCO_natIso_X (Y:=Y) (Z:=Z)).app X'
      (f.comp (ContinuousMap.prodMk (φ.comp ContinuousMap.fst) ContinuousMap.snd))) x' y
  =
  ((expLawCO_natIso_X (Y:=Y) (Z:=Z)).app X f) (φ x') y := by
  simpa using
    (expLawCO_precomp_left_apply (X:=X) (X':=X') (Y:=Y) (Z:=Z) φ f x' y)

namespace MyProjects.Topology.B

/-! # Y-naturality and Z-postcomposition (pointwise `@[simp]`)

These are pointwise forms derived from the `_apply` lemmas in `ExpLawCO.lean`.
They keep everything inside `ContinuousMap`/`Homeomorph` with `rfl`/`ext` proofs.
-/

@[simp] lemma expLawCO_natIso_X_precomp_right_apply
  {X Y Y' Z : Type*}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Y'] [TopologicalSpace Z]
  [LocallyCompactSpace X] [LocallyCompactSpace Y] [LocallyCompactSpace Y']
  (τ : C(Y', Y)) (f : C(X × Y, Z)) (x : X) (y' : Y') :
  ((expLawCO_natIso_X (Y:=Y') (Z:=Z)).app X
      (f.comp (ContinuousMap.prodMk ContinuousMap.fst (τ.comp ContinuousMap.snd)))) x y'
  =
  ((expLawCO_natIso_X (Y:=Y) (Z:=Z)).app X f) x (τ y') := by
  simpa using
    (expLawCO_precomp_right_apply (X:=X) (Y:=Y) (Y':=Y') (Z:=Z) τ f x y')

@[simp] lemma expLawCO_natIso_X_postcomp_apply
  {X Y Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace Z']
  [LocallyCompactSpace X] [LocallyCompactSpace Y]
  (ψ : C(Z, Z')) (f : C(X × Y, Z)) (x : X) (y : Y) :
  ((expLawCO_natIso_X (Y:=Y) (Z:=Z')).app X (ψ.comp f)) x y
  =
  ψ (((expLawCO_natIso_X (Y:=Y) (Z:=Z)).app X f) x y) := by
  simpa using
    (expLawCO_postcomp_apply (X:=X) (Y:=Y) (Z:=Z) (Z':=Z') ψ f x y)

end MyProjects.Topology.B

-- Symmetric packaging: Y‑naturality as a tiny record

noncomputable section
open scoped Topology

namespace MyProjects.Topology.B

/-- A tiny "NatIso-like" record for a family of homeomorphisms natural in `Y`.
We intentionally avoid category-theoretic packaging to keep this in
`ContinuousMap`/`Homeomorph` land. -/
structure NatHomeoInY (X Z : Type*)
    [TopologicalSpace X] [TopologicalSpace Z] [LocallyCompactSpace X] where
  app : ∀ (Y : Type*) [TopologicalSpace Y] [LocallyCompactSpace Y],
    C(X × Y, Z) ≃ₜ C(X, C(Y, Z))

/-- Canonical natural family: `Y ↦ expLawCOHomeo (X, Y, Z)`. -/
def expLawCO_natIso_Y
  (X Z : Type*) [TopologicalSpace X] [TopologicalSpace Z] [LocallyCompactSpace X] :
  NatHomeoInY X Z :=
{ app := fun Y _ _ => expLawCOHomeo (X:=X) (Y:=Y) (Z:=Z) }

-- convenience simp lemmas (pointwise)

@[simp] lemma expLawCO_natIso_Y_apply
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [LocallyCompactSpace X] [LocallyCompactSpace Y]
  (f : C(X × Y, Z)) (x : X) (y : Y) :
  (expLawCO_natIso_Y (X:=X) (Z:=Z)).app Y f x y = f (x, y) := rfl

@[simp] lemma expLawCO_natIso_Y_symm_apply
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [LocallyCompactSpace X] [LocallyCompactSpace Y]
  (g : C(X, C(Y, Z))) (x : X) (y : Y) :
  ((expLawCO_natIso_Y (X:=X) (Z:=Z)).app Y).symm g (x, y) = g x y := rfl

/-- Y‑naturality (inner precomposition), pointwise form. -/
@[simp] lemma expLawCO_natIso_Y_precomp_right_apply
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Y'] [TopologicalSpace Z]
  [LocallyCompactSpace X] [LocallyCompactSpace Y] [LocallyCompactSpace Y']
  (τ : C(Y', Y)) (f : C(X × Y, Z)) (x : X) (y' : Y') :
  ((expLawCO_natIso_Y (X:=X) (Z:=Z)).app Y'
      (f.comp (ContinuousMap.prodMk ContinuousMap.fst (τ.comp ContinuousMap.snd)))) x y'
  =
  ((expLawCO_natIso_Y (X:=X) (Z:=Z)).app Y f) x (τ y') := by
  simpa using
    (expLawCO_precomp_right_apply (X:=X) (Y:=Y) (Y':=Y') (Z:=Z) τ f x y')

end MyProjects.Topology.B
