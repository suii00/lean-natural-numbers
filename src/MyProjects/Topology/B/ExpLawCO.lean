-- Exponential law (compact–open) at Homeomorph level, with pointwise `@[simp]`.
-- Snapshot-friendly: all key lemmas are `rfl` on applications.

import Mathlib.Topology.CompactOpen

noncomputable section

open scoped Topology

namespace MyProjects.Topology.B

variable {X Y Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable [LocallyCompactSpace X] [LocallyCompactSpace Y]

-- Homeomorphism for the exponential law under compact–open topology.
-- In this snapshot it is available as `Homeomorph.curry`.
abbrev expLawCOHomeo : C(X × Y, Z) ≃ₜ C(X, C(Y, Z)) :=
  Homeomorph.curry (X:=X) (Y:=Y) (Z:=Z)

-- β/η (pointwise, simp-safe)

@[simp] lemma expLawCO_apply (f : C(X × Y, Z)) (x : X) (y : Y) :
  (expLawCOHomeo (X:=X) (Y:=Y) (Z:=Z) f) x y = f (x, y) := rfl

@[simp] lemma expLawCO_symm_apply (g : C(X, C(Y, Z))) (x : X) (y : Y) :
  (expLawCOHomeo (X:=X) (Y:=Y) (Z:=Z)).symm g (x, y) = g x y := rfl

@[simp] lemma expLawCO_left_inv (f : C(X × Y, Z)) :
  (expLawCOHomeo (X:=X) (Y:=Y) (Z:=Z)).symm (expLawCOHomeo f) = f := by
  ext x y; rfl

@[simp] lemma expLawCO_right_inv (g : C(X, C(Y, Z))) :
  expLawCOHomeo ((expLawCOHomeo (X:=X) (Y:=Y) (Z:=Z)).symm g) = g := by
  ext x y; rfl

-- Naturality (pointwise `@[simp]`)

-- X-side precomposition: `(φ × id)` downstairs, postcomposition by `(· ∘ φ)` upstairs.
@[simp] lemma expLawCO_precomp_left_apply
  {X X' Y Z : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Z]
  [LocallyCompactSpace X] [LocallyCompactSpace X'] [LocallyCompactSpace Y]
  (φ : C(X', X)) (f : C(X × Y, Z)) (x' : X') (y : Y) :
  (expLawCOHomeo (X:=X') (Y:=Y) (Z:=Z)
      (f.comp (ContinuousMap.prodMk (φ.comp ContinuousMap.fst) ContinuousMap.snd))) x' y
  = (expLawCOHomeo (X:=X) (Y:=Y) (Z:=Z) f) (φ x') y := rfl

-- Y-side precomposition: `(id × τ)` downstairs, precomposition in the inner slot upstairs.
@[simp] lemma expLawCO_precomp_right_apply
  {X Y Y' Z : Type*}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Y'] [TopologicalSpace Z]
  [LocallyCompactSpace X] [LocallyCompactSpace Y] [LocallyCompactSpace Y']
  (τ : C(Y', Y)) (f : C(X × Y, Z)) (x : X) (y' : Y') :
  (expLawCOHomeo (X:=X) (Y:=Y') (Z:=Z)
      (f.comp (ContinuousMap.prodMk ContinuousMap.fst (τ.comp ContinuousMap.snd)))) x y'
  = (expLawCOHomeo (X:=X) (Y:=Y) (Z:=Z) f) x (τ y') := rfl

-- Z-side postcomposition: curry commutes with postcomposition.
@[simp] lemma expLawCO_postcomp_apply
  {X Y Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace Z']
  [LocallyCompactSpace X] [LocallyCompactSpace Y]
  (ψ : C(Z, Z')) (f : C(X × Y, Z)) (x : X) (y : Y) :
  (expLawCOHomeo (X:=X) (Y:=Y) (Z:=Z') (ψ.comp f)) x y
  = ψ ((expLawCOHomeo (X:=X) (Y:=Y) (Z:=Z) f) x y) := rfl

end MyProjects.Topology.B
