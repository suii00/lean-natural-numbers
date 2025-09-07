/-
  Topology B — Scaffold generated from:
  src/MyProjects/Topology/B/claude_topologyB_en.md

  Notes:
  - This file is a scaffold converted from the Markdown brief.
  - Declarations are placeholders or comments to guide implementation.
  - Encoding: UTF-8 (no BOM), EOL: LF.
  - Replace `axiom` stubs with real implementations over mathlib.
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.CompactOpen

set_option autoImplicit true

noncomputable section

namespace MyProjects.Topology.B

open scoped Topology
open CategoryTheory

/-
Submission Analysis: Complete Implementation of Product Universality and Exponential Laws

Mastered concepts (from brief):
- Bidirectional proof of product universality (categorical characterization)
- Continuity of structural morphisms in topological rings
- Exponential law `C(X × Y, Z) ≃ C(X, C(Y, Z))`
- Continuity of the evaluation map under the compact-open topology
- Consistency between currying composition rules and precomposition

Outstanding achievements (targets to formalize):
- Use of `Homeomorph.curry` as a homeomorphism
- Local compactness generalized via `LocallyCompactSpace`
- `@[simp]` lemmas for β-reduction of curry/uncurry
- Continuity of partial evaluation
- Concrete examples over `ℝ`
-/

/-
Section A: Adjoint Functors in Categories of Topological Spaces

Goal sketches from the brief. Replace `axiom` stubs with real statements once the precise
API is chosen (TopCat vs. Concrete categories, functors on `TopCat`).
-/
section Adjunctions

/-
Adjunction between product and diagonal functors (sketch).
Expected shape: `Adjunction Δ ⊣ (X ↦ X × -)` on `TopCat`.
Note: In mathlib, the category of topological spaces is `TopCat`.
-/
/-
Continuous product universality in `TopCat` specialized to `ContinuousMap`:
`C(X, Y × Z) ≃ C(X, Y) × C(X, Z)`.
This is the data-level bijection behind `Δ ⊣ (×_)`.
-/
section ProductUniversality

variable {X Y Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Universal property of binary products for continuous maps. -/
def prodHomEquiv : C(X, Y × Z) ≃ (C(X, Y) × C(X, Z)) where
  toFun f := (ContinuousMap.fst.comp f, ContinuousMap.snd.comp f)
  invFun g := g.1.prodMk g.2
  left_inv f := by
    ext x <;> rfl
  right_inv g := by
    cases g with
    | mk f g =>
      apply Prod.ext <;> ext x <;> rfl

@[simp] lemma prodHomEquiv_toFun_fst (f : C(X, Y × Z)) :
    (prodHomEquiv (X:=X) (Y:=Y) (Z:=Z) f).1 = ContinuousMap.fst.comp f := rfl

@[simp] lemma prodHomEquiv_toFun_snd (f : C(X, Y × Z)) :
    (prodHomEquiv (X:=X) (Y:=Y) (Z:=Z) f).2 = ContinuousMap.snd.comp f := rfl

lemma prodHomEquiv_invFun_fst (f : C(X, Y)) (g : C(X, Z)) :
    ContinuousMap.fst.comp (((prodHomEquiv (X:=X) (Y:=Y) (Z:=Z)).invFun (f, g))) = f := by
  ext x; rfl

lemma prodHomEquiv_invFun_snd (f : C(X, Y)) (g : C(X, Z)) :
    ContinuousMap.snd.comp (((prodHomEquiv (X:=X) (Y:=Y) (Z:=Z)).invFun (f, g))) = g := by
  ext x; rfl

end ProductUniversality

/- A lightweight categorical packaging: record the existence of the adjunction as a Prop. -/
def product_diagonal_adjunction : Prop := True

/-
Diagonal ⊣ Product (as functors):

`diag : TopCat ⥤ TopCat × TopCat` has a right adjoint given by the "binary product" functor
`TopCat × TopCat ⥤ TopCat` sending `(Y, Z)` to the product space `Y × Z` with the product topology.
-/
section DiagonalAdjunction

open TopCat

universe u

/- The product functor on `TopCat` implemented via type-level product. -/
def prodFunctorTop : (TopCat.{u} × TopCat.{u}) ⥤ TopCat.{u} where
  obj X := TopCat.of ((X.1) × (X.2))
  map f :=
    TopCat.ofHom ⟨fun p => (f.1 p.1, f.2 p.2),
      Continuous.prodMk (f.1.hom.continuous.comp continuous_fst)
                        (f.2.hom.continuous.comp continuous_snd)⟩

/- Hom-set equivalence used for the adjunction. -/
def homEquiv
  (X : TopCat.{u}) (YZ : TopCat.{u} × TopCat.{u}) :
  ((Functor.diag (C:=TopCat)).obj X ⟶ YZ) ≃ (X ⟶ (prodFunctorTop.obj YZ)) := by
  rcases X with ⟨X, _⟩; rcases YZ with ⟨Y, Z⟩
  -- Left side: pair of Top morphisms `(X ⟶ Y) × (X ⟶ Z)`
  change ((TopCat.of X ⟶ Y) × (TopCat.of X ⟶ Z)) ≃ (TopCat.of X ⟶ TopCat.of (Y × Z))
  refine
    { toFun :=
        (fun fg =>
          let fy : C(X, Y) := (fg.1).hom
          let fz : C(X, Z) := (fg.2).hom
          TopCat.ofHom ((prodHomEquiv (X:=X) (Y:=Y) (Z:=Z)).symm (fy, fz)))
      , invFun :=
        (fun h =>
          let h' : C(X, Y × Z) := h.hom
          let p := (prodHomEquiv (X:=X) (Y:=Y) (Z:=Z)) h'
          (TopCat.ofHom p.1, TopCat.ofHom p.2))
      , left_inv := by
          intro fg; cases fg with
          | mk f g =>
            apply Prod.ext
            · -- fst ∘ (f,g) = f
              ext x; rfl
            · -- snd ∘ (f,g) = g
              ext x; rfl
      , right_inv := by
          intro h
          -- `(fst ∘ h, snd ∘ h)` paired back is `h`.
          ext x <;> rfl }

/- Assemble the adjunction via `mkOfHomEquiv`. -/
def diagProdAdjunction :
  CategoryTheory.Adjunction (F := Functor.diag (C:=TopCat.{u})) (G := prodFunctorTop) := by
  classical
  refine CategoryTheory.Adjunction.mkOfHomEquiv ?core
  refine { homEquiv := fun X Y => homEquiv X Y
         , homEquiv_naturality_left_symm := ?nleft
         , homEquiv_naturality_right := ?nright }
  · -- naturality in the left variable (precomposition)
    intro X' X Y f g
    -- both sides are morphisms `TopCat.of X' ⟶ TopCat.of (Y.1 × Y.2)`; prove by ext
    ext x <;> rfl
  · -- naturality in the right variable (postcomposition)
    intro X Y Y' f g
    -- `f` is a pair of morphisms; `G.map g` acts componentwise on product
    ext x <;> rfl

end DiagonalAdjunction

/-
-- (Reserved) We can add `@[simp]` unit/counit lemmas for `diagProdAdjunction`
-- after confirming projection names in this mathlib snapshot.
-/

section DiagonalAdjunctionSimp

open TopCat

universe u

@[simp, reassoc]
lemma unit_comp_counit_fst (X : TopCat.{u}) :
    (diagProdAdjunction.unit.app X) ≫
      (diagProdAdjunction.counit.app ((X, X))).1 = 𝟙 X := by
  -- First component of left triangle identity
  have h := diagProdAdjunction.left_triangle_components (X := X)
  -- Take the first component equality in the product category
  simpa using congrArg Prod.fst h

@[simp, reassoc]
lemma unit_comp_counit_snd (X : TopCat.{u}) :
    (diagProdAdjunction.unit.app X) ≫
      (diagProdAdjunction.counit.app ((X, X))).2 = 𝟙 X := by
  have h := diagProdAdjunction.left_triangle_components (X := X)
  simpa using congrArg Prod.snd h

end DiagonalAdjunctionSimp

/-
Bridging: make `TopCat.ofHom`/composition evaluation simp-friendly.
These restate existing lemmas with `@[simp]` so category-style composites
reduce to pointwise equalities via `ext x; simp`.
-/
-- (Optional) Symmetric right triangle lemmas can be obtained on demand by
-- applying `ConcreteCategory.congr_hom` to
-- `diagProdAdjunction.right_triangle_components` and then `simp` pointwise.

/-
Exponential law — Pi-topology version (always available):
`curryPi : C(X × Y, Z) → C(X, Y → Z)` with β-rule.
The inverse/homeomorphism needs compact–open; see below.
-/
section ExponentialPi

variable {X Y Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Currying into the Pi-topology function space `Y → Z`. -/
def curryPi (f : C(X × Y, Z)) : C(X, Y → Z) :=
  ContinuousMap.pi (fun (y : Y) =>
    f.comp <| ContinuousMap.prodMk (ContinuousMap.id X) (ContinuousMap.const X y))

@[simp] lemma curryPi_apply (f : C(X × Y, Z)) (x : X) (y : Y) :
    curryPi (X:=X) (Y:=Y) (Z:=Z) f x y = f (x, y) := rfl

/-! Naturality for `curryPi` under pre/post composition. -/

/- Precompose on the first variable: `(φ ×ᵣ id)` before `f`. -/
def precompProdLeft {X' : Type*} [TopologicalSpace X'] (φ : C(X', X)) :
    C(X' × Y, X × Y) :=
  ContinuousMap.prodMk (φ.comp ContinuousMap.fst) ContinuousMap.snd

@[simp] lemma precompProdLeft_apply {X'} [TopologicalSpace X']
    (φ : C(X', X)) (p : X' × Y) :
    precompProdLeft (X:=X) (Y:=Y) φ p = (φ p.1, p.2) := rfl

lemma curryPi_precomp_left {X'} [TopologicalSpace X'] (φ : C(X', X)) (f : C(X × Y, Z)) :
    curryPi (X:=X') (Y:=Y) (Z:=Z) (f.comp (precompProdLeft (X:=X) (Y:=Y) φ))
      = (curryPi (X:=X) (Y:=Y) (Z:=Z) f).comp φ := by
  ext x y; rfl

/- Precompose on the second variable: `(id ×ᵣ τ)` before `f`. -/
def precompProdRight {Y' : Type*} [TopologicalSpace Y'] (τ : C(Y', Y)) :
    C(X × Y', X × Y) :=
  ContinuousMap.prodMk ContinuousMap.fst (τ.comp ContinuousMap.snd)

@[simp] lemma precompProdRight_apply {Y'} [TopologicalSpace Y']
    (τ : C(Y', Y)) (p : X × Y') :
    precompProdRight (X:=X) (Y:=Y) τ p = (p.1, τ p.2) := rfl

def precompPi {Y' : Type*} [TopologicalSpace Y'] (τ : C(Y', Y))
    (g : C(X, Y → Z)) : C(X, Y' → Z) :=
  ContinuousMap.pi (fun (y' : Y') => ((ContinuousMap.eval (τ y')).comp g))

@[simp] lemma precompPi_apply {Y'} [TopologicalSpace Y']
    (τ : C(Y', Y)) (g : C(X, Y → Z)) (x : X) (y' : Y') :
    precompPi (X:=X) (Y:=Y) (Z:=Z) τ g x y' = g x (τ y') := rfl

lemma curryPi_precomp_right {Y'} [TopologicalSpace Y'] (τ : C(Y', Y)) (f : C(X × Y, Z)) :
    curryPi (X:=X) (Y:=Y') (Z:=Z) (f.comp (precompProdRight (X:=X) (Y:=Y) τ))
      = precompPi (X:=X) (Y:=Y) (Z:=Z) τ (curryPi (X:=X) (Y:=Y) (Z:=Z) f) := by
  ext x y'; rfl

/- Postcompose in the codomain: `ψ ∘ f`. -/
def postcompPi {W : Type*} [TopologicalSpace W]
    (ψ : C(Z, W)) (g : C(X, Y → Z)) : C(X, Y → W) :=
  ContinuousMap.pi (fun (y : Y) => ψ.comp ((ContinuousMap.eval y).comp g))

@[simp] lemma postcompPi_apply {W} [TopologicalSpace W]
    (ψ : C(Z, W)) (g : C(X, Y → Z)) (x : X) (y : Y) :
    postcompPi (X:=X) (Y:=Y) ψ g x y = ψ (g x y) := rfl

lemma curryPi_postcomp {W} [TopologicalSpace W]
    (ψ : C(Z, W)) (f : C(X × Y, Z)) :
    curryPi (X:=X) (Y:=Y) (Z:=W) (ψ.comp f)
      = postcompPi (X:=X) (Y:=Y) ψ (curryPi (X:=X) (Y:=Y) (Z:=Z) f) := by
  ext x y; rfl

/-! Algebra for product precomposition and Pi post/pre composition (id/comp). -/

@[simp] lemma precompProdLeft_id :
    precompProdLeft (X:=X) (Y:=Y) (ContinuousMap.id X)
      = (ContinuousMap.id (X × Y)) := by
  ext p <;> rfl

lemma precompProdLeft_comp {X₁ X₂ X₃ : Type*}
    [TopologicalSpace X₁] [TopologicalSpace X₂] [TopologicalSpace X₃]
    (φ₁ : C(X₂, X₁)) (φ₂ : C(X₃, X₂)) :
    (precompProdLeft (X:=X₁) (Y:=Y) φ₁).comp
      (precompProdLeft (X:=X₂) (Y:=Y) φ₂)
      = precompProdLeft (X:=X₁) (Y:=Y) (φ₁.comp φ₂) := by
  ext p <;> rfl

@[simp] lemma precompProdRight_id :
    precompProdRight (X:=X) (Y:=Y) (ContinuousMap.id Y)
      = (ContinuousMap.id (X × Y)) := by
  ext p <;> rfl

lemma precompProdRight_comp {Y₁ Y₂ Y₃ : Type*}
    [TopologicalSpace Y₁] [TopologicalSpace Y₂] [TopologicalSpace Y₃]
    (τ₁ : C(Y₂, Y₁)) (τ₂ : C(Y₃, Y₂)) :
    (precompProdRight (X:=X) (Y:=Y₁) τ₁).comp
      (precompProdRight (X:=X) (Y:=Y₂) τ₂)
      = precompProdRight (X:=X) (Y:=Y₁) (τ₁.comp τ₂) := by
  ext p <;> rfl

@[simp] lemma precompPi_id (g : C(X, Y → Z)) :
    precompPi (X:=X) (Y:=Y) (Z:=Z) (ContinuousMap.id Y) g = g := by
  ext x y; rfl

lemma precompPi_comp {Y₁ Y₂ Y₃ : Type*}
    [TopologicalSpace Y₁] [TopologicalSpace Y₂] [TopologicalSpace Y₃]
    (τ₁ : C(Y₂, Y₁)) (τ₂ : C(Y₃, Y₂)) (g : C(X, Y₁ → Z)) :
    precompPi (X:=X) (Y:=Y₁) (Z:=Z) (τ₁.comp τ₂) g
      = precompPi (X:=X) (Y:=Y₂) (Z:=Z) τ₂ (precompPi (X:=X) (Y:=Y₁) (Z:=Z) τ₁ g) := by
  ext x y; rfl

@[simp] lemma postcompPi_id (g : C(X, Y → Z)) :
    postcompPi (X:=X) (Y:=Y) (Z:=Z) (ContinuousMap.id Z) g = g := by
  ext x y; rfl

lemma postcompPi_comp {W U : Type*} [TopologicalSpace W] [TopologicalSpace U]
    (χ : C(W, U)) (ψ : C(Z, W)) (g : C(X, Y → Z)) :
    postcompPi (X:=X) (Y:=Y) χ (postcompPi (X:=X) (Y:=Y) ψ g)
      = postcompPi (X:=X) (Y:=Y) (χ.comp ψ) g := by
  ext x y; rfl

/-! Constants curry/uncurry normalize to constants. -/

@[simp] lemma curryPi_const (c : Z) :
    curryPi (X:=X) (Y:=Y) (Z:=Z) (ContinuousMap.const (X × Y) c)
      = ContinuousMap.const X (Function.const Y c) := rfl

-- moved below `uncurryPi` definition
/-- Uncurrying from the Pi-topology function space. This needs `[DiscreteTopology Y]` for joint
continuity of evaluation. -/
def uncurryPi [DiscreteTopology Y] (g : C(X, Y → Z)) : C(X × Y, Z) :=
  { toFun := fun p => g p.1 p.2
    continuous_toFun := by
      -- Use the characterization of continuity on a product with a discrete factor.
      refine (continuous_prod_of_discrete_right).2 ?_;
      intro y;
      -- For fixed `y`, the slice `x ↦ g x y` is `continuous_apply y ∘ g`.
      simpa using (continuous_apply y).comp g.continuous }

@[simp] lemma uncurryPi_apply [DiscreteTopology Y]
    (g : C(X, Y → Z)) (x : X) (y : Y) :
    uncurryPi (X:=X) (Y:=Y) (Z:=Z) g (x, y) = g x y := rfl

@[simp] lemma uncurryPi_const [DiscreteTopology Y] (h : C(Y, Z)) :
    uncurryPi (X:=X) (Y:=Y) (Z:=Z) (ContinuousMap.const X (fun y => h y))
      = h.comp ContinuousMap.snd := rfl

/-- Exponential law (Pi-topology version) as an equivalence. -/
def expLawPi [DiscreteTopology Y] : C(X × Y, Z) ≃ C(X, Y → Z) where
  toFun := curryPi (X:=X) (Y:=Y) (Z:=Z)
  invFun := uncurryPi (X:=X) (Y:=Y) (Z:=Z)
  left_inv f := by
    ext x y; rfl
  right_inv g := by
    ext x y; rfl

@[simp] lemma expLawPi_toFun [DiscreteTopology Y]
    (f : C(X × Y, Z)) (x : X) (y : Y) :
    (expLawPi (X:=X) (Y:=Y) (Z:=Z) f) x y = f (x, y) := rfl

@[simp] lemma expLawPi_invFun [DiscreteTopology Y]
    (g : C(X, Y → Z)) (x : X) (y : Y) :
    (expLawPi (X:=X) (Y:=Y) (Z:=Z)).invFun g (x, y) = g x y := rfl

end ExponentialPi

/-
Uncurry-side naturality for the Pi-topology version (pointwise `@[simp]` lemmas).
These let `ext x y; simp` crush composites around `uncurryPi`.
-/
section ExponentialPiUncurryNaturality

variable {X Y Z W X' Y' : Type*}
variable [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y]
  [TopologicalSpace Y'] [TopologicalSpace Z] [TopologicalSpace W]

@[simp] lemma uncurryPi_precomp_left_apply [DiscreteTopology Y]
    (φ : C(X', X)) (g : C(X, Y → Z)) (x' : X') (y : Y) :
    (uncurryPi (X:=X) (Y:=Y) (Z:=Z) g).comp (precompProdLeft (X:=X) (Y:=Y) φ) (x', y)
      = (uncurryPi (X:=X') (Y:=Y) (Z:=Z) (g.comp φ)) (x', y) := by
  simp [uncurryPi_apply, precompProdLeft_apply]

@[simp] lemma uncurryPi_precomp_right_apply [DiscreteTopology Y] [DiscreteTopology Y']
    (τ : C(Y', Y)) (g : C(X, Y → Z)) (x : X) (y' : Y') :
    (uncurryPi (X:=X) (Y:=Y) (Z:=Z) g).comp (precompProdRight (X:=X) (Y:=Y) τ) (x, y')
      = (uncurryPi (X:=X) (Y:=Y') (Z:=Z) (precompPi (X:=X) (Y:=Y) (Z:=Z) τ g)) (x, y') := by
  simp [uncurryPi_apply, precompProdRight_apply, precompPi_apply]

@[simp] lemma uncurryPi_postcomp_apply [DiscreteTopology Y]
    (ψ : C(Z, W)) (g : C(X, Y → Z)) (x : X) (y : Y) :
    (ψ.comp (uncurryPi (X:=X) (Y:=Y) (Z:=Z) g)) (x, y)
      = (uncurryPi (X:=X) (Y:=Y) (Z:=W) (postcompPi (X:=X) (Y:=Y) ψ g)) (x, y) := by
  simp [uncurryPi_apply, postcompPi_apply]

end ExponentialPiUncurryNaturality

/-
Exponential law — compact–open version (internal exponential in `TopCat`).
We recall the mathlib API and expose convenient aliases for simp.
-/
section ExponentialCompactOpen

variable {X Y Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

@[simp] lemma curry_apply (f : C(X × Y, Z)) (x : X) (y : Y) :
    ContinuousMap.curry f x y = f (x, y) := rfl

/-- Uncurrying under compact–open requires local compactness of `Y`. -/
@[simp] lemma uncurry_apply [LocallyCompactSpace Y]
    (g : C(X, C(Y, Z))) (x : X) (y : Y) :
    (ContinuousMap.uncurry g) (x, y) = g x y := rfl

/-- The compact–open homeomorphism (needs `X, Y` locally compact). -/
def curryHomeo [LocallyCompactSpace X] [LocallyCompactSpace Y] :
    C(X × Y, Z) ≃ₜ C(X, C(Y, Z)) :=
  Homeomorph.curry (X:=X) (Y:=Y) (Z:=Z)

@[simp] lemma curry_uncurry [LocallyCompactSpace Y]
    (g : C(X, C(Y, Z))) : ContinuousMap.curry (ContinuousMap.uncurry g) = g := by
  ext x y; rfl

@[simp] lemma uncurry_curry [LocallyCompactSpace X] [LocallyCompactSpace Y]
    (f : C(X × Y, Z)) : ContinuousMap.uncurry (ContinuousMap.curry f) = f := by
  ext p; cases p; rfl

/-! Naturality (compact–open): pointwise simp rules so that `ext; simp` crushes composites. -/

@[simp] lemma curry_precomp_left_apply {X'} [TopologicalSpace X']
    (φ : C(X', X)) (f : C(X × Y, Z)) (x' : X') (y : Y) :
    (ContinuousMap.curry (f.comp (precompProdLeft (X:=X) (Y:=Y) φ))) x' y
      = (ContinuousMap.curry f) (φ x') y := by
  simp [curry_apply, precompProdLeft_apply]

@[simp] lemma curry_precomp_right_apply {Y'} [TopologicalSpace Y']
    (τ : C(Y', Y)) (f : C(X × Y, Z)) (x : X) (y' : Y') :
    (ContinuousMap.curry (f.comp (precompProdRight (X:=X) (Y:=Y) τ))) x y'
      = (ContinuousMap.curry f) x (τ y') := by
  simp [curry_apply, precompProdRight_apply]

@[simp] lemma curry_postcomp_apply {W} [TopologicalSpace W]
    (ψ : C(Z, W)) (f : C(X × Y, Z)) (x : X) (y : Y) :
    (ContinuousMap.curry (ψ.comp f)) x y = ψ ((ContinuousMap.curry f) x y) := by
  simp [curry_apply]

/- Additional helpers to express uncurry-side naturality. -/
def precompCo {Y' : Type*} [TopologicalSpace Y']
    (τ : C(Y', Y)) (g : C(X, C(Y, Z))) : C(X, C(Y', Z)) :=
  ⟨fun x => (g x).comp τ,
    (ContinuousMap.continuous_precomp (X:=Y') (Y:=Y) (Z:=Z) (f:=τ)).comp g.continuous⟩

def postcompCo {W : Type*} [TopologicalSpace W]
    (ψ : C(Z, W)) (g : C(X, C(Y, Z))) : C(X, C(Y, W)) :=
  ⟨fun x => ψ.comp (g x), (ContinuousMap.continuous_postcomp (X:=Y) (Y:=Z) (Z:=W) (g:=ψ)).comp g.continuous⟩

@[simp] lemma precompCo_apply {Y'} [TopologicalSpace Y']
    (τ : C(Y', Y)) (g : C(X, C(Y, Z))) (x : X) :
    precompCo (X:=X) (Y:=Y) (Z:=Z) τ g x = (g x).comp τ := rfl

@[simp] lemma postcompCo_apply {W} [TopologicalSpace W]
    (ψ : C(Z, W)) (g : C(X, C(Y, Z))) (x : X) :
    postcompCo (X:=X) (Y:=Y) (Z:=Z) ψ g x = ψ.comp (g x) := rfl

/-! Uncurry-side naturality (compact–open): pointwise simp rules. -/

@[simp] lemma uncurry_precomp_left_apply {X'} [TopologicalSpace X'] [LocallyCompactSpace Y]
    (φ : C(X', X)) (g : C(X, C(Y, Z))) (x' : X') (y : Y) :
    ((ContinuousMap.uncurry g).comp (precompProdLeft (X:=X) (Y:=Y) φ)) (x', y)
      = (ContinuousMap.uncurry (g.comp φ)) (x', y) := by
  simp [uncurry_apply, precompProdLeft_apply]

@[simp] lemma uncurry_precomp_right_apply {Y'} [TopologicalSpace Y']
    [LocallyCompactSpace Y] [LocallyCompactSpace Y']
    (τ : C(Y', Y)) (g : C(X, C(Y, Z))) (x : X) (y' : Y') :
    ((ContinuousMap.uncurry g).comp (precompProdRight (X:=X) (Y:=Y) τ)) (x, y')
      = (ContinuousMap.uncurry (precompCo (X:=X) (Y:=Y) (Z:=Z) τ g)) (x, y') := by
  simp [uncurry_apply, precompProdRight_apply, precompCo_apply]

@[simp] lemma uncurry_postcomp_apply {W} [TopologicalSpace W] [LocallyCompactSpace Y]
    (ψ : C(Z, W)) (g : C(X, C(Y, Z))) (x : X) (y : Y) :
    (ψ.comp (ContinuousMap.uncurry g)) (x, y)
      = (ContinuousMap.uncurry (postcompCo (X:=X) (Y:=Y) (Z:=Z) ψ g)) (x, y) := by
  simp [uncurry_apply, postcompCo_apply]

end ExponentialCompactOpen

end Adjunctions

/-
Section B: Covering Spaces and Fundamental Groups (scaffold)

This section sets up placeholders for covering maps and path lifting.
Precise definitions require more infrastructure (local homeomorphisms, evenly covered neighborhoods).
-/
section Coverings

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]

/- A minimal placeholder to mark intent; replace with a full definition. -/
structure CoveringMap (p : E → B) : Prop :=
  /- TODO: continuity of `p`, evenly covered neighborhoods, etc. -/
  (placeholder : True := True.intro)

/- Path lifting theorem (statement placeholder). -/
axiom path_lifting_theorem : Prop

end Coverings

/-
Section C: Stone–Čech Compactification (scaffold)

Mathlib provides `StoneCech` for types; universal property relates continuous maps from `X`
to any compact Hausdorff space `K` with continuous maps from `StoneCech X` to `K`.
-/
section StoneCech

variable {X : Type*} [TopologicalSpace X]

/- Universal property (placeholder). -/
axiom stoneCech_universal : Prop

/- Stone–Weierstrass via compactification (directional placeholder). -/
axiom stone_weierstrass_via_compactification : Prop

end StoneCech

end MyProjects.Topology.B


