/-
  ClaudeD: Bourbaki-style structuration via ordered pairs and projections

  This module follows the spirit of Nicolas Bourbaki's Elements de mathématique:
  structures carried by sets, ordered pairs characterized via projections, and
  morphisms organized by their behavior under these projections.

  Contents (chosen focus: Task A core, with Bourbaki flavor)
  - Equivalence of hom-sets for products: C(X, Y × Z) ≃ C(X, Y) × C(X, Z)
  - A concrete binary product functor TopCat × TopCat ⥤ TopCat
  - The diagonal–product adjunction: Functor.diag ⊣ prodFunctorTop

  Notes
  - We keep the implementation constructive with mathlib primitives.
  - Small `example` blocks act as sanity checks near new lemmas.
  - No global imports/targets are adjusted; this file stands alone.
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monad.Kleisli

noncomputable section

namespace MyProjects.Topology.D

open scoped Topology
open CategoryTheory

/-! # Ordered pairs and projections

Equivalence underlying the universal property of products, expressed on
continuous maps. This is the Bourbaki viewpoint: an arrow into a product is
determined by its composites with the projections.
-/

section ProductHomEquiv

variable {X Y Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Universal property of binary products for continuous maps.
C(X, Y × Z) ≃ C(X, Y) × C(X, Z).
The forward map is given by post-composing with the projections.
The inverse map pairs two continuous maps by `ContinuousMap.prodMk`.
-/
def prodHomEquiv : C(X, Y × Z) ≃ (C(X, Y) × C(X, Z)) where
  toFun f := (ContinuousMap.fst.comp f, ContinuousMap.snd.comp f)
  invFun g := ContinuousMap.prodMk g.1 g.2
  left_inv f := by
    ext x <;> rfl
  right_inv g := by
    cases' g with fy fz
    ext x <;> rfl

@[simp] lemma prodHomEquiv_fst (f : C(X, Y × Z)) :
    (prodHomEquiv (X:=X) (Y:=Y) (Z:=Z) f).1 = ContinuousMap.fst.comp f := rfl

@[simp] lemma prodHomEquiv_snd (f : C(X, Y × Z)) :
    (prodHomEquiv (X:=X) (Y:=Y) (Z:=Z) f).2 = ContinuousMap.snd.comp f := rfl

@[simp] lemma prodHomEquiv_symm_apply_fst (f : C(X, Y)) (g : C(X, Z)) :
    (prodHomEquiv (X:=X) (Y:=Y) (Z:=Z)).symm (f, g) = ContinuousMap.prodMk f g := rfl

-- Quick sanity examples
section Examples
  example (f : C(X, Y × Z)) (x : X) :
      ((prodHomEquiv (X:=X) (Y:=Y) (Z:=Z) f).1 x,
       (prodHomEquiv (X:=X) (Y:=Y) (Z:=Z) f).2 x) = f x := by
    simp
  example (f : C(X, Y)) (g : C(X, Z)) :
      (prodHomEquiv (X:=X) (Y:=Y) (Z:=Z)).symm (f, g) = ContinuousMap.prodMk f g := rfl
end Examples

end ProductHomEquiv

/-! # Binary product functor and the diagonal–product adjunction

We package the Bourbaki product–projection equivalence into a categorical
adjunction between the diagonal functor and the binary product functor on TopCat.
-/

section DiagonalAdjunction

open TopCat

universe u

/-- The binary product functor on `TopCat`, implemented via type-level products.
Sends `(Y, Z)` to `Y × Z`, and a pair of continuous maps `(f, g)` to
`Prod.map f g` written using `ContinuousMap` primitives.
-/
def prodFunctorTop : (TopCat.{u} × TopCat.{u}) ⥤ TopCat.{u} where
  obj YZ := TopCat.of (YZ.1 × YZ.2)
  map f := by
    -- `f.1 : Y ⟶ Y'`, `f.2 : Z ⟶ Z'` in `TopCat`.
    refine TopCat.ofHom ?h
    -- Build a continuous map `(Y × Z) → (Y' × Z')` componentwise.
    exact ContinuousMap.prodMk (f.1.hom.comp ContinuousMap.fst)
                              (f.2.hom.comp ContinuousMap.snd)

/-- The hom-set equivalence realizing `Functor.diag ⊣ prodFunctorTop`.
For each `X : TopCat` and `YZ : TopCat × TopCat`, morphisms
`(X, X) ⟶ (Y, Z)` correspond to morphisms `X ⟶ (Y × Z)`.
We build this from the concrete `prodHomEquiv` on `ContinuousMap`.
-/
def diagProd_homEquiv
  (X : TopCat.{u}) (YZ : TopCat.{u} × TopCat.{u}) :
  ((Functor.diag (C:=TopCat)).obj X ⟶ YZ) ≃ (X ⟶ prodFunctorTop.obj YZ) := by
  -- Work componentwise on the pair `YZ = (Y, Z)`.
  cases YZ with
  | mk Y Z =>
    -- LHS: morphisms `(X ⟶ Y, X ⟶ Z)`; RHS: a morphism `X ⟶ Y × Z`.
    refine
      { toFun := fun fg =>
          TopCat.ofHom <| ContinuousMap.prodMk fg.1.hom fg.2.hom
      , invFun := fun h =>
          ( TopCat.ofHom (ContinuousMap.fst.comp h.hom)
          , TopCat.ofHom (ContinuousMap.snd.comp h.hom) )
      , left_inv := by
          intro fg; cases fg with
          | mk f g =>
            ext x <;> rfl
      , right_inv := by
          intro h; ext x <;> rfl }

/-- The diagonal–product adjunction on `TopCat`.
This packages the Bourbaki equivalence into categorical form.
-/
def diagProdAdjunction :
  CategoryTheory.Adjunction (F := Functor.diag (C:=TopCat.{u})) (G := prodFunctorTop) := by
  classical
  -- Construct from hom-set equivalences, with naturality verified by `rfl`/`ext`.
  refine CategoryTheory.Adjunction.mkOfHomEquiv ?core
  refine
    { homEquiv := fun X Y => diagProd_homEquiv X Y
    , homEquiv_naturality_left_symm := ?nleft
    , homEquiv_naturality_right := ?nright }
  -- Naturality in the left variable: precomposition.
  · intro X' X Y f g
    -- Both sides are pairs of morphisms; check components pointwise.
    ext x <;> rfl
  -- Naturality in the right variable: postcomposition acts componentwise.
  · intro X Y Y' f g
    -- Componentwise action of `prodFunctorTop.map` followed by pairing.
    ext x <;> rfl

-- Minimal pointwise consequences (sanity): composing with projections recovers components.
section Sanity
  open TopCat
  variable (X : TopCat.{u}) (Y Z : TopCat.{u})

  @[simp] lemma homEquiv_toFun_fst
      (f : (Functor.diag (C:=TopCat)).obj X ⟶ (Y, Z)) (x : X) :
      (((diagProd_homEquiv X (Y, Z)) f).hom x).1 = (f.1.hom x) := rfl

  @[simp] lemma homEquiv_toFun_snd
      (f : (Functor.diag (C:=TopCat)).obj X ⟶ (Y, Z)) (x : X) :
      (((diagProd_homEquiv X (Y, Z)) f).hom x).2 = (f.2.hom x) := rfl
end Sanity

end DiagonalAdjunction

/-! # Product Monad (Task C)

From the adjunction `Functor.diag ⊣ prodFunctorTop`, we obtain a monad on `TopCat` with
underlying functor `(Functor.diag) ⋙ prodFunctorTop`, unit `η` (the diagonal), and
multiplication `μ = G ε F` (induced by the counit of the adjunction).
-/

section ProductMonad

open TopCat

/-- The monad on `TopCat` induced by the diagonal–product adjunction. -/
def productMonad : CategoryTheory.Monad TopCat :=
  (diagProdAdjunction).toMonad

@[simp] lemma productMonad_toFunctor :
    productMonad.toFunctor = (Functor.diag (C:=TopCat)) ⋙ prodFunctorTop := rfl

/-- The Kleisli category for the product monad (objects are those of `TopCat`). -/
abbrev KleisliTopCat := CategoryTheory.Kleisli productMonad

-- Quick sanity: the object part is definitional (`X ↦ X × X`).
section Examples
  variable (X : TopCat)
  example : productMonad.toFunctor.obj X = TopCat.of (X × X) := rfl
end Examples

end ProductMonad

/-! # Product monad: componentwise simp lemmas (C‑1)

These `@[simp, reassoc]` lemmas fix the pointwise behavior of the unit `η`
of `productMonad` against the product projections. They are sufficient to make
many Kleisli-side calculations discharge via `ext; simp`. (Component lemmas for
`μ` can be added next if desired.)
-/

section ProductMonadSimp

open TopCat

@[simp, reassoc]
lemma productMonad_eta_comp_fst (X : TopCat) :
    (productMonad.η.app X) ≫ (diagProdAdjunction.counit.app (X, X)).1 = 𝟙 X := by
  -- Componentwise left triangle identity for Δ ⊣ × (first projection)
  -- Expand the left triangle in `TopCat × TopCat` and take the first component.
  -- `Functor.diag.map (productMonad.η.app X)` is the pair `(η_X, η_X)`.
  -- Composing with the counit `(π₁, π₂)` yields `(𝟙, 𝟙)`.
  -- We extract the first component equality.
  -- Use the adjunction triangle at `F.obj X = (X, X)`.
  have h := diagProdAdjunction.left_triangle_components (X := X)
  -- Now project to the first component in the product category.
  -- This normalizes to the desired equality in `TopCat`.
  simpa using congrArg Prod.fst h

  @[simp, reassoc]
  lemma productMonad_eta_comp_snd (X : TopCat) :
      (productMonad.η.app X) ≫ (diagProdAdjunction.counit.app (X, X)).2 = 𝟙 X := by
    -- Componentwise left triangle identity (second projection)
    have h := diagProdAdjunction.left_triangle_components (X := X)
    simpa using congrArg Prod.snd h

  -- (Optional) μ component lemmas can be added once notations for the big
  -- projections `((X×X)×(X×X)) ⟶ (X×X)` are settled. The unit lemmas above
  -- already cover common diagonal rewrites.
-- Componentwise multiplication `μ` remarks:
-- The multiplication flattens `((X×X)×(X×X)) ⟶ (X×X)` so that the first component
-- is `π₁ ∘ π₁` and the second is `π₂ ∘ π₂`.
-- (Optional) `μ` component lemmas can be added once we settle notations for the
-- "big" projections `((X×X)×(X×X)) ⟶ (X×X)`. The unit lemmas above already
-- cover the typical rewriting needs for diagonal maps.

end ProductMonadSimp

end MyProjects.Topology.D
