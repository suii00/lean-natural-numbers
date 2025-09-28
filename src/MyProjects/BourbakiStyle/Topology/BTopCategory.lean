import Mathlib.Topology.Category.TopCat.Basic
import MyProjects.BourbakiStyle.Topology.ContinuousComposition

open CategoryTheory
open Set

namespace MyProjects
namespace BourbakiStyle
namespace Topology

/-!
Bourbaki-style topological spaces organised as a category.

We package a type and its Bourbaki topology together with morphisms as ordered
pairs `(f, proof)` so that identities and composition satisfy the categorical
axioms.  A forgetful functor back to `TopCat` witnesses compatibility with
Mathlib's `TopologicalSpace` universe.
-/

universe u v w

open scoped Classical

namespace BourbakiMorphism

variable {X : Type u} {Y : Type v}
variable {τX : BourbakiTopology X} {τY : BourbakiTopology Y}

@[ext]
lemma ext {f g : BourbakiMorphism τX τY} (h : ∀ x, f x = g x) : f = g := by
  rcases f with ⟨f, hf⟩
  rcases g with ⟨g, hg⟩
  have hfg : f = g := by
    funext x
    simpa using h x
  subst hfg
  simp

@[simp] lemma id_apply (τX : BourbakiTopology X) (x : X) :
    (BourbakiMorphism.id τX).toFun x = x := rfl

end BourbakiMorphism

/-- Bourbaki spaces packaged with their topology. -/
structure BTop where
  α : Type u
  τ : BourbakiTopology α

namespace BTop

instance : CoeSort BTop (Type u) := ⟨fun X => X.α⟩

instance instBourbakiTopology (X : BTop) : BourbakiTopology X := X.τ

instance instTopologicalSpace (X : BTop) : TopologicalSpace X :=
  toTopologicalSpace X.τ

abbrev Hom (X Y : BTop) := BourbakiMorphism X.τ Y.τ

@[simp] lemma coe_mk (α : Type u) (τ : BourbakiTopology α) :
    ((BTop.mk α τ : BTop) : Type u) = α := rfl

instance : Category BTop where
  Hom X Y := Hom X Y
  id X := BourbakiMorphism.id X.τ
  comp f g := BourbakiMorphism.comp g f
  id_comp f := by
    apply BourbakiMorphism.ext
    intro x
    rfl
  comp_id f := by
    apply BourbakiMorphism.ext
    intro x
    rfl
  assoc f g h := by
    apply BourbakiMorphism.ext
    intro x
    rfl

@[simp] lemma id_apply (X : BTop) (x : X) :
    (𝟙 X : X ⟶ X).toFun x = x := rfl

@[simp] lemma comp_apply {X Y Z : BTop} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).toFun x = g.toFun (f.toFun x) := rfl

noncomputable def toTopCatObj (X : BTop) : TopCat :=
  TopCat.of X

noncomputable def toTopCatMap {X Y : BTop} (f : X ⟶ Y) :
    toTopCatObj X ⟶ toTopCatObj Y :=
  TopCat.ofHom
    { toFun := f.toFun
      continuous_toFun :=
        BourbakiMorphism.continuous_of_morphism (τX := X.τ) (τY := Y.τ) f }

noncomputable def forgetToTopCat : BTop ⥤ TopCat where
  obj X := toTopCatObj X
  map f := toTopCatMap f
  map_id X := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

@[simp] lemma forgetToTopCat_map_apply {X Y : BTop}
    (f : X ⟶ Y) (x : X) :
    (forgetToTopCat.map f : X → Y) x = f.toFun x := rfl

@[simp] lemma forgetToTopCat_obj (X : BTop) :
    forgetToTopCat.obj X = TopCat.of X := rfl

noncomputable def ofTopCatObj (X : TopCat) : BTop :=
  { α := X
    τ := ofTopologicalSpace inferInstance }

noncomputable def ofTopCatMap {X Y : TopCat} (f : X ⟶ Y) :
    ofTopCatObj X ⟶ ofTopCatObj Y :=
  BourbakiMorphism.ofContinuous
    (X := X) (Y := Y) (f := fun x => f x)
    (by
      simpa using f.hom.continuous)

noncomputable def ofTopCat : TopCat ⥤ BTop where
  obj X := ofTopCatObj X
  map f := ofTopCatMap f
  map_id X := by
    apply BourbakiMorphism.ext
    intro x
    rfl
  map_comp f g := by
    apply BourbakiMorphism.ext
    intro x
    rfl

@[simp] lemma ofTopCat_map_apply {X Y : TopCat}
    (f : X ⟶ Y) (x : X) :
    ((ofTopCat.map f).toFun) x = f x := rfl

@[simp] lemma forgetToTopCat_comp_obj (X : BTop) :
    ((forgetToTopCat ⋙ ofTopCat).obj X) = X := by
  cases X with
  | mk α τ =>
      dsimp [Functor.comp, forgetToTopCat, ofTopCat, ofTopCatObj, toTopCatObj,
        forgetToTopCat_obj]
      apply congrArg (fun τ' => BTop.mk α τ')
      change ofTopologicalSpace (toTopologicalSpace τ) = τ
      simpa using BourbakiTopology.of_toTopologicalSpace (τ := τ)

@[simp] lemma ofTopCat_comp_obj (X : TopCat) :
    ((ofTopCat ⋙ forgetToTopCat).obj X) = X := by
  cases X
  simp [Functor.comp, ofTopCat, ofTopCatObj, forgetToTopCat, toTopCatObj,
    forgetToTopCat_obj, to_ofTopologicalSpace]

noncomputable def unitIso : 𝟭 BTop ≅ forgetToTopCat ⋙ ofTopCat :=
  NatIso.ofComponents
    (fun X =>
      { hom :=
          { toFun := fun x => x
            isContinuous := by
              intro U hU
              simp [Functor.comp, forgetToTopCat, ofTopCat, ofTopCatObj,
                toTopCatObj, forgetToTopCat_obj, BourbakiTopology.of_toTopologicalSpace] at hU
              simpa [Functor.comp, forgetToTopCat, ofTopCat, ofTopCatObj,
                toTopCatObj, forgetToTopCat_obj, BourbakiTopology.of_toTopologicalSpace]
                using hU }
        inv :=
          { toFun := fun x => x
            isContinuous := by
              intro U hU
              simp [Functor.comp, forgetToTopCat, ofTopCat, ofTopCatObj,
                toTopCatObj, forgetToTopCat_obj, BourbakiTopology.of_toTopologicalSpace] at hU
              simpa [Functor.comp, forgetToTopCat, ofTopCat, ofTopCatObj,
                toTopCatObj, forgetToTopCat_obj, BourbakiTopology.of_toTopologicalSpace]
                using hU }
        hom_inv_id := by
          apply BourbakiMorphism.ext
          intro x
          rfl
        inv_hom_id := by
          apply BourbakiMorphism.ext
          intro x
          rfl })
    (by
      intro X Y f
      apply BourbakiMorphism.ext
      intro x
      rfl)

noncomputable def counitIso : ofTopCat ⋙ forgetToTopCat ≅ 𝟭 TopCat :=
  NatIso.ofComponents
    (fun X => eqToIso (ofTopCat_comp_obj X))
    (by
      intro X Y f
      cases X
      cases Y
      cases f
      rfl)

@[simp] lemma TopCat_of_ofTopCat_obj (X : TopCat) :
    TopCat.of (ofTopCat.obj X).α = X := by
  cases X
  rfl

@[simp] lemma forgetToTopCat_obj_ofTopCat (X : TopCat) :
    forgetToTopCat.obj (ofTopCat.obj X) = X := by
  simpa [Functor.comp] using ofTopCat_comp_obj (X := X)

@[simp] lemma unitIso_hom_app_apply (X : BTop) (x : X) :
    (unitIso.hom.app X).toFun x = x := rfl

@[simp] lemma forgetToTopCat_map_unitIso_hom (X : BTop) :
    forgetToTopCat.map (unitIso.hom.app X) = 𝟙 _ := by
  ext x
  rfl

@[simp] lemma counitIso_hom_app (X : TopCat) :
    counitIso.hom.app X = 𝟙 _ := by
  cases X
  rfl

@[simp] lemma counitIso_inv_app (X : TopCat) :
    counitIso.inv.app X = 𝟙 _ := by
  cases X
  rfl

noncomputable def equivTopCat : BTop ≌ TopCat :=
{ functor := forgetToTopCat
  inverse := ofTopCat
  unitIso := unitIso
  counitIso := counitIso
  functor_unitIso_comp := by
    intro X
    simp }

section Examples

variable {X Y Z : BTop}
variable (f : X ⟶ Y) (g : Y ⟶ Z)

example : (𝟙 X ≫ f) = f := by
  apply BourbakiMorphism.ext
  intro x
  rfl

example (h : Z ⟶ BTop.mk Z.α Z.τ) : (f ≫ g) ≫ h = f ≫ (g ≫ h) := by
  apply BourbakiMorphism.ext
  intro x
  rfl

end Examples

end BTop

end Topology
end BourbakiStyle
end MyProjects
