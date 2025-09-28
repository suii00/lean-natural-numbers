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
