import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Adjunctions
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Topology.Order
import MyProjects.BourbakiStyle.Topology.ContinuousComposition

open CategoryTheory Limits
open Set

namespace MyProjects
namespace BourbakiStyle
namespace Topology

/-!
Bourbaki-style topological spaces organised as a category.

We package a type and its Bourbaki topology together with morphisms as ordered
pairs `(f, proof)` so that identities and composition satisfy the categorical
axioms.  A forgetful functor back to `TopCat` witnesses compatibility with
Mathlib's `TopologicalSpace` universe and yields an explicit equivalence
`equivTopCat : BTop ≌ TopCat`, allowing categorical structure to be
transferred to or from `TopCat` when needed.
-/

universe u v w

open scoped Classical

noncomputable section

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
  toTopologicalSpace (X.τ)

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

instance instCoeFun {X Y : BTop} : CoeFun (X ⟶ Y) (fun _ => X → Y) :=
  ⟨fun f => f.toFun⟩

@[simp] lemma id_apply (X : BTop) (x : X) :
    (𝟙 X : X ⟶ X) x = x := rfl

@[simp] lemma comp_apply {X Y Z : BTop} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := rfl

noncomputable def toTopCatObj (X : BTop) : TopCat :=
  TopCat.of X

noncomputable def toTopCatMap {X Y : BTop} (f : X ⟶ Y) :
    toTopCatObj X ⟶ toTopCatObj Y :=
  TopCat.ofHom
    { toFun := f
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
    (forgetToTopCat.map f : X → Y) x = f x := rfl

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
    (ofTopCat.map f) x = f x := rfl

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
    (unitIso.hom.app X) x = x := rfl

@[simp, reassoc] lemma forgetToTopCat_map_unitIso_hom (X : BTop) :
    forgetToTopCat.map (unitIso.hom.app X) = 𝟙 _ := by
  ext x
  rfl

@[simp, reassoc] lemma counitIso_hom_app (X : TopCat) :
    counitIso.hom.app X = 𝟙 _ := by
  cases X
  rfl

@[simp, reassoc] lemma counitIso_inv_app (X : TopCat) :
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

noncomputable def forget : BTop ⥤ Type u where
  obj X := X
  map f := f
  map_id X := rfl
  map_comp f g := rfl

@[simp] lemma forget_obj (X : BTop) : forget.obj X = X := rfl

@[simp] lemma forget_map_apply {X Y : BTop}
    (f : X ⟶ Y) (x : X) : forget.map f x = f x := rfl

instance : (forget : BTop ⥤ Type u).Faithful := by
  constructor
  intro X Y f g hfg
  apply BourbakiMorphism.ext
  intro x
  have := congrArg (fun h => h x) hfg
  simpa using this

noncomputable instance : HasForget BTop where
  forget := forget
  forget_faithful := inferInstance

noncomputable instance : HasForget₂ BTop TopCat where
  forget₂ := forgetToTopCat
  forget_comp := rfl

noncomputable instance : HasForget₂ BTop (Type u) where
  forget₂ := forget
  forget_comp := rfl

section InitialFinal

variable {ι : Type v} {X : Type u}

noncomputable def initialTopology (F : ι → BTop) (φ : ∀ i, X → F i) :
    BourbakiTopology X :=
  ofTopologicalSpace
    (⨅ i, TopologicalSpace.induced (φ i) (toTopologicalSpace ((F i).τ)))

noncomputable def initial (F : ι → BTop) (φ : ∀ i, X → F i) : BTop :=
  { α := X
    τ := initialTopology (X := X) F φ }

noncomputable def initialProjection (F : ι → BTop) (φ : ∀ i, X → F i) (i : ι) :
    initial (X := X) F φ ⟶ F i := by
  classical
  have h₀ :
      @Continuous X (F i)
        (TopologicalSpace.induced (φ i) (toTopologicalSpace ((F i).τ)))
        (toTopologicalSpace ((F i).τ)) (φ i) := by
    simpa using (continuous_induced_dom (t := toTopologicalSpace ((F i).τ)) (f := φ i))
  have h₁ :
      @Continuous X (F i)
        (⨅ j, TopologicalSpace.induced (φ j) (toTopologicalSpace ((F j).τ)))
        (toTopologicalSpace ((F i).τ)) (φ i) :=
    continuous_iInf_dom
      (t₁ := fun j => TopologicalSpace.induced (φ j) (toTopologicalSpace ((F j).τ)))
      (t₂ := toTopologicalSpace ((F i).τ))
      (i := i) (f := φ i) h₀
  have h₂ :
      @Continuous (initial (X := X) F φ) (F i)
        (toTopologicalSpace ((initial (X := X) F φ).τ))
        (toTopologicalSpace ((F i).τ)) (fun x => φ i x) := by
    simpa [initial, initialTopology, to_ofTopologicalSpace] using h₁
  exact BourbakiMorphism.ofContinuous h₂

@[simp] lemma initialProjection_apply (F : ι → BTop) (φ : ∀ i, X → F i)
    (i : ι) (x : initial (X := X) F φ) :
    initialProjection (X := X) F φ i x = φ i x := rfl

noncomputable def finalTopology (F : ι → BTop) (ψ : ∀ i, F i → X) :
    BourbakiTopology X :=
  ofTopologicalSpace
    (⨆ i, TopologicalSpace.coinduced (ψ i) (toTopologicalSpace ((F i).τ)))

noncomputable def final (F : ι → BTop) (ψ : ∀ i, F i → X) : BTop :=
  { α := X
    τ := finalTopology (X := X) F ψ }

noncomputable def finalInclusion (F : ι → BTop) (ψ : ∀ i, F i → X) (i : ι) :
    F i ⟶ final (X := X) F ψ := by
  classical
  have h₀ :
      @Continuous (F i) X
        (toTopologicalSpace ((F i).τ))
        (TopologicalSpace.coinduced (ψ i) (toTopologicalSpace ((F i).τ))) (ψ i) := by
    simpa using
      (continuous_coinduced_rng (t := toTopologicalSpace ((F i).τ)) (f := ψ i))
  have h₁ :
      @Continuous (F i) X
        (toTopologicalSpace ((F i).τ))
        (⨆ j, TopologicalSpace.coinduced (ψ j) (toTopologicalSpace ((F j).τ))) (ψ i) :=
    continuous_iSup_rng
      (t₁ := toTopologicalSpace ((F i).τ))
      (t₂ := fun j => TopologicalSpace.coinduced (ψ j) (toTopologicalSpace ((F j).τ)))
      (i := i) (f := ψ i) h₀
  have h₂ :
      @Continuous (F i) (final (X := X) F ψ)
        (toTopologicalSpace ((F i).τ))
        (toTopologicalSpace ((final (X := X) F ψ).τ)) (fun x => ψ i x) := by
    simpa [final, finalTopology, to_ofTopologicalSpace] using h₁
  exact BourbakiMorphism.ofContinuous h₂

@[simp] lemma finalInclusion_apply (F : ι → BTop) (ψ : ∀ i, F i → X)
    (i : ι) (x : F i) :
    finalInclusion (X := X) F ψ i x = ψ i x := rfl

lemma initial_continuous_iff {Z : BTop} (F : ι → BTop) (φ : ∀ i, X → F i)
    (f : Z → X) :
    @Continuous Z X (toTopologicalSpace (Z.τ))
        (toTopologicalSpace ((initial (X := X) F φ).τ)) f ↔
      ∀ i,
        @Continuous Z (F i) (toTopologicalSpace (Z.τ))
          (toTopologicalSpace ((F i).τ)) fun x => φ i (f x) := by
  classical
  have h :=
    (continuous_iInf_rng
      (t₁ := toTopologicalSpace (Z.τ))
      (t₂ := fun j => TopologicalSpace.induced (φ j) (toTopologicalSpace ((F j).τ)))
      (f := f))
  simpa [initial, initialTopology, to_ofTopologicalSpace, continuous_induced_rng,
    Function.comp] using h

lemma final_continuous_iff {Z : BTop} (F : ι → BTop) (ψ : ∀ i, F i → X)
    (f : X → Z) :
    @Continuous X Z (toTopologicalSpace ((final (X := X) F ψ).τ))
        (toTopologicalSpace (Z.τ)) f ↔
      ∀ i,
        @Continuous (F i) Z (toTopologicalSpace ((F i).τ))
          (toTopologicalSpace (Z.τ)) fun x => f (ψ i x) := by
  classical
  have h :=
    (continuous_iSup_dom
      (t₁ := fun j => TopologicalSpace.coinduced (ψ j) (toTopologicalSpace ((F j).τ)))
      (t₂ := toTopologicalSpace (Z.τ))
      (f := f))
  simpa [final, finalTopology, to_ofTopologicalSpace, continuous_coinduced_dom,
    Function.comp] using h

noncomputable def initialLift {Z : BTop} (F : ι → BTop) (φ : ∀ i, X → F i)
    (f : Z → X)
    (hf : ∀ i,
      @Continuous Z (F i) (toTopologicalSpace (Z.τ))
        (toTopologicalSpace ((F i).τ)) fun x => φ i (f x)) :
    Z ⟶ initial (X := X) F φ := by
  classical
  have hf' :=
    (initial_continuous_iff (X := X) (F := F) (φ := φ) (Z := Z) f).2 hf
  have hf'' :
      @Continuous Z (initial (X := X) F φ)
        (toTopologicalSpace (Z.τ))
        (toTopologicalSpace ((initial (X := X) F φ).τ)) f := by
    simpa [initial] using hf'
  exact BourbakiMorphism.ofContinuous hf''

@[simp] lemma initialLift_apply {Z : BTop} (F : ι → BTop) (φ : ∀ i, X → F i)
    (f : Z → X) (hf : ∀ i,
      @Continuous Z (F i) (toTopologicalSpace (Z.τ))
        (toTopologicalSpace ((F i).τ)) fun x => φ i (f x))
    (x : Z) :
    initialLift (X := X) F φ f hf x = f x := rfl

noncomputable def finalDesc {Z : BTop} (F : ι → BTop) (ψ : ∀ i, F i → X)
    (f : X → Z)
    (hf : ∀ i,
      @Continuous (F i) Z (toTopologicalSpace ((F i).τ))
        (toTopologicalSpace (Z.τ)) fun x => f (ψ i x)) :
    final (X := X) F ψ ⟶ Z := by
  classical
  have hf' :=
    (final_continuous_iff (X := X) (F := F) (ψ := ψ) (Z := Z) f).2 hf
  have hf'' :
      @Continuous (final (X := X) F ψ) Z
        (toTopologicalSpace ((final (X := X) F ψ).τ))
        (toTopologicalSpace (Z.τ)) f := by
    simpa [final] using hf'
  exact BourbakiMorphism.ofContinuous hf''

@[simp] lemma finalDesc_apply {Z : BTop} (F : ι → BTop) (ψ : ∀ i, F i → X)
    (f : X → Z)
    (hf : ∀ i,
      @Continuous (F i) Z (toTopologicalSpace ((F i).τ))
        (toTopologicalSpace (Z.τ)) fun x => f (ψ i x))
    (x : final (X := X) F ψ) :
    finalDesc (X := X) F ψ f hf x = f x := rfl

end InitialFinal

noncomputable def disc : Type u ⥤ BTop :=
  TopCat.discrete ⋙ ofTopCat

noncomputable def indisc : Type u ⥤ BTop :=
  TopCat.trivial ⋙ ofTopCat

noncomputable def disc_adj_forget : disc ⊣ forget := by
  simpa [disc, forget] using (TopCat.adj₁).comp (equivTopCat.symm.toAdjunction)

noncomputable def forget_adj_indisc : forget ⊣ indisc := by
  simpa [forget, indisc] using (equivTopCat.toAdjunction).comp (TopCat.adj₂)

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

example (x : X) : ((𝟙 X ≫ f) x) = f x := by
  simp

example (x : X) : ((f ≫ g) x) = g (f x) := by
  simp

variable {ι : Type v} {α : Type u}
variable (F : ι → BTop) (φ : ∀ i, α → F i) (ψ : ∀ i, F i → α)
variable {Z₁ Z₂ : BTop}
variable (f₁ : Z₁ → α) (f₂ : α → Z₂)

example (hf : ∀ i,
    @Continuous Z₁ (F i) (toTopologicalSpace (Z₁.τ))
      (toTopologicalSpace ((F i).τ)) fun x => φ i (f₁ x)) :
    @Continuous Z₁ α (toTopologicalSpace (Z₁.τ))
      (toTopologicalSpace ((initial (X := α) F φ).τ)) f₁ :=
  (initial_continuous_iff (X := α) (F := F) (φ := φ) (Z := Z₁) f₁).2 hf

example (hg : ∀ i,
    @Continuous (F i) Z₂ (toTopologicalSpace ((F i).τ))
      (toTopologicalSpace (Z₂.τ)) fun x => f₂ (ψ i x)) :
    @Continuous α Z₂ (toTopologicalSpace ((final (X := α) F ψ).τ))
      (toTopologicalSpace (Z₂.τ)) f₂ :=
  (final_continuous_iff (X := α) (F := F) (ψ := ψ) (Z := Z₂) f₂).2 hg

end Examples

end BTop

end

end Topology
end BourbakiStyle
end MyProjects


