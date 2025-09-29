import MyProjects.BourbakiStyle.Topology.BTopInitialFinal
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Adjunction.Limits

namespace MyProjects
namespace BourbakiStyle
namespace Topology

/-!
# Limits and colimits in `BTop`

We specialise the Bourbaki-style topology API to categorical constructions.
The key point is to promote the ordered-pair morphisms from the initial/final
lemmata to categorical lifts and descents, then register the universal
properties for products and coproducts.  Finally we transport global
(co)limits along the equivalence `equivTopCat : BTop ≌ TopCat`.

* `piLift`, `sigmaDesc` wrap universal arrows as ordered pairs.
* `@[simp, reassoc]` lemmas `piProj_comp_piLift` and `sigmaIn_desc` expose
  the "existence" half of uniqueness; the `*_unique` lemmas supply the reverse.
* `isLimit_piFan`, `isColimit_sigmaCofan` exhibit the canonical cones.
* `HasLimits`/`HasColimits` follow from the equivalence with `TopCat`.
-/

open CategoryTheory Limits

universe u v w

open scoped Classical

noncomputable section

namespace BTop

section Pi

variable {ι : Type v}

/-- Lift a family of morphisms into the dependent product object. -/
noncomputable def piLift {Z : BTop} (F : ι → BTop) (f : ∀ i, Z ⟶ F i) :
    Z ⟶ piObj F := by
  classical
  refine
    (BourbakiMorphism.ofContinuous
      (X := Z)
      (Y := piObj F)
      (tX := toTopologicalSpace (Z.τ))
      (tY := toTopologicalSpace ((piObj F).τ))
      (f := fun z => fun i => f i z)
      ?_)
  have hf :
      ∀ i,
        @Continuous Z (F i) (toTopologicalSpace (Z.τ))
          (toTopologicalSpace ((F i).τ)) (fun z => f i z) := by
    intro i
    simpa using BourbakiMorphism.continuous_of_morphism (f i)
  exact
    (continuous_to_pi_iff (Z := Z) (F := F)
      (f := fun z : Z => fun i => f i z)).2 (by
        intro i
        simpa using hf i)

@[simp] lemma piLift_apply {Z : BTop} (F : ι → BTop) (f : ∀ i, Z ⟶ F i)
    (z : Z) (i : ι) :
    piLift (F := F) f z i = f i z := rfl

@[simp, reassoc] lemma piProj_comp_piLift {Z : BTop} (F : ι → BTop)
    (f : ∀ i, Z ⟶ F i) (i : ι) :
    piLift (F := F) f ≫ piProj (F := F) i = f i := by
  apply BourbakiMorphism.ext
  intro z
  simp [piLift_apply, comp_apply, piProj_apply]

lemma piLift_unique {Z : BTop} (F : ι → BTop) (f : ∀ i, Z ⟶ F i)
    {g : Z ⟶ piObj F}
    (h : ∀ i, g ≫ piProj (F := F) i = f i) :
    g = piLift (F := F) f := by
  apply BourbakiMorphism.ext
  intro z
  funext i
  have hz := congrArg (fun k => k z) (h i)
  simpa [comp_apply, piProj_apply, piLift_apply] using hz

end Pi

section Sigma

variable {ι : Type v}

/-- Descend from the disjoint union object using a family of morphisms. -/
noncomputable def sigmaDesc {Z : BTop} (F : ι → BTop) (f : ∀ i, F i ⟶ Z) :
    sigmaObj F ⟶ Z := by
  classical
  refine
    (BourbakiMorphism.ofContinuous
      (X := sigmaObj F)
      (Y := Z)
      (tX := toTopologicalSpace ((sigmaObj F).τ))
      (tY := toTopologicalSpace (Z.τ))
      (f := fun s => f s.1 s.2)
      ?_)
  have hf :
      ∀ i,
        @Continuous (F i) Z (toTopologicalSpace ((F i).τ))
          (toTopologicalSpace (Z.τ)) (fun x => f i x) := by
    intro i
    simpa using BourbakiMorphism.continuous_of_morphism (f i)
  exact
    (continuous_from_sigma_iff (Z := Z) (F := F)
      (f := fun s : sigmaObj F => f s.1 s.2)).2 (by
        intro i
        simpa using hf i)

@[simp] lemma sigmaDesc_apply {Z : BTop} (F : ι → BTop) (f : ∀ i, F i ⟶ Z)
    (s : sigmaObj F) :
    sigmaDesc (F := F) f s = f s.1 s.2 := rfl

@[simp, reassoc] lemma sigmaIn_desc {Z : BTop} (F : ι → BTop)
    (f : ∀ i, F i ⟶ Z) (i : ι) :
    sigmaInl (F := F) i ≫ sigmaDesc (F := F) f = f i := by
  apply BourbakiMorphism.ext
  intro x
  simp [sigmaDesc_apply, comp_apply, sigmaInl_apply]

lemma sigmaDesc_unique {Z : BTop} (F : ι → BTop) (f : ∀ i, F i ⟶ Z)
    {g : sigmaObj F ⟶ Z}
    (h : ∀ i, sigmaInl (F := F) i ≫ g = f i) :
    g = sigmaDesc (F := F) f := by
  apply BourbakiMorphism.ext
  intro s
  rcases s with ⟨i, x⟩
  have hx := congrArg (fun k => k x) (h i)
  simpa [comp_apply, sigmaInl_apply, sigmaDesc_apply] using hx

end Sigma

section Limits

variable {ι : Type v}

/-- The canonical fan exhibiting the Bourbaki product. -/
noncomputable def piFan (F : ι → BTop) : Fan F :=
  Fan.mk (piObj F) (fun i => piProj (F := F) i)

/-- The canonical fan is limiting. -/
noncomputable def isLimit_piFan (F : ι → BTop) : IsLimit (piFan (F := F)) := by
  classical
  refine
    { lift := fun s => piLift (F := F) (fun i => s.π.app ⟨i⟩)
      fac := ?_
      uniq := ?_ }
  · intro s i
    simp [piFan, piProj_comp_piLift]
  · intro s m hm
    apply piLift_unique (F := F)
    intro i
    simpa [piFan] using hm ⟨i⟩

/-- The canonical cofan realising the Bourbaki coproduct. -/
noncomputable def sigmaCofan (F : ι → BTop) : Cofan F :=
  Cofan.mk (sigmaObj F) (fun i => sigmaInl (F := F) i)

/-- The canonical cofan is colimiting. -/
noncomputable def isColimit_sigmaCofan (F : ι → BTop) :
    IsColimit (sigmaCofan (F := F)) := by
  classical
  refine
    { desc := fun s => sigmaDesc (F := F) (fun i => s.ι.app ⟨i⟩)
      fac := ?_
      uniq := ?_ }
  · intro s i
    simp [sigmaCofan, sigmaIn_desc]
  · intro s m hm
    apply sigmaDesc_unique (F := F)
    intro i
    simpa [sigmaCofan] using hm ⟨i⟩

noncomputable instance instHasLimits : HasLimits BTop :=
  Adjunction.has_limits_of_equivalence (equivTopCat.functor)

noncomputable instance instHasColimits : HasColimits BTop :=
  Adjunction.has_colimits_of_equivalence (equivTopCat.functor)

end Limits

section Examples

variable {ι : Type v}

example {Z : BTop} (F : ι → BTop) (f : ∀ i, Z ⟶ F i) (i : ι) :
    (piLift (F := F) f ≫ piProj (F := F) i) = f i :=
  piProj_comp_piLift (F := F) f i

example {Z : BTop} (F : ι → BTop) (f : ∀ i, F i ⟶ Z) (i : ι) :
    (sigmaInl (F := F) i ≫ sigmaDesc (F := F) f) = f i :=
  sigmaIn_desc (F := F) f i

example : Limits.HasBinaryProducts BTop := inferInstance

example : Limits.HasCoequalizers BTop := inferInstance

end Examples

end BTop

end

end Topology
end BourbakiStyle
end MyProjects
