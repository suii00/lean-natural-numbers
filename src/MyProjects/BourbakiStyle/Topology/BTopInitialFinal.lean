import MyProjects.BourbakiStyle.Topology.BTopCategory

/-!
# Initial and final topologies in `BTop`

This file follows the exposition in `BTopInitialFinal.tex` and organises
initial and final topologies inside the Bourbaki-flavoured category `BTop`.
We package product- and coproduct-like constructions, show their universal
properties via the forgetful functor to `Type`, and record basic examples such
as quotients and disjoint sums.
-/

open CategoryTheory
open scoped Classical

namespace MyProjects
namespace BourbakiStyle
namespace Topology

universe u v w

namespace BTop

variable {ι : Type v}

section Pi

/-- The dependent product of a family of Bourbaki spaces, realised as an
initial topology with respect to evaluation maps. -/
noncomputable def piObj (F : ι → BTop) : BTop :=
  initial (X := ∀ i, F i) F fun i f => f i

/-- Evaluation morphisms out of the dependent product. -/
noncomputable def piProj (F : ι → BTop) (i : ι) :
    piObj F ⟶ F i :=
  initialProjection (X := ∀ j, F j) F (fun j f => f j) i

@[simp] lemma piProj_apply (F : ι → BTop) (i : ι)
    (f : piObj F) :
    piProj (F := F) i f = f i := rfl

variable {Z : BTop}

/-- Universal property of the dependent product in terms of continuity. -/
lemma continuous_to_pi_iff (F : ι → BTop) (f : Z → piObj F) :
    @Continuous Z (piObj F) (toTopologicalSpace (Z.τ))
        (toTopologicalSpace ((piObj F).τ)) f ↔
      ∀ i,
        @Continuous Z (F i) (toTopologicalSpace (Z.τ))
          (toTopologicalSpace ((F i).τ)) fun z => (f z) i := by
  classical
  simpa [piObj, initial] using
    (initial_continuous_iff (X := ∀ i, F i) (F := F)
      (φ := fun i (g : ∀ j, F j) => g i) (Z := Z) f)

end Pi

section Sigma

/-- The disjoint union (categorical coproduct) of a family of Bourbaki spaces,
realised as a final topology with respect to coproduct injections. -/
noncomputable def sigmaObj (F : ι → BTop) : BTop :=
  final (X := Σ i, F i) F fun i x => ⟨i, x⟩

/-- Coproduct inclusions into the disjoint union. -/
noncomputable def sigmaInl (F : ι → BTop) (i : ι) :
    F i ⟶ sigmaObj F :=
  finalInclusion (X := Σ j, F j) F (fun j x => ⟨j, x⟩) i

@[simp] lemma sigmaInl_apply (F : ι → BTop) (i : ι)
    (x : F i) :
    sigmaInl (F := F) i x = ⟨i, x⟩ := rfl

variable {Z : BTop}

/-- Universal property of the disjoint union in terms of continuity. -/
lemma continuous_from_sigma_iff (F : ι → BTop) (f : sigmaObj F → Z) :
    @Continuous (sigmaObj F) Z (toTopologicalSpace ((sigmaObj F).τ))
        (toTopologicalSpace (Z.τ)) f ↔
      ∀ i,
        @Continuous (F i) Z (toTopologicalSpace ((F i).τ))
          (toTopologicalSpace (Z.τ)) fun x => f ⟨i, x⟩ := by
  classical
  simpa [sigmaObj, final] using
    (final_continuous_iff (X := Σ i, F i) (F := F)
      (ψ := fun i x => ⟨i, x⟩) (Z := Z) f)

end Sigma

section Quotients

variable {X : BTop}

/-- The quotient of a Bourbaki space by a setoid, as a final topology. -/
noncomputable def quotientObj (X : BTop) (r : Setoid X) : BTop :=
  final (X := Quot r) (fun _ : Unit => X)
    (fun _ x => Quot.mk _ x)

/-- The canonical surjection into the quotient object. -/
noncomputable def quotientMap (X : BTop) (r : Setoid X) :
    X ⟶ quotientObj X r :=
  finalInclusion (X := Quot r) (F := fun _ : Unit => X)
    (ψ := fun _ x => Quot.mk _ x) Unit.unit

@[simp] lemma quotientMap_apply (X : BTop) (r : Setoid X)
    (x : X) :
    quotientMap (X := X) r x = Quot.mk _ x := rfl

variable {Z : BTop}

/-- Universal property of the quotient topology in terms of continuity. -/
lemma continuous_from_quotient_iff (X : BTop) (r : Setoid X)
    (f : quotientObj X r → Z) :
    @Continuous (quotientObj X r) Z
        (toTopologicalSpace ((quotientObj X r).τ))
        (toTopologicalSpace (Z.τ)) f ↔
      @Continuous X Z (toTopologicalSpace (X.τ))
        (toTopologicalSpace (Z.τ)) fun x => f (Quot.mk _ x) := by
  classical
  simpa [quotientObj, final] using
    (final_continuous_iff (X := Quot r) (F := fun _ : Unit => X)
      (ψ := fun _ x => Quot.mk _ x) (Z := Z) f)

end Quotients

section Examples

variable {ι : Type v} (F : ι → BTop) {Z : BTop}

example (f : Z → piObj F)
    (hf : ∀ i,
        @Continuous Z (F i) (toTopologicalSpace (Z.τ))
          (toTopologicalSpace ((F i).τ)) fun z => (f z) i) :
    @Continuous Z (piObj F) (toTopologicalSpace (Z.τ))
        (toTopologicalSpace ((piObj F).τ)) f :=
  (continuous_to_pi_iff (Z := Z) (F := F) f).2 hf

example (f : sigmaObj F → Z)
    (hf : ∀ i,
        @Continuous (F i) Z (toTopologicalSpace ((F i).τ))
          (toTopologicalSpace (Z.τ)) fun x => f ⟨i, x⟩) :
    @Continuous (sigmaObj F) Z (toTopologicalSpace ((sigmaObj F).τ))
        (toTopologicalSpace (Z.τ)) f :=
  (continuous_from_sigma_iff (Z := Z) (F := F) f).2 hf

variable (X : BTop) (r : Setoid X) {Z : BTop}

example (f : quotientObj X r → Z)
    (hf : @Continuous X Z (toTopologicalSpace (X.τ))
        (toTopologicalSpace (Z.τ)) fun x => f (Quot.mk _ x)) :
    @Continuous (quotientObj X r) Z
        (toTopologicalSpace ((quotientObj X r).τ))
        (toTopologicalSpace (Z.τ)) f :=
  (continuous_from_quotient_iff (X := X) (r := r) (Z := Z) f).2 hf

end Examples

end BTop

end Topology
end BourbakiStyle
end MyProjects
