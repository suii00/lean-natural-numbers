/-
  Topology B — Bourbaki-Style Synthesis

  This module mirrors the Bourbaki-flavoured constructions from the archive file
  `Archive/Topology/2025-09-04/TopologyB_Bourbaki2.lean`, recreating them inside the
  `MyProjects.BourbakiStyle.Topology` namespace so that the archive import is no
  longer required.  The implementations are streamlined but keep the same
  universal-property spirit: products defined via projections, covering maps
  sketched through evenly-covered neighborhoods, and Stone–Čech compactification
  framed by its universal arrow.

  Sections
  * `ProductUniversality`: continuity of projections, componentwise test, and
    existence/uniqueness of mediating maps, plus the categorical adjunction
    Δ ⊣ × in `TopCat`.
  * `ExponentialLaw`: currying/uncurrying, the exponential homeomorphism of
    continuous map spaces, and continuity of evaluation.
  * `CoveringSpaces`: a skeleton for covering maps via evenly-covered data and
    path lifting helpers.
  * `StoneCech`: an abstract Stone–Čech compactification interface together with
    constructions from trivial compact Hausdorff spaces and the mathlib
    `StoneCech` object.
-/

import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Path
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Compactification.StoneCech

open CategoryTheory
open scoped Topology

namespace MyProjects
namespace BourbakiStyle
namespace Topology

/-! ## A. Product universality via projections -/

section ProductUniversality

variable {T X Y : Type*}
variable [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace Y]

/-- First projection from a product, in Bourbaki's ordered-pair viewpoint. -/
def π₁ : X × Y → X := fun p => p.1

/-- Second projection from a product. -/
def π₂ : X × Y → Y := fun p => p.2

lemma continuous_π₁ : Continuous (π₁ : X × Y → X) := by
  simpa [π₁] using continuous_fst

lemma continuous_π₂ : Continuous (π₂ : X × Y → Y) := by
  simpa [π₂] using continuous_snd

/-- A map into a product is continuous iff its components are continuous. -/
theorem continuous_iff_proj (h : T → X × Y) :
    Continuous h ↔
      Continuous (fun t => (h t).1) ∧ Continuous (fun t => (h t).2) := by
  constructor
  · intro hh
    exact ⟨continuous_fst.comp hh, continuous_snd.comp hh⟩
  · rintro ⟨h₁, h₂⟩
    simpa using h₁.prodMk h₂

/-- Mediating map into a product exists and is unique. -/
theorem exists_unique_lift_to_prod {f : T → X} {g : T → Y}
    (hf : Continuous f) (hg : Continuous g) :
    ∃! h : T → X × Y,
      Continuous h ∧ (∀ t, (h t).1 = f t) ∧ (∀ t, (h t).2 = g t) := by
  refine ⟨fun t => (f t, g t), ?exist, ?uniq⟩
  · refine And.intro ?hcont ?hproj
    · simpa using hf.prodMk hg
    · exact ⟨fun t => rfl, fun t => rfl⟩
  · intro h hh
    rcases hh with ⟨_hc, hfst, hsnd⟩
    ext t <;> [simpa using hfst t, simpa using hsnd t]

end ProductUniversality

section TopCatAdjunction

/-- Δ duplicates objects and morphisms. -/
noncomputable def deltaTop : TopCat ⥤ TopCat × TopCat where
  obj X := ⟨X, X⟩
  map {X Y} (f : X ⟶ Y) := ⟨f, f⟩
  map_id X := by
    ext <;> rfl
  map_comp {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) := by
    ext <;> rfl

/-- Binary product functor on `TopCat`. -/
noncomputable def prodTop : TopCat × TopCat ⥤ TopCat where
  obj X := TopCat.of (X.1 × X.2)
  map {X Y} (f : X ⟶ Y) :=
    (⟨(fun p : X.1 × X.2 => (f.1 p.1, f.2 p.2)), by
      have h1 : Continuous fun p : X.1 × X.2 => f.1 p.1 := by
        simpa using (f.1.continuous.comp continuous_fst)
      have h2 : Continuous fun p : X.1 × X.2 => f.2 p.2 := by
        simpa using (f.2.continuous.comp continuous_snd)
      exact h1.prodMk h2⟩ : ContinuousMap (X.1 × X.2) (Y.1 × Y.2))
  map_id X := by
    ext p <;> rfl
  map_comp {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) := by
    ext p <;> rfl

/-- Hom-set equivalence witnessing Δ ⊣ ×. -/
noncomputable def homEquivDeltaProd (X : TopCat) (YZ : TopCat × TopCat) :
    ((deltaTop.obj X) ⟶ YZ) ≃ (X ⟶ prodTop.obj YZ) :=
{ toFun := fun fg =>
    (⟨(fun x => (fg.1 x, fg.2 x)), by
      simpa using (fg.1.continuous.prodMk fg.2.continuous)⟩ :
      ContinuousMap X (YZ.1 × YZ.2))
, invFun := fun h =>
    ((⟨(fun x => (h x).1), by
        simpa using (continuous_fst.comp h.continuous)⟩ : ContinuousMap X YZ.1),
     (⟨(fun x => (h x).2), by
        simpa using (continuous_snd.comp h.continuous)⟩ : ContinuousMap X YZ.2))
, left_inv := by
    intro fg; ext x <;> rfl
, right_inv := by
    intro h; ext p <;> rfl }

end TopCatAdjunction

/-! ## A′. Exponential law -/

section ExponentialLaw

variable {X Y Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Currying plain functions. -/
def curry (f : X × Y → Z) : X → Y → Z := fun x y => f (x, y)

/-- Uncurrying plain functions. -/
def uncurry (g : X → Y → Z) : X × Y → Z := fun p => g p.1 p.2

@[simp] lemma curry_uncurry (g : X → Y → Z) : curry (uncurry g) = g := rfl
@[simp] lemma uncurry_curry (f : X × Y → Z) : uncurry (curry f) = f := by
  funext p; cases p; rfl

variable [LocallyCompactSpace X] [LocallyCompactSpace Y]

/-- Exponential homeomorphism for spaces of continuous maps. -/
noncomputable def exponential_homeo :
    ContinuousMap (X × Y) Z ≃ₜ ContinuousMap X (ContinuousMap Y Z) :=
  Homeomorph.curry (X:=X) (Y:=Y) (Z:=Z)

@[simp] lemma exponential_homeo_apply
    (F : ContinuousMap (X × Y) Z) (x : X) (y : Y) :
    exponential_homeo (X:=X) (Y:=Y) (Z:=Z) F x y = F (x, y) := rfl

@[simp] lemma exponential_homeo_symm_apply
    (G : ContinuousMap X (ContinuousMap Y Z)) (p : X × Y) :
    (exponential_homeo (X:=X) (Y:=Y) (Z:=Z)).symm G p = G p.1 p.2 := rfl

/-- Continuity of the evaluation map under the compact-open topology. -/
theorem continuous_eval [LocallyCompactPair Y Z] :
    Continuous (fun p : ContinuousMap Y Z × Y => p.1 p.2) := by
  simpa using (ContinuousEval.continuous_eval :
    Continuous (fun p : ContinuousMap Y Z × Y => p.1 p.2))

end ExponentialLaw

/-! ## B. Covering spaces skeleton -/

section CoveringSpaces

variable {E B : Type*}
variable [TopologicalSpace E] [TopologicalSpace B]

@[inline] def I0 : unitInterval := ⟨0, by simp⟩
@[inline] def I1 : unitInterval := ⟨1, by simp⟩

@[simp] lemma coe_I0 : ((I0 : unitInterval) : ℝ) = 0 := rfl
@[simp] lemma coe_I1 : ((I1 : unitInterval) : ℝ) = 1 := rfl

@[simp] lemma path_map_apply
  {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {x y : X} (γ : Path x y) (f : X → Y) (hf : Continuous f) (t : ↑unitInterval) :
  (γ.map (f := f) hf) t = f (γ t) := rfl

@[simp] lemma path_source_I0
  {X : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y) :
  γ I0 = x := by simpa [I0] using γ.source

@[simp] lemma path_target_I1
  {X : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y) :
  γ I1 = y := by simpa [I1] using γ.target

/-- Bourbaki-flavoured definition of a covering map. -/
structure CoveringMap (p : E → B) : Prop where
  continuous : Continuous p
  evenlyCovered :
    ∀ b : B,
      ∃ (U : Set B), IsOpen U ∧ b ∈ U ∧
        ∃ (I : Type*) (_ : TopologicalSpace I) (_ : DiscreteTopology I),
        ∃ e : (Subtype fun e : E => p e ∈ U) ≃ₜ ((Subtype fun x : B => x ∈ U) × I),
          ∀ s, ((e s).1 : Subtype fun x : B => x ∈ U).1 = p s.1

/-- Evenly-covered data packaged for re-use. -/
structure EvenlyCoveredAt (p : E → B) (b : B) where
  U : Set B
  isOpenU : IsOpen U
  memU : b ∈ U
  I : Type*
  instTopI : TopologicalSpace I
  instDiscI : @DiscreteTopology I instTopI
  e : (Subtype fun e : E => p e ∈ U) ≃ₜ ((Subtype fun x : B => x ∈ U) × I)
  base : ∀ s,
    ((e s).1 : Subtype fun x : B => x ∈ U).1 = p s.1

namespace EvenlyCoveredAt

variable {p : E → B} {b : B}

instance instTopologicalSpace_I (d : EvenlyCoveredAt p b) :
    TopologicalSpace d.I := d.instTopI

instance instDiscreteTopology_I (d : EvenlyCoveredAt p b) :
    DiscreteTopology d.I := d.instDiscI

/-- The `i`-th sheet over `U`. -/
noncomputable def sheet (d : EvenlyCoveredAt p b)
    (i : d.I) : (Subtype fun x : B => x ∈ d.U)
      → (Subtype fun e : E => p e ∈ d.U) :=
  fun u => d.e.symm (u, i)

lemma sheet_base (d : EvenlyCoveredAt p b) (i : d.I)
    (u : Subtype fun x : B => x ∈ d.U) :
    p ((d.sheet i u).1) = u.1 := by
  classical
  set s := d.e.symm (u, i)
  have hs : d.e s = (u, i) := by
    subst s; simpa using d.e.left_inv (u, i)
  have hb := d.base s
  have : u.1 = p s.1 := by simpa [hs] using hb
  simpa [s, sheet] using this.symm

lemma continuous_sheet_val (d : EvenlyCoveredAt p b) (i : d.I) :
    Continuous (fun u : Subtype fun x : B => x ∈ d.U => ((d.sheet i u).1)) := by
  classical
  have hpair : Continuous fun u : Subtype fun x : B => x ∈ d.U => (u, i) := by
    have h1 : Continuous fun u : Subtype fun x : B => x ∈ d.U => u := continuous_id
    have h2 : Continuous fun _u : Subtype fun x : B => x ∈ d.U => i := continuous_const
    simpa using h1.prodMk h2
  have hsymm : Continuous d.e.symm := d.e.continuous_symm
  have hcomp : Continuous (fun u : Subtype fun x : B => x ∈ d.U => d.e.symm (u, i)) :=
    hsymm.comp hpair
  simpa [sheet] using (continuous_subtype_val.comp hcomp)

/-- Inclusion of `U` into the base. -/
noncomputable def inclB (d : EvenlyCoveredAt p b) :
    ContinuousMap (Subtype fun x : B => x ∈ d.U) B :=
  ⟨(fun u => u.1), continuous_subtype_val⟩

/-- Inclusion of the lifted neighborhood into the total space. -/
noncomputable def inclE (d : EvenlyCoveredAt p b) :
    ContinuousMap (Subtype fun e : E => p e ∈ d.U) E :=
  ⟨(fun s => s.1), continuous_subtype_val⟩

/-- The `i`-th sheet as a bundled continuous map. -/
noncomputable def sheetMap (d : EvenlyCoveredAt p b) (i : d.I) :
    ContinuousMap (Subtype fun x : B => x ∈ d.U)
                  (Subtype fun e : E => p e ∈ d.U) :=
  ⟨(fun u => d.e.symm (u, i)), by
    classical
    have hpair : Continuous fun u : Subtype (fun x : B => x ∈ d.U) => (u, i) := by
      have h1 : Continuous fun u : Subtype (fun x : B => x ∈ d.U) => u := continuous_id
      have h2 : Continuous fun _u : Subtype (fun x : B => x ∈ d.U) => i := continuous_const
      simpa using h1.prodMk h2
    have hcont : Continuous (fun u : Subtype (fun x : B => x ∈ d.U) => d.e.symm (u, i)) :=
      d.e.continuous_symm.comp hpair
    simpa using hcont⟩

@[simp] lemma sheet_comp_eq_inclB {p : E → B}
    (h : CoveringMap p) (b : B)
    (d : EvenlyCoveredAt p b) (i : d.I) :
    (((⟨p, h.continuous⟩ : ContinuousMap E B)).comp (d.inclE)).comp (d.sheetMap i) =
      d.inclB := by
  classical
  ext u
  change p ((d.sheet i u).1) = u.1
  exact sheet_base (p:=p) (b:=b) d i u

end EvenlyCoveredAt

/-- Extract evenly covered data from a covering map. -/
noncomputable def CoveringMap.evenlyCoveredAt {p : E → B}
    (h : CoveringMap p) (b : B) : EvenlyCoveredAt p b := by
  classical
  rcases h.evenlyCovered b with ⟨U, hUopen, hbmem, I, tI, dI, e, hbase⟩
  refine ⟨U, hUopen, hbmem, I, tI, dI, e, ?_⟩
  intro s
  simpa using hbase s

/-! We record a placeholder for the path lifting theorem, ready for refinement. -/
lemma path_lifting_theorem_skeleton {p : E → B} (h : CoveringMap p) : True := by
  trivial

end CoveringSpaces

/-! ## C. Stone–Čech compactification -/

section StoneCech

variable (X : Type*) [TopologicalSpace X]

/-- Abstract Stone–Čech compactification data. -/
structure StoneCechCompactification where
  βX : Type*
  [instTopβX : TopologicalSpace βX]
  [instCompβX : CompactSpace βX]
  [instT2βX : T2Space βX]
  ι : ContinuousMap X βX
  dense_range : DenseRange (ι : X → βX)
  universal :
    ∀ (K : Type*) [TopologicalSpace K] [CompactSpace K] [T2Space K]
      (f : ContinuousMap X K),
      ∃! F : ContinuousMap βX K,
        F.comp ι = f

variable {X}

attribute [instance] StoneCechCompactification.instTopβX
attribute [instance] StoneCechCompactification.instCompβX
attribute [instance] StoneCechCompactification.instT2βX

/-- The universal arrow `βX → K` extending `f : X → K`. -/
noncomputable def StoneCechCompactification.lift
    (S : StoneCechCompactification X)
    (K : Type*) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (f : ContinuousMap X K) : ContinuousMap S.βX K :=
  Classical.choose (S.universal K f)

@[simp] lemma StoneCechCompactification.lift_comp
    (S : StoneCechCompactification X)
    (K : Type*) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (f : ContinuousMap X K) :
    (S.lift K f).comp S.ι = f :=
  (Classical.choose_spec (S.universal K f)).1

@[simp] lemma StoneCechCompactification.lift_comp_apply
    (S : StoneCechCompactification X)
    (K : Type*) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (f : ContinuousMap X K) (x : X) :
    (S.lift K f).comp S.ι x = f x := by
  have := S.lift_comp (K:=K) f
  exact congrArg (fun g => g x) (show (S.lift K f).comp S.ι = f from this)

lemma StoneCechCompactification.lift_unique
    (S : StoneCechCompactification X)
    (K : Type*) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (f : ContinuousMap X K) {G : ContinuousMap S.βX K}
    (hG : G.comp S.ι = f) :
    G = S.lift K f := by
  classical
  have huniq :=
    (Classical.choose_spec (S.universal K f)).2
  have : G = Classical.choose (S.universal K f) := huniq G hG
  simpa [StoneCechCompactification.lift] using this

/-- Trivial compactification for compact Hausdorff spaces. -/
noncomputable def StoneCechCompactification.trivial
    (X : Type*) [TopologicalSpace X]
    [CompactSpace X] [T2Space X] : StoneCechCompactification X :=
{ βX := X
, instTopβX := inferInstance
, instCompβX := inferInstance
, instT2βX := inferInstance
, ι := ContinuousMap.id X
, dense_range := by
    classical
    simpa using (denseRange_id : DenseRange (fun x : X => x))
, universal := by
    intro K _ _ _ f
    refine ⟨f, ?comp, ?uniq⟩
    · ext x; rfl
    · intro G hG
      ext x
      have := congrArg (fun (h : ContinuousMap X K) => h x) hG
      simpa using this
}

/-- Stone–Čech compactification as provided by mathlib. -/
noncomputable def StoneCechCompactification.fromMathlib :
    StoneCechCompactification X :=
{ βX := StoneCech X
, instTopβX := inferInstance
, instCompβX := inferInstance
, instT2βX := inferInstance
, ι := ⟨stoneCechUnit, continuous_stoneCechUnit⟩
, dense_range := by
    simpa using (denseRange_stoneCechUnit : DenseRange (stoneCechUnit : X → StoneCech X))
, universal := by
    intro K _ _ _ f
    classical
    let F : ContinuousMap (StoneCech X) K :=
      ⟨stoneCechExtend (α := X) (β := K) (g := fun x => f x) f.continuous,
        continuous_stoneCechExtend (α := X) (β := K) (g := fun x => f x) f.continuous⟩
    refine ⟨F, ?comp, ?uniq⟩
    · ext x
      simp [F]
    · intro G hG
      have hFcomp : F.comp ⟨stoneCechUnit, continuous_stoneCechUnit⟩ = f := by
        ext x; simp [F]
      have hEq : G.comp ⟨stoneCechUnit, continuous_stoneCechUnit⟩
                = F.comp ⟨stoneCechUnit, continuous_stoneCechUnit⟩ := by
        simpa [hFcomp] using hG
      have hcomp : (G ∘ stoneCechUnit) = (F ∘ stoneCechUnit) := by
        funext x; simpa [Function.comp] using
          congrArg (fun (h : ContinuousMap X K) => h x) hEq
      have hfun : (fun y => G y) = (fun y => F y) :=
        stoneCech_hom_ext (α := X) (β := K)
          G.continuous F.continuous hcomp
      ext y; simpa using congrArg (fun h => h y) hfun
}

/-- Smoke test for the β-rule of the Stone–Čech lift. -/
example {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (f : ContinuousMap X K) (x : X) :
  ((StoneCechCompactification.fromMathlib (X:=X)).lift K f).comp
      (StoneCechCompactification.fromMathlib (X:=X)).ι x = f x := by
  exact
    (StoneCechCompactification.lift_comp_apply
      (S := StoneCechCompactification.fromMathlib (X:=X)) (K:=K) f x)

end StoneCech

end Topology
end BourbakiStyle
end MyProjects
