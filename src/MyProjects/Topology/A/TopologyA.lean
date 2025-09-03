import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Prod

/-
  Bourbaki-style structured sets via ordered pairs and projections

  Layer 1: TopPair (space) + morphisms (continuous maps) and product universal property.
  Layer 2: C(X,Y) with induced topology from functions; evaluation continuity; curry/uncurry.
  Layer 4: Bourbaki tau-layer: sets-of-sets topology and conversion to/from TopologicalSpace.
-/

namespace MyProjects
namespace Topology
namespace A

universe u v w

/********************
  LAYER 1: TopPair + product UP
********************/

/- Structured set: a pair (E, tau) with tau a topology on E -/
structure TopPair where
  E   : Type u
  tau : TopologicalSpace E

namespace TopPair

/- Morphisms as arrows preserving structure: continuous maps -/
def Hom (X Y : TopPair) := { f : X.E → Y.E // by
  let _ : TopologicalSpace X.E := X.tau
  let _ : TopologicalSpace Y.E := Y.tau
  exact Continuous f }

namespace Hom

/- Coercion to function -/
instance {X Y : TopPair} : Coe (Hom X Y) (X.E → Y.E) where
  coe f := f.1

@[simp] theorem coe_mk {X Y : TopPair} {f : X.E → Y.E}
    (hf : by let _ : TopologicalSpace X.E := X.tau; let _ : TopologicalSpace Y.E := Y.tau; exact Continuous f) :
    ((⟨f, hf⟩ : Hom X Y) : X.E → Y.E) = f := rfl

/- Identity morphism -/
def id (X : TopPair) : Hom X X := by
  classical
  refine ⟨(fun x : X.E => x), ?_⟩
  let _ : TopologicalSpace X.E := X.tau
  simpa using (continuous_id : Continuous (fun x : X.E => x))

/- Composition of morphisms -/
def comp {X Y Z : TopPair} (g : Hom Y Z) (f : Hom X Y) : Hom X Z := by
  classical
  refine ⟨fun x => g.1 (f.1 x), ?_⟩
  let _ : TopologicalSpace X.E := X.tau
  let _ : TopologicalSpace Y.E := Y.tau
  let _ : TopologicalSpace Z.E := Z.tau
  simpa using (g.2.comp f.2)

@[simp] theorem comp_apply {X Y Z : TopPair} (g : Hom Y Z) (f : Hom X Y) (x : X.E) :
    (comp g f : X.E → Z.E) x = g (f x) := rfl

end Hom

/- Product object: the product of pairs with the product topology -/
def prod (X Y : TopPair) : TopPair := by
  classical
  refine ⟨X.E × Y.E, ?_⟩
  let _ : TopologicalSpace X.E := X.tau
  let _ : TopologicalSpace Y.E := Y.tau
  exact instTopologicalSpaceProd

notation:35 X:35 " ⨯ " Y:35 => prod X Y

/- Projections as morphisms from the product -/
def proj₁ (X Y : TopPair) : Hom (X ⨯ Y) X := by
  classical
  refine ⟨Prod.fst, ?_⟩
  let _ : TopologicalSpace X.E := X.tau
  let _ : TopologicalSpace Y.E := Y.tau
  have _ : TopologicalSpace (X.E × Y.E) := instTopologicalSpaceProd
  simpa using (continuous_fst : Continuous (fun p : X.E × Y.E => p.1))

def proj₂ (X Y : TopPair) : Hom (X ⨯ Y) Y := by
  classical
  refine ⟨Prod.snd, ?_⟩
  let _ : TopologicalSpace X.E := X.tau
  let _ : TopologicalSpace Y.E := Y.tau
  have _ : TopologicalSpace (X.E × Y.E) := instTopologicalSpaceProd
  simpa using (continuous_snd : Continuous (fun p : X.E × Y.E => p.2))

/- Pairing: given f : Z → X and g : Z → Y, produce ⟨f, g⟩ : Z → X×Y -/
def pair {X Y Z : TopPair} (f : Hom Z X) (g : Hom Z Y) : Hom Z (X ⨯ Y) := by
  classical
  refine ⟨fun z => (f z, g z), ?_⟩
  let _ : TopologicalSpace X.E := X.tau
  let _ : TopologicalSpace Y.E := Y.tau
  let _ : TopologicalSpace Z.E := Z.tau
  have _ : TopologicalSpace (X.E × Y.E) := instTopologicalSpaceProd
  simpa using (f.2.prodMk g.2)

@[simp] theorem proj₁_pair {X Y Z : TopPair} (f : Hom Z X) (g : Hom Z Y) :
    Hom.comp (proj₁ X Y) (pair f g) = f := by
  classical
  apply Subtype.ext
  funext z; rfl

@[simp] theorem proj₂_pair {X Y Z : TopPair} (f : Hom Z X) (g : Hom Z Y) :
    Hom.comp (proj₂ X Y) (pair f g) = g := by
  classical
  apply Subtype.ext
  funext z; rfl

/- Universal property of the product: existence and uniqueness -/
theorem existsUnique_lift_to_prod {X Y Z : TopPair}
    (f : Hom Z X) (g : Hom Z Y) :
    ∃! h : Hom Z (X ⨯ Y),
      Hom.comp (proj₁ X Y) h = f ∧ Hom.comp (proj₂ X Y) h = g := by
  classical
  refine ⟨pair f g, ?_, ?_⟩
  · exact ⟨proj₁_pair f g, proj₂_pair f g⟩
  · intro h hh
    rcases hh with ⟨h₁, h₂⟩
    apply Subtype.ext
    funext z
    have h₁' := congrArg (fun (k : Hom Z X) => (k : Z.E → X.E) z) h₁
    have h₂' := congrArg (fun (k : Hom Z Y) => (k : Z.E → Y.E) z) h₂
    have : (Prod.fst (h z), Prod.snd (h z)) = (f z, g z) := by
      have a : (Prod.fst (h z)) = (f z) := by simpa [Hom.comp_apply] using h₁'
      have b : (Prod.snd (h z)) = (g z) := by simpa [Hom.comp_apply] using h₂'
      simpa [a, b]
    simpa using this

/- Product universal property, functional form (equivalence of continuities) -/
theorem product_universal_property {X Y Z : TopPair}
    (f : Z.E → X.E) (g : Z.E → Y.E) :
    Continuous (fun z => (f z, g z)) ↔ (Continuous f ∧ Continuous g) := by
  classical
  let _ : TopologicalSpace X.E := X.tau
  let _ : TopologicalSpace Y.E := Y.tau
  let _ : TopologicalSpace Z.E := Z.tau
  let _ : TopologicalSpace (X.E × Y.E) := instTopologicalSpaceProd
  simpa using (continuous_prod_mk :
    Continuous (fun z => (f z, g z)) ↔ (Continuous f ∧ Continuous g))

/********************
  LAYER 2: C(X,Y) with induced topology; eval/curry/uncurry
********************/

/- Alias for the continuous maps: this is C(X,Y) -/
abbrev C (X Y : TopPair) := Hom X Y

/- Choose the induced topology from the full function space X → Y
   so that the inclusion C(X,Y) ↪ (X → Y) is continuous. -/
instance instTopC (X Y : TopPair) : TopologicalSpace (C X Y) := by
  let _ : TopologicalSpace X.E := X.tau
  let _ : TopologicalSpace Y.E := Y.tau
  exact TopologicalSpace.induced (fun f : C X Y => (f : X.E → Y.E)) inferInstance

/- Package C(Y,Z) itself as a TopPair so we can write C(X, C(Y,Z)) as Hom X (Cpair Y Z). -/
def Cpair (Y Z : TopPair) : TopPair :=
  { E := C Y Z, tau := (instTopC Y Z) }

/- Evaluation map and its continuity -/
def eval (X Y : TopPair) : (C X Y × X.E) → Y.E := fun p => p.1 p.2

theorem continuous_evalC (X Y : TopPair) : Continuous (eval X Y) := by
  classical
  let _ : TopologicalSpace X.E := X.tau
  let _ : TopologicalSpace Y.E := Y.tau
  -- inclusion C(X,Y) → (X → Y) is continuous by induced topology
  have hIncl : Continuous (fun f : C X Y => (f : X.E → Y.E)) := continuous_induced_dom
  -- build (C×X) → ((X→Y)×X)
  have hProd : Continuous (fun p : (C X Y × X.E) => ((p.1 : X.E → Y.E), p.2)) := by
    exact (hIncl.comp continuous_fst).prodMk continuous_snd
  -- evaluation on the ambient function space is continuous
  have hEv : Continuous (fun q : (X.E → Y.E) × X.E => q.1 q.2) := continuous_eval
  exact hEv.comp hProd

/- Curry/uncurry as continuous maps -/
def uncurry {X Y Z : TopPair} (F : C X (Cpair Y Z)) : C (X ⨯ Y) Z := by
  classical
  refine ⟨(fun p => (F p.1) p.2), ?_⟩
  let _ : TopologicalSpace X.E := X.tau
  let _ : TopologicalSpace Y.E := Y.tau
  let _ : TopologicalSpace Z.E := Z.tau
  -- map into ((Y→Z) × Y)
  have hIncl : Continuous (fun f : C Y Z => (f : Y.E → Z.E)) := continuous_induced_dom
  have h3 : Continuous (fun p : (X.E × Y.E) => ((F p.1 : Y.E → Z.E), p.2)) := by
    exact (hIncl.comp (F.2.comp continuous_fst)).prodMk continuous_snd
  -- evaluation on ambient function space is continuous
  exact (continuous_eval).comp h3

def curry {X Y Z : TopPair} (f : C (X ⨯ Y) Z) : C X (Cpair Y Z) := by
  classical
  -- define the pointwise map X → C(Y,Z)
  refine ⟨(fun x => ⟨(fun y => f (x, y)), ?_⟩), ?_⟩
  · -- inner continuity: Y → Z, y ↦ f (x, y)
    let _ : TopologicalSpace X.E := X.tau
    let _ : TopologicalSpace Y.E := Y.tau
    let _ : TopologicalSpace Z.E := Z.tau
    -- map y ↦ (x, y) is continuous
    have hx : Continuous (fun y : Y.E => (x, y)) := continuous_const.prodMk continuous_id
    simpa using f.2.comp hx
  · -- outer continuity: X → C(Y,Z) with induced topology on C(Y,Z)
    let _ : TopologicalSpace X.E := X.tau
    let _ : TopologicalSpace Y.E := Y.tau
    let _ : TopologicalSpace Z.E := Z.tau
    refine (continuous_induced_rng.mpr ?_)
    -- Show continuity of x ↦ (y ↦ f (x,y)) in the Π-topology by checking each y
    refine continuous_pi.mpr ?_
    intro y
    have hy : Continuous (fun x : X.E => (x, y)) := continuous_id.prodMk continuous_const
    simpa using f.2.comp hy

end TopPair

/********************
  LAYER 4: Bourbaki tau-layer (sets-of-sets) + conversions
********************/

namespace TauLayer

/- Bourbaki-style topology as a family of subsets satisfying axioms -/
structure Tau (E : Type u) where
  t : Set (Set E)
  isOpen_univ : Set.univ ∈ t
  isOpen_empty : (∅ : Set E) ∈ t
  isOpen_sUnion : ∀ (A : Set (Set E)), A ⊆ t → sUnion A ∈ t
  isOpen_inter : ∀ {U V : Set E}, U ∈ t → V ∈ t → (U ∩ V) ∈ t

namespace Tau

variable {E : Type u}

/- Convert Tau → TopologicalSpace -/
def toTopologicalSpace (τ : Tau E) : TopologicalSpace E where
  IsOpen s := s ∈ τ.t
  isOpen_univ := τ.isOpen_univ
  isOpen_inter := by
    intro s t hs ht; simpa using τ.isOpen_inter hs ht
  isOpen_sUnion := by
    intro S hS; simpa using τ.isOpen_sUnion S hS

/- Convert TopologicalSpace → Tau -/
def ofTopologicalSpace (tE : TopologicalSpace E) : Tau E where
  t := {s | @IsOpen E tE s}
  isOpen_univ := by change IsOpen (Set.univ : Set E); simpa
  isOpen_empty := by change IsOpen (∅ : Set E); simpa
  isOpen_sUnion := by
    intro A hA
    change IsOpen (⋃₀ A)
    exact isOpen_sUnion (by intro s hs; exact hA hs)
  isOpen_inter := by
    intro U V hU hV
    change IsOpen (U ∩ V)
    exact IsOpen.inter hU hV

/- Round-trip lemmas on opens -/
theorem to_from_isOpen {tE : TopologicalSpace E} {s : Set E} :
    (IsOpen s) ↔ s ∈ (ofTopologicalSpace (E:=E) tE).t := Iff.rfl

theorem from_to_isOpen {τ : Tau E} {s : Set E} :
    (s ∈ τ.t) ↔ @IsOpen E (toTopologicalSpace τ) s := Iff.rfl

/- Basic constructors on Tau using TopologicalSpace operations -/
def induced {E F : Type u} (f : E → F) (τF : Tau F) : Tau E :=
  ofTopologicalSpace (TopologicalSpace.induced f (toTopologicalSpace τF))

def coinduced {E F : Type u} (f : E → F) (τE : Tau E) : Tau F :=
  ofTopologicalSpace (TopologicalSpace.coinduced f (toTopologicalSpace τE))

def prod {X Y : Type u} (τX : Tau X) (τY : Tau Y) : Tau (X × Y) :=
  ofTopologicalSpace (by
    let _ := toTopologicalSpace τX
    let _ := toTopologicalSpace τY
    exact instTopologicalSpaceProd)

def generateFrom {E : Type u} (S : Set (Set E)) : Tau E :=
  ofTopologicalSpace (TopologicalSpace.generateFrom S)

end Tau

end TauLayer

end A
end Topology
end MyProjects
