import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Ring.Basic
/-
  Bourbaki-style structured sets via ordered pairs and projections
  Layer 1: TopPair (space) + morphisms (continuous maps) and product universal property.
  Layer 2: C(X,Y) with induced topology from functions; evaluation continuity; curry/uncurry.
  Layer 3: Topological groups/rings and bundled continuous homs.
  Layer 4: Bourbaki τ-layer: sets-of-sets topology and conversion to/from TopologicalSpace.
-/
namespace MyProjects
universe u v w
/-********************
  LAYER 1: TopPair + product UP
********************-/
/- Structured set: a pair (E, τ) with τ a topology on E -/
structure TopPair where
  E  : Type u
namespace TopPair
/- Projections π₁, π₂ (underlying set and topology) -/
def π₁ (X : TopPair) : Type u := X.E
def π₂ (X : TopPair) : TopologicalSpace X.E := X.τ
/- Morphisms as arrows preserving structure: continuous maps -/
def Hom (X Y : TopPair) := { f : X.E → Y.E // by
  let _ : TopologicalSpace X.E := X.τ
  let _ : TopologicalSpace Y.E := Y.τ
  exact Continuous f }
  refine ⟨Prod.fst, ?_⟩
  let _ : TopologicalSpace X.E := X.τ
  let _ : TopologicalSpace Y.E := Y.τ
  have _ : TopologicalSpace (X.E × Y.E) := instTopologicalSpaceProd
  simpa using (continuous_fst : Continuous (fun p : X.E × Y.E => p.1))
  let _ : TopologicalSpace X.E := X.τ
  let _ : TopologicalSpace Y.E := Y.τ
  let _ : TopologicalSpace Z.E := Z.τ
  have _ : TopologicalSpace (X.E × Y.E) := instTopologicalSpaceProd
  simpa using (f.2.prod_mk g.2)
@[simp] theorem proj₁_pair {X Y Z : TopPair} (f : Hom Z X) (g : Hom Z Y) :
    Hom.comp (proj₁ X Y) (pair f g) = f := by
  classical
  apply Subtype.ext
  funext z; rfl
    -- compare via the commuting equalities at point z
    have h₁' := congrArg (fun (k : Hom Z X) => (k : Z.E → X.E) z) h₁
    have h₂' := congrArg (fun (k : Hom Z Y) => (k : Z.E → Y.E) z) h₂
    have : (Prod.fst (h z), Prod.snd (h z)) = (f z, g z) := by
      have a : (Prod.fst (h z)) = (f z) := by simpa [Hom.comp_apply] using h₁'
      have b : (Prod.snd (h z)) = (g z) := by simpa [Hom.comp_apply] using h₂'
      simpa [a, b]
      exact (Continuous (fun z => (f z, g z))) ↔ (Continuous f ∧ Continuous g)) :=
by
  classical
  let _ : TopologicalSpace X.E := X.τ
  let _ : TopologicalSpace Y.E := Y.τ
  let _ : TopologicalSpace Z.E := Z.τ
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
  let _ : TopologicalSpace X.E := X.τ
  let _ : TopologicalSpace Y.E := Y.τ
  exact TopologicalSpace.induced (fun f : C X Y => (f : X.E → Y.E)) inferInstance
/- Evaluation map and its continuity -/
def eval (X Y : TopPair) : (C X Y × X.E) → Y.E := fun p => p.1 p.2
theorem continuous_eval (X Y : TopPair) : Continuous (eval X Y) := by
  classical
  let _ : TopologicalSpace X.E := X.τ
  let _ : TopologicalSpace Y.E := Y.τ
  -- inclusion C(X,Y) → (X → Y) is continuous by induced topology
  have hIncl : Continuous (fun f : C X Y => (f : X.E → Y.E)) := continuous_induced_dom
  -- build (C×X) → ((X→Y)×X)
  have hProd : Continuous (fun p : (C X Y × X.E) => ((p.1 : X.E → Y.E), p.2)) := by
    refine (hIncl.comp (continuous_fst)).prod_mk continuous_snd
  -- evaluation on the ambient function space is continuous
  have hEv : Continuous (fun q : (X.E → Y.E) × X.E => q.1 q.2) := continuous_eval
  exact hEv.comp hProd
/- Uncurry: C(X, C(Y, Z)) → C(X×Y, Z) is continuous under our topologies -/
def uncurry {X Y Z : TopPair} (F : C X (C Y Z)) : C (X ⨯ Y) Z := by
  classical
  -- underlying function
  refine ⟨(fun p => (F p.1) p.2), ?_⟩
  -- prove continuity via evaluation continuity
  let _ : TopologicalSpace X.E := X.τ
  let _ : TopologicalSpace Y.E := Y.τ
  let _ : TopologicalSpace Z.E := Z.τ
  -- map into ((Y→Z) × Y)
  have hIncl : Continuous (fun f : C Y Z => (f : Y.E → Z.E)) := continuous_induced_dom
  have h3 : Continuous (fun p : (X.E × Y.E) => ((F p.1 : Y.E → Z.E), p.2)) := by
    exact (hIncl.comp (F.2.comp continuous_fst)).prod_mk continuous_snd
  -- evaluation on ambient function space is continuous
  exact (continuous_eval).comp h3
/- Curry: C(X×Y, Z) → C(X, C(Y, Z)) with continuity -/
def curry {X Y Z : TopPair} (f : C (X ⨯ Y) Z) : C X (C Y Z) := by
  classical
  -- define the pointwise map X → C(Y,Z)
  refine ⟨(fun x => ⟨(fun y => f (x, y)), ?_⟩), ?_⟩
  · -- inner continuity: Y → Z, y ↦ f (x, y)
    let _ : TopologicalSpace X.E := X.τ
    let _ : TopologicalSpace Y.E := Y.τ
    let _ : TopologicalSpace Z.E := Z.τ
    -- map y ↦ (x, y) is continuous
    have hx : Continuous (fun y : Y.E => (x, y)) := continuous_const.prod_mk continuous_id
    simpa using f.2.comp hx
  · -- outer continuity: X → C(Y,Z) with induced topology on C(Y,Z)
    let _ : TopologicalSpace X.E := X.τ
    let _ : TopologicalSpace Y.E := Y.τ
    let _ : TopologicalSpace Z.E := Z.τ
    -- To show continuity into an induced codomain, it suffices to compose with the inclusion
    -- X → (Y → Z), x ↦ (y ↦ f (x, y)) is continuous by `continuous_pi`
    refine (continuous_induced_rng.mpr ?_)
    -- Show continuity of x ↦ (y ↦ f (x,y)) in the Π-topology
    -- by checking each coordinate y
    refine continuous_pi.mpr ?_
    intro y
    have hy : Continuous (fun x : X.E => (x, y)) := continuous_id.prod_mk continuous_const
    simpa using f.2.comp hy
end TopPair
/********************
  LAYER 3: Topological groups/rings and continuous hom bundles
********************/
namespace TopGrp
/- A Bourbaki-style pair enriched with group + topological group structure -/
structure Pair where
  E   : Type u
  τ   : TopologicalSpace E
  grp : Group E
  tgrp : by let _ : TopologicalSpace E := τ; exact TopologicalGroup E
/- Bundled continuous monoid hom as morphisms -/
def Hom (X Y : Pair) := { φ : MonoidHom X.E Y.E // by
  let _ : TopologicalSpace X.E := X.τ
  let _ : TopologicalSpace Y.E := Y.τ
  let _ : Group X.E := X.grp
  let _ : Group Y.E := Y.grp
  exact Continuous φ }
namespace Hom
instance {X Y : Pair} : Coe (Hom X Y) (X.E → Y.E) where
  coe h := h.1
/- identity -/
def id (X : Pair) : Hom X X := by
  classical
  let _ : Group X.E := X.grp
  refine ⟨MonoidHom.id X.E, ?_⟩
  let _ : TopologicalSpace X.E := X.τ
  simpa using (continuous_id : Continuous (fun x : X.E => x))
/- composition -/
def comp {X Y Z : Pair} (g : Hom Y Z) (f : Hom X Y) : Hom X Z := by
  classical
  let _ : Group X.E := X.grp
  let _ : Group Y.E := Y.grp
  let _ : Group Z.E := Z.grp
  refine ⟨(g.1.comp f.1), ?_⟩
  let _ : TopologicalSpace X.E := X.τ
  let _ : TopologicalSpace Y.E := Y.τ
  let _ : TopologicalSpace Z.E := Z.τ
  simpa using g.2.comp f.2
/- product object and projections -/
def prod (X Y : Pair) : Pair := by
  classical
  refine ⟨X.E × Y.E, ?_, ?_, ?_⟩
  · let _ : TopologicalSpace X.E := X.τ; let _ : TopologicalSpace Y.E := Y.τ; exact instTopologicalSpaceProd
  · -- product group instance
    have _ : Group X.E := X.grp
    have _ : Group Y.E := Y.grp
    exact (inferInstance : Group (X.E × Y.E))
  · let _ : TopologicalSpace X.E := X.τ; let _ : TopologicalSpace Y.E := Y.τ
    let _ : Group X.E := X.grp; let _ : Group Y.E := Y.grp
    exact (inferInstance : TopologicalGroup (X.E × Y.E))
notation:35 X:35 " ⨯g " Y:35 => prod X Y
private def fstMonoidHom {A B : Type*} [Mul A] [Mul B] : MonoidHom (A × B) A where
  toFun := Prod.fst
  map_one' := rfl
  map_mul' := by intro x y; rfl
private def sndMonoidHom {A B : Type*} [Mul A] [Mul B] : MonoidHom (A × B) B where
  toFun := Prod.snd
  map_one' := rfl
  map_mul' := by intro x y; rfl
def proj₁ (X Y : Pair) : Hom (X ⨯g Y) X := by
  classical
  let _ : Group X.E := X.grp; let _ : Group Y.E := Y.grp
  refine ⟨fstMonoidHom, ?_⟩
  let _ : TopologicalSpace X.E := X.τ; let _ : TopologicalSpace Y.E := Y.τ
  have _ : TopologicalSpace (X.E × Y.E) := instTopologicalSpaceProd
  simpa using (continuous_fst : Continuous (fun p : X.E × Y.E => p.1))
def proj₂ (X Y : Pair) : Hom (X ⨯g Y) Y := by
  classical
  let _ : Group X.E := X.grp; let _ : Group Y.E := Y.grp
  refine ⟨sndMonoidHom, ?_⟩
  let _ : TopologicalSpace X.E := X.τ; let _ : TopologicalSpace Y.E := Y.τ
  have _ : TopologicalSpace (X.E × Y.E) := instTopologicalSpaceProd
  simpa using (continuous_snd : Continuous (fun p : X.E × Y.E => p.2))
/- pairing of homs -/
def pair {X Y Z : Pair} (f : Hom Z X) (g : Hom Z Y) : Hom Z (X ⨯g Y) := by
  classical
  let _ : Group X.E := X.grp; let _ : Group Y.E := Y.grp; let _ : Group Z.E := Z.grp
  refine ⟨{
    toFun := fun z => (f z, g z)
    map_one' := by simp
    map_mul' := by intro a b; ext <;> simp
  }, ?_⟩
  let _ : TopologicalSpace X.E := X.τ; let _ : TopologicalSpace Y.E := Y.τ; let _ : TopologicalSpace Z.E := Z.τ
  have _ : TopologicalSpace (X.E × Y.E) := instTopologicalSpaceProd
  exact f.2.prod_mk g.2
end Hom
end TopGrp
namespace TopRing
/- Bourbaki-style pair for rings with topological ring structure -/
structure Pair where
  E   : Type u
  τ   : TopologicalSpace E
  ring : Ring E
  tring : by let _ : TopologicalSpace E := τ; exact TopologicalRing E
/- Bundled continuous ring hom -/
def Hom (X Y : Pair) := { φ : RingHom X.E Y.E // by
  let _ : TopologicalSpace X.E := X.τ
  let _ : TopologicalSpace Y.E := Y.τ
  let _ : Ring X.E := X.ring
  let _ : Ring Y.E := Y.ring
  exact Continuous φ }
namespace Hom
instance {X Y : Pair} : Coe (Hom X Y) (X.E → Y.E) where coe h := h.1
def id (X : Pair) : Hom X X := by
  classical
  let _ : Ring X.E := X.ring
  refine ⟨RingHom.id X.E, ?_⟩
  let _ : TopologicalSpace X.E := X.τ
  simpa using (continuous_id : Continuous (fun x : X.E => x))
def comp {X Y Z : Pair} (g : Hom Y Z) (f : Hom X Y) : Hom X Z := by
  classical
  let _ : Ring X.E := X.ring; let _ : Ring Y.E := Y.ring; let _ : Ring Z.E := Z.ring
  refine ⟨(g.1.comp f.1), ?_⟩
  let _ : TopologicalSpace X.E := X.τ; let _ : TopologicalSpace Y.E := Y.τ; let _ : TopologicalSpace Z.E := Z.τ
  simpa using g.2.comp f.2
/- product and projections for rings -/
def prod (X Y : Pair) : Pair := by
  classical
  refine ⟨X.E × Y.E, ?_, ?_, ?_⟩
  · let _ : TopologicalSpace X.E := X.τ; let _ : TopologicalSpace Y.E := Y.τ; exact instTopologicalSpaceProd
  · -- ring instance on product
    have _ : Ring X.E := X.ring
    have _ : Ring Y.E := Y.ring
    exact (inferInstance : Ring (X.E × Y.E))
  · let _ : TopologicalSpace X.E := X.τ; let _ : TopologicalSpace Y.E := Y.τ
    let _ : Ring X.E := X.ring; let _ : Ring Y.E := Y.ring
    exact (inferInstance : TopologicalRing (X.E × Y.E))
notation:35 X:35 " ⨯r " Y:35 => prod X Y
end Hom
end TopRing
/-********************
  LAYER 4: Bourbaki τ-layer (sets-of-sets) + conversions
********************-/
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
  isOpen_empty := τ.isOpen_empty
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
