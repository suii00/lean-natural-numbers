import Mathlib/Topology/Basic

/-
  Bourbaki-style structured sets via ordered pairs and projections

  We model a topological space as an ordered pair (E, τ) where E is the
  underlying set (type) and τ is the topology on E. Projections π₁, π₂
  extract the carrier and its structure. Morphisms are structure-preserving
  maps (continuous maps). The categorical product is given by the product
  topology, and we prove its universal property via projections.
-/

namespace MyProjects
namespace Topology
namespace A

universe u v w

/- Structured set: a pair (E, τ) with τ a topology on E -/
structure TopPair where
  E  : Type u
  τ  : TopologicalSpace E

namespace TopPair

/- Projections π₁, π₂ reflecting the ordered-pair viewpoint -/
def π₁ (X : TopPair) : Type u := X.E
def π₂ (X : TopPair) : TopologicalSpace X.E := X.τ

/- Morphisms as arrows preserving structure: continuous maps -/
def Hom (X Y : TopPair) := { f : X.E → Y.E // by
  -- supply the topological structure instances locally
  let _ : TopologicalSpace X.E := X.τ
  let _ : TopologicalSpace Y.E := Y.τ
  exact Continuous f }

namespace Hom

/- Coercion to function -/
instance {X Y : TopPair} : Coe (Hom X Y) (X.E → Y.E) where
  coe f := f.1

@[simp] theorem coe_mk {X Y : TopPair} {f : X.E → Y.E}
    (hf : by let _ : TopologicalSpace X.E := X.τ; let _ : TopologicalSpace Y.E := Y.τ; exact Continuous f) :
    ((⟨f, hf⟩ : Hom X Y) : X.E → Y.E) = f := rfl

/- Identity morphism -/
def id (X : TopPair) : Hom X X := by
  classical
  refine ⟨id, ?_⟩
  let _ : TopologicalSpace X.E := X.τ
  simpa using (continuous_id : Continuous (fun x : X.E => x))

/- Composition of morphisms -/
def comp {X Y Z : TopPair} (g : Hom Y Z) (f : Hom X Y) : Hom X Z := by
  classical
  refine ⟨fun x => g.1 (f.1 x), ?_⟩
  let _ : TopologicalSpace X.E := X.τ
  let _ : TopologicalSpace Y.E := Y.τ
  let _ : TopologicalSpace Z.E := Z.τ
  simpa using (g.2.comp f.2)

@[simp] theorem comp_apply {X Y Z : TopPair} (g : Hom Y Z) (f : Hom X Y) (x : X.E) :
    (comp g f : X.E → Z.E) x = g (f x) := rfl

end Hom

/- Product object: the product of pairs with the product topology -/
def prod (X Y : TopPair) : TopPair := by
  classical
  refine ⟨X.E × Y.E, ?_⟩
  -- provide local instances for the factors and use the canonical product topology
  let _ : TopologicalSpace X.E := X.τ
  let _ : TopologicalSpace Y.E := Y.τ
  exact instTopologicalSpaceProd

notation:35 X:35 " ⨯ " Y:35 => prod X Y

/- Projections (π₁, π₂) as morphisms from the product -/
def proj₁ (X Y : TopPair) : Hom (X ⨯ Y) X := by
  classical
  refine ⟨Prod.fst, ?_⟩
  let _ : TopologicalSpace X.E := X.τ
  let _ : TopologicalSpace Y.E := Y.τ
  -- product topology on X×Y inferred from local instances above
  have _ : TopologicalSpace (X.E × Y.E) := instTopologicalSpaceProd
  simpa using (continuous_fst : Continuous (fun p : X.E × Y.E => p.1))

def proj₂ (X Y : TopPair) : Hom (X ⨯ Y) Y := by
  classical
  refine ⟨Prod.snd, ?_⟩
  let _ : TopologicalSpace X.E := X.τ
  let _ : TopologicalSpace Y.E := Y.τ
  have _ : TopologicalSpace (X.E × Y.E) := instTopologicalSpaceProd
  simpa using (continuous_snd : Continuous (fun p : X.E × Y.E => p.2))

/- Pairing: given f : Z → X and g : Z → Y, produce ⟨f, g⟩ : Z → X×Y -/
def pair {X Y Z : TopPair} (f : Hom Z X) (g : Hom Z Y) : Hom Z (X ⨯ Y) := by
  classical
  refine ⟨fun z => (f z, g z), ?_⟩
  let _ : TopologicalSpace X.E := X.τ
  let _ : TopologicalSpace Y.E := Y.τ
  let _ : TopologicalSpace Z.E := Z.τ
  -- product topology on X×Y inferred from local instances above
  have _ : TopologicalSpace (X.E × Y.E) := instTopologicalSpaceProd
  simpa using (f.2.prod_mk g.2)

@[simp] theorem proj₁_pair {X Y Z : TopPair} (f : Hom Z X) (g : Hom Z Y) :
    Hom.comp (proj₁ X Y) (pair f g) = f := by
  classical
  -- extensionality on the underlying function of subtypes
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
    -- equality of subtypes by pointwise equality
    apply Subtype.ext
    funext z
    -- compare via the commuting equalities at point z
    have h₁' := congrArg (fun (k : Hom Z X) => (k : Z.E → X.E) z) h₁
    have h₂' := congrArg (fun (k : Hom Z Y) => (k : Z.E → Y.E) z) h₂
    -- show both coordinates coincide
    -- LHS: (h z).1 = fst (h z) = (proj₁ X Y ∘ h) z
    -- RHS: f z
    have : (Prod.fst (h z), Prod.snd (h z)) = (f z, g z) := by
      -- derive from the component equalities
      have a : (Prod.fst (h z)) = (f z) := by simpa [Hom.comp_apply] using h₁'
      have b : (Prod.snd (h z)) = (g z) := by simpa [Hom.comp_apply] using h₂'
      simpa [a, b]
    simpa using this

/- Product universal property, functional form (equivalence of continuities) -/
theorem product_universal_property {X Y Z : TopPair}
    (f : Z.E → X.E) (g : Z.E → Y.E) :
    (by
      let _ : TopologicalSpace X.E := X.τ
      let _ : TopologicalSpace Y.E := Y.τ
      let _ : TopologicalSpace Z.E := Z.τ
      let _ : TopologicalSpace (X.E × Y.E) := instTopologicalSpaceProd
      exact (Continuous (fun z => (f z, g z))) ↔ (Continuous f ∧ Continuous g)) :=
by
  classical
  -- Provide instances locally
  let _ : TopologicalSpace X.E := X.τ
  let _ : TopologicalSpace Y.E := Y.τ
  let _ : TopologicalSpace Z.E := Z.τ
  let _ : TopologicalSpace (X.E × Y.E) := instTopologicalSpaceProd
  -- Use the standard lemma in mathlib
  simpa using (continuous_prod_mk :
    Continuous (fun z => (f z, g z)) ↔ (Continuous f ∧ Continuous g))

end TopPair

end A
end Topology
end MyProjects
