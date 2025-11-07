import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Basic
import MyProjects.ST.CAT2_complete
import MyProjects.ST.HierarchicalStructureTower
import MyProjects.ST.AdvancedStructureTowerExercises

/-!
# Next Exercises: Universal Behaviour of minLayer

Lean companion to the final section of `Hierarchical_structure_tower.md`.
We isolate the "Bourbaki-style" principles that distinguish trivial versus
extremal minLayer choices and package them into reusable lemmas:

* `UniversalMinLayer`: minimal axioms extracted from `StructureTowerWithMin`
* `free_tower_minLayer_is_id`: discrete/free towers are literally identity
* `prod_minLayer_componentwise`: products compute minLayer coordinatewise
* `minLayer_naturality`: restatement of the functorial condition
* `constant_minLayer_terminal`: constant towers are terminal when every index
  is witnessed by some element (surjective minLayer)
* `minLayerFreedom`: counts the number of accessible minLayers in finite cases

These facts formalise the "自明例" (discrete minLayer) and
"極端例" (constant-collapse towers) emphasised in the notes.
-/

namespace MyProjects.ST

open CategoryTheory
open scoped Classical

universe u v

/-- A thin wrapper that isolates the categorical content of `minLayer`.  Every
`StructureTowerWithMin` already satisfies it, but naming the property simplifies
downstream lemmas. -/
class UniversalMinLayer (T : StructureTowerWithMin.{u, v}) : Prop where
  minLayer_is_section :
    ∀ x : T.carrier, x ∈ T.layer (T.minLayer x)
  minLayer_functorial :
    ∀ {T' : StructureTowerWithMin.{u, v}} (f : T ⟶ T') (x : T.carrier),
      T'.minLayer (f.map x) = f.indexMap (T.minLayer x)

instance (T : StructureTowerWithMin.{u, v}) :
    UniversalMinLayer T where
  minLayer_is_section := T.minLayer_mem
  minLayer_functorial := fun f x => f.minLayer_preserving x

@[simp]
lemma free_tower_minLayer_is_id (X : Type u) [Preorder X] :
    (freeStructureTowerMin X).minLayer = id := rfl

@[simp]
lemma prod_minLayer_componentwise
    (T₁ T₂ : StructureTowerWithMin.{u, v}) (x : T₁.carrier) (y : T₂.carrier) :
    (StructureTowerWithMin.prod T₁ T₂).minLayer (x, y) =
      (T₁.minLayer x, T₂.minLayer y) :=
  rfl

section Instances

instance (X : Type u) [Preorder X] [Fintype X] :
    Fintype (freeStructureTowerMin X).carrier := by
  change Fintype X
  infer_instance

instance (X : Type u) [Preorder X] [Fintype X] :
    Fintype (freeStructureTowerMin X).Index := by
  change Fintype X
  infer_instance

instance (X : Type u) [Preorder X] [DecidableEq X] :
    DecidableEq (freeStructureTowerMin X).Index := by
  change DecidableEq X
  infer_instance

end Instances

@[simp]
lemma minLayer_naturality
    {T T' : StructureTowerWithMin.{u, v}}
    (f : T ⟶ T') (x : T.carrier) :
    T'.minLayer (f.map x) = f.indexMap (T.minLayer x) :=
  f.minLayer_preserving x

section ConstantTerminal

variable {T : StructureTowerWithMin.{u, v}}
variable {X : Type u} {I : Type v} [Preorder I]
variable [DecidableRel ((· ≤ ·) : I → I → Prop)]
variable (i₀ : I)

/-- Constant minLayer towers are terminal among towers whose `minLayer` hits
every index.  The surjectivity hypothesis mirrors the Bourbaki requirement that
each abstract layer be realised by some element of the tower. -/
theorem constant_minLayer_terminal
    (hml : Function.Surjective T.minLayer)
    (f : T.carrier → X) :
    ∃! (φ : T ⟶ constantMinLayerTower X I i₀),
      ∀ x, φ.map x = f x := by
  classical
  refine ⟨collapseToConstant (T := T) (I := I) i₀ f, ?_, ?_⟩
  · intro x; rfl
  · intro ψ hψ
    apply StructureTowerWithMin.Hom.ext
    · funext x; exact hψ x
    · funext i
      obtain ⟨x, hx⟩ := hml i
      have h := ψ.minLayer_preserving x
      have h' : i₀ = ψ.indexMap i := by
        simpa [hx] using h
      have h'' : ψ.indexMap i = i₀ := h'.symm
      simpa [collapseToConstant] using h''

end ConstantTerminal

section Freedom

variable (T : StructureTowerWithMin.{u, v})

noncomputable def minLayerFreedom
    [Fintype T.carrier] [DecidableEq T.Index] : ℕ :=
  (((Finset.univ : Finset T.carrier).image fun x => T.minLayer x).card)

@[simp]
lemma minLayerFreedom_le_card
    [Fintype T.carrier] [DecidableEq T.Index] :
    minLayerFreedom T ≤ Fintype.card T.carrier := by
  classical
  simpa [minLayerFreedom] using
    (Finset.card_image_le (f := fun x => T.minLayer x)
      (s := (Finset.univ : Finset T.carrier)))

@[simp]
lemma minLayerFreedom_free
    (X : Type u) [Preorder X] [Fintype X] [DecidableEq X] :
    minLayerFreedom (freeStructureTowerMin X) = Fintype.card X := by
  classical
  unfold minLayerFreedom
  change (((Finset.univ : Finset X).image fun x : X => x).card) = Fintype.card X
  have h :
      ((Finset.univ : Finset X).image fun x : X => x) =
        (Finset.univ : Finset X) := by
    simpa using (Finset.image_id (Finset.univ : Finset X))
  simpa [h] using
    (Finset.card_univ : (Finset.univ : Finset X).card = Fintype.card X)

example : minLayerFreedom (freeStructureTowerMin (Fin 2)) = 2 := by
  simpa using (minLayerFreedom_free (X := Fin 2))

end Freedom

end MyProjects.ST
