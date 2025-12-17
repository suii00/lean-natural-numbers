import MyProjects.ST.CAT.Cat_le_exists
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Cat_le_functors: Data → Exists → D connections.

This file connects three "lanes" built on the same underlying notion of structure tower `TowerD`:

- **Data `Cat_le`**: morphisms are `HomLe` (they store `indexMap` as data). This is the `Category`
  instance on `TowerD` provided by `Cat_le.lean`.
- **Existential `Cat_le`**: morphisms are `HomLeExists` (they store only `map` and require the
  existence of a suitable monotone `indexMap`). This is the `Category` instance on
  `TowerD_LeExists` provided by `Cat_le_exists.lean`.
- **`Cat_D` lane**: morphisms are `HomD` (existential layer preservation). To avoid `Category`
  instance collisions, we put the `Category` instance on the wrapper type `TowerD_D` here.

We then provide the forgetful functors:
- `forgetIndexMap : TowerD ⥤ TowerD_LeExists`
- `forgetToD : TowerD_LeExists ⥤ TowerD_D`
- `forgetLeToD : TowerD ⥤ TowerD_D` as their composition.
-/

namespace ST

open CategoryTheory

/-!
## `HomD` as a category (on a wrapper type)

`Cat_le.lean` defines `HomD` as a structure, but does not equip it with `id`/`comp` or an
associated `Category` instance (because `TowerD` already carries the `Cat_le` instance there).

We add the basic operations and an ext lemma here, then lift them to a `Category` instance on
`TowerD_D`.
-/

namespace TowerD

namespace HomD

@[ext]
theorem ext {T T' : TowerD} {f g : HomD T T'}
    (h : f.map = g.map) : f = g := by
  cases f with
  | mk map₁ map_layer₁ =>
    cases g with
    | mk map₂ map_layer₂ =>
      cases h
      have h₂ : map_layer₁ = map_layer₂ := funext (fun _ => Subsingleton.elim _ _)
      cases h₂
      rfl

/-- Identity morphism in `Cat_D` (for the local wrapper category). -/
def id (T : TowerD) : HomD T T where
  map := _root_.id
  map_layer := by
    intro i
    refine ⟨i, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hx

/-- Composition in `Cat_D` (for the local wrapper category). -/
def comp {T T' T'' : TowerD} (g : HomD T' T'') (f : HomD T T') : HomD T T'' where
  map := g.map ∘ f.map
  map_layer := by
    intro i
    obtain ⟨j, hj⟩ := f.map_layer i
    obtain ⟨k, hk⟩ := g.map_layer j
    refine ⟨k, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hk ⟨f.map x, hj ⟨x, hx, rfl⟩, rfl⟩

@[simp] lemma id_map (T : TowerD) : (id T).map = _root_.id := rfl

@[simp] lemma comp_map {T T' T'' : TowerD} (g : HomD T' T'') (f : HomD T T') :
    (comp g f).map = g.map ∘ f.map := rfl

end HomD

end TowerD

/-- Object wrapper for the `Cat_D` lane (to avoid `Category` instance collisions on `TowerD`). -/
structure TowerD_D where
  toTowerD : TowerD

instance : Coe TowerD_D TowerD := ⟨TowerD_D.toTowerD⟩

namespace TowerD_D

/-- Morphisms in the `Cat_D` lane. -/
abbrev Hom (T T' : TowerD_D) : Type :=
  TowerD.HomD (T : TowerD) (T' : TowerD)

instance : Category TowerD_D where
  Hom := Hom
  id := fun T => TowerD.HomD.id (T : TowerD)
  comp := fun f g => TowerD.HomD.comp g f
  id_comp := by
    intro X Y f
    apply TowerD.HomD.ext
    rfl
  comp_id := by
    intro X Y f
    apply TowerD.HomD.ext
    rfl
  assoc := by
    intro W X Y Z h g f
    apply TowerD.HomD.ext
    rfl

end TowerD_D

namespace Functors

/-- Convert a data `HomLe` morphism to an existential-lane morphism by forgetting the `indexMap`
data but keeping it as an existence witness. -/
def homLeData_to_homLeExists {T T' : TowerD} (f : T ⟶ T') :
    (⟨T⟩ : TowerD_LeExists) ⟶ (⟨T'⟩ : TowerD_LeExists) := by
  refine ⟨f.map, ?_⟩
  refine ⟨f.indexMap, f.indexMap_mono, ?_⟩
  intro i x hx
  exact f.layer_preserving i x hx

/-- Forgetful functor: data `Cat_le` (on `TowerD`) → existential lane. -/
def forgetIndexMap : TowerD ⥤ TowerD_LeExists where
  obj T := ⟨T⟩
  map := by
    intro T T' f
    exact homLeData_to_homLeExists (T := T) (T' := T') f
  map_id := by
    intro T
    apply TowerD_LeExists.HomLeExists.ext
    intro x
    rfl
  map_comp := by
    intro T T' T'' f g
    apply TowerD_LeExists.HomLeExists.ext
    intro x
    rfl

/-- Convert an existential-lane morphism to a `HomD` morphism by choosing `j := indexMap i`. -/
def homLeExists_to_homD {T T' : TowerD_LeExists} (f : T ⟶ T') :
    TowerD.HomD (T : TowerD) (T' : TowerD) := by
  refine ⟨f.map, ?_⟩
  intro i
  rcases (TowerD_LeExists.HomLeExists.exists_indexMap f) with ⟨φ, -, hφ⟩
  refine ⟨φ i, ?_⟩
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact hφ i x hx

/-- Forgetful functor: existential lane → `Cat_D` lane (wrapper). -/
def forgetToD : TowerD_LeExists ⥤ TowerD_D where
  obj T := ⟨(T : TowerD)⟩
  map := by
    intro T T' f
    exact homLeExists_to_homD (T := T) (T' := T') f
  map_id := by
    intro T
    apply TowerD.HomD.ext
    rfl
  map_comp := by
    intro T T' T'' f g
    apply TowerD.HomD.ext
    rfl

instance : Functor.Faithful forgetToD where
  map_injective := by
    intro T T' f g h
    have hm : (forgetToD.map f).map = (forgetToD.map g).map := by
      exact congrArg (fun k => k.map) h
    apply TowerD_LeExists.HomLeExists.ext
    intro x
    exact congrArg (fun m => m x) hm

/-- Composite forgetful functor: data `Cat_le` → `Cat_D` via the existential lane. -/
def forgetLeToD : TowerD ⥤ TowerD_D :=
  forgetIndexMap ⋙ forgetToD

  /-! A tiny sanity check: `forgetLeToD` sends identity to identity on carrier maps. -/
  example (T : TowerD) (x : T.carrier) :
      (forgetLeToD.map (𝟙 T)).map x = x := rfl

  /-! A tiny sanity check: `forgetLeToD` preserves composition on carrier maps. -/
  example (x : TowerD.natTowerD.carrier) :
      (forgetLeToD.map (TowerD.natSuccHomLe ≫ TowerD.natSuccHomLe)).map x = Nat.succ (Nat.succ x) := rfl
 
  end Functors

end ST
