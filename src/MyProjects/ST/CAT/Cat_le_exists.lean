import MyProjects.ST.CAT.Cat_le

/-!
# Cat_le_exists: Existential variant of `Cat_le`.

This file introduces an "existential" version of order-preserving morphisms between structure
towers.

Compared with the data version `HomLe` (which stores an `indexMap`), the morphisms here only store
the underlying `map` together with the *existence* of a monotone `indexMap` witnessing layer
preservation. This design makes the forgetful map to `Cat_D` closer to being faithful.

To avoid `Category` instance collisions, we put the `Category` instance on a wrapper type
`TowerD_LeExists`.

## Main definitions
- `ST.TowerD_LeExists`
- `ST.TowerD_LeExists.HomLeExists`
-/

namespace ST

open CategoryTheory

/-- Object wrapper for the existential `Cat_le` lane. -/
structure TowerD_LeExists where
  toTowerD : TowerD

instance : Coe TowerD_LeExists TowerD := ⟨TowerD_LeExists.toTowerD⟩

namespace TowerD_LeExists

/-- Existential version of order-preserving morphisms:
`map` together with the existence of a monotone `indexMap` witnessing layer preservation. -/
def HomLeExists (T T' : TowerD_LeExists) : Type :=
  { f : (T : TowerD).carrier → (T' : TowerD).carrier //
      ∃ indexMap : (T : TowerD).Index → (T' : TowerD).Index,
        Monotone indexMap ∧
        ∀ (i : (T : TowerD).Index) (x : (T : TowerD).carrier),
          x ∈ (T : TowerD).layer i →
            f x ∈ (T' : TowerD).layer (indexMap i) }

infixr:10 " ⟶ₗₑ∃ " => HomLeExists

namespace HomLeExists

/-- The underlying function on carriers. -/
def map {T T' : TowerD_LeExists} (f : T ⟶ₗₑ∃ T') :
    (T : TowerD).carrier → (T' : TowerD).carrier :=
  f.1

/-- Retrieve the witness `indexMap` and its properties. -/
lemma exists_indexMap {T T' : TowerD_LeExists} (f : T ⟶ₗₑ∃ T') :
    ∃ indexMap : (T : TowerD).Index → (T' : TowerD).Index,
      Monotone indexMap ∧
      ∀ i x, x ∈ (T : TowerD).layer i → f.map x ∈ (T' : TowerD).layer (indexMap i) :=
  f.2

@[ext]
theorem ext {T T' : TowerD_LeExists} {f g : T ⟶ₗₑ∃ T'}
    (h : ∀ x, f.map x = g.map x) : f = g := by
  apply Subtype.ext
  funext x
  exact h x

/-- Identity morphism in the existential lane. -/
def id (T : TowerD_LeExists) : T ⟶ₗₑ∃ T :=
  ⟨_root_.id, ⟨_root_.id, monotone_id, by
    intro i x hx
    simpa using hx⟩⟩

/-- Composition in the existential lane. -/
def comp {T T' T'' : TowerD_LeExists}
    (g : T' ⟶ₗₑ∃ T'') (f : T ⟶ₗₑ∃ T') : T ⟶ₗₑ∃ T'' :=
  ⟨g.map ∘ f.map, by
    rcases f.exists_indexMap with ⟨φ, hφmono, hφ⟩
    rcases g.exists_indexMap with ⟨ψ, hψmono, hψ⟩
    refine ⟨ψ ∘ φ, hψmono.comp hφmono, ?_⟩
    intro i x hx
    exact hψ (φ i) (f.map x) (hφ i x hx)⟩

@[simp] lemma id_map (T : TowerD_LeExists) : (id T).map = _root_.id := rfl

@[simp] lemma comp_map {T T' T'' : TowerD_LeExists}
    (g : T' ⟶ₗₑ∃ T'') (f : T ⟶ₗₑ∃ T') :
    (comp g f).map = g.map ∘ f.map := rfl

end HomLeExists

/-- Category instance for the existential lane. -/
instance : Category TowerD_LeExists where
  Hom := HomLeExists
  id := HomLeExists.id
  comp := fun f g => HomLeExists.comp g f
  id_comp := by
    intro X Y f
    apply HomLeExists.ext
    intro x
    rfl
  comp_id := by
    intro X Y f
    apply HomLeExists.ext
    intro x
    rfl
  assoc := by
    intro W X Y Z h g f
    apply HomLeExists.ext
    intro x
    rfl

/-! A tiny sanity check: `𝟙` acts as the identity function. -/
example (T : TowerD_LeExists) (x : (T : TowerD).carrier) :
    (𝟙 T : T ⟶ T).map x = x := rfl

end TowerD_LeExists

end ST
