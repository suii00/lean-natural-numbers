import MyProjects.ST.CAT.Cat_D.P4.P4_Categorical

/-!
# P4_SumCarrierTower2D: a 2-parameter tower over a sum carrier

This file reuses the definitions from `P4_Categorical.lean` (`TowerD`, `HomD`, etc.) and defines a
structure tower whose carrier is the sum `T₁.carrier ⊕ T₂.carrier` and whose index is the product
`T₁.Index × T₂.Index`, i.e. a two-parameter tower.

## Main definition

- `sumCarrierTower2D`:
  - `carrier := T₁.carrier ⊕ T₂.carrier`
  - `Index := T₁.Index × T₂.Index`
  - `layer (i, j) := (Sum.inl '' T₁.layer i) ∪ (Sum.inr '' T₂.layer j)`

## Note (universal property)

In general, this does *not* claim the coproduct universal property in Cat_D.
Since `HomD.map_layer` requires a single upper bound, merging the two bounds coming from the left
and right sides needs additional structure on the target index (e.g. existence of binary sup).

(Bourbaki style: first give the set-theoretic construction; state universal properties separately
under additional axioms.)
-/

namespace ST
namespace TowerD

section SumTower2D

/-- A 2-parameter tower over a sum carrier (`Index := Prod`).

This construction tracks the complexity of the left and right layers simultaneously via `(i, j)`.
Unlike the `Sum`-index version `coprod`, it does not in general satisfy the coproduct universal
property.

We assume `[Inhabited T₁.Index] [Inhabited T₂.Index]` to fill the opposite component when proving
`covering`.
-/
def sumCarrierTower2D (T₁ T₂ : TowerD) [Inhabited T₁.Index] [Inhabited T₂.Index] : TowerD where
  carrier := T₁.carrier ⊕ T₂.carrier
  Index := T₁.Index × T₂.Index
  indexPreorder := inferInstanceAs (Preorder (T₁.Index × T₂.Index))
  layer := fun ⟨i, j⟩ => (Sum.inl '' (T₁.layer i)) ∪ (Sum.inr '' (T₂.layer j))
  covering := by
    intro x
    cases x with
    | inl x₁ =>
      obtain ⟨i, hi⟩ := T₁.covering x₁
      refine ⟨⟨i, default⟩, ?_⟩
      exact Or.inl ⟨x₁, hi, rfl⟩
    | inr x₂ =>
      obtain ⟨j, hj⟩ := T₂.covering x₂
      refine ⟨⟨default, j⟩, ?_⟩
      exact Or.inr ⟨x₂, hj, rfl⟩
  monotone := by
    intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ hij x hx
    rcases hij with ⟨hi, hj⟩
    rcases hx with hx | hx
    · rcases hx with ⟨a, ha, rfl⟩
      exact Or.inl ⟨a, T₁.monotone hi ha, rfl⟩
    · rcases hx with ⟨b, hb, rfl⟩
      exact Or.inr ⟨b, T₂.monotone hj hb, rfl⟩

notation:35 T₁ " ⊕₂ᴰ " T₂ => sumCarrierTower2D T₁ T₂

-- Backward-compatible alias (keeps older notes compiling)
abbrev sumTower₂D := sumCarrierTower2D

/-- The left injection into `sumCarrierTower2D`. -/
def inl₂D (T₁ T₂ : TowerD) [Inhabited T₁.Index] [Inhabited T₂.Index] :
    T₁ ⟶ᴰ (T₁ ⊕₂ᴰ T₂) where
  map := Sum.inl
  map_layer := by
    intro i
    refine ⟨(i, default), ?_⟩
    intro x hx
    rcases hx with ⟨a, ha, rfl⟩
    exact Or.inl ⟨a, ha, rfl⟩

/-- The right injection into `sumCarrierTower2D`. -/
def inr₂D (T₁ T₂ : TowerD) [Inhabited T₁.Index] [Inhabited T₂.Index] :
    T₂ ⟶ᴰ (T₁ ⊕₂ᴰ T₂) where
  map := Sum.inr
  map_layer := by
    intro j
    refine ⟨(default, j), ?_⟩
    intro y hy
    rcases hy with ⟨b, hb, rfl⟩
    exact Or.inr ⟨b, hb, rfl⟩

end SumTower2D

section Examples

-- Minimal sanity checks (for compilation)
example : TowerD := natTower ⊕₂ᴰ natTower

example : (inl₂D natTower natTower).map (5 : ℕ) = Sum.inl 5 := rfl

example : Sum.inl (2 : ℕ) ∈ (natTower ⊕₂ᴰ natTower).layer ((2 : ℕ), (0 : ℕ)) := by
  -- It suffices to show membership in the left component of `layer (2, 0)`.
  simp [sumCarrierTower2D]

end Examples

end TowerD
end ST
