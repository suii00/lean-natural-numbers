import MyProjects.ST.CAT2_complete

/-!
# Cat_WithMin: the `minLayer`-equality lane

This file is a lightweight entry point under `MyProjects.ST.CAT.*` for the “with `minLayer`”
structure-tower lane.

Concretely, it re-exports the definitions from `MyProjects.ST.CAT2_complete`, where objects carry
a chosen `minLayer` and morphisms preserve it **by equality**:

`minLayer_preserving : T'.minLayer (f.map x) = f.indexMap (T.minLayer x)`.

## Relation to `Cat_eq`

`MyProjects.ST.CAT.Cat_eq` is a thin wrapper that re-exports this module as the preferred
entry point for the `minLayer`-equality lane.

For the bijective lane on the minLayer-free notion `TowerD`, see `MyProjects.ST.CAT.Cat_TowerD_Bij`
(built on top of `MyProjects.ST.CAT.Cat_LeBij`).
-/

namespace ST

/-- Objects in the “with `minLayer`” lane. -/
abbrev TowerWithMin := _root_.StructureTowerWithMin

/-- Alias for `TowerWithMin` (objects, not morphisms). -/
abbrev WithMin := TowerWithMin

/-- `homeq` (the “=`minLayer`” morphisms): just `StructureTowerWithMin.Hom`. -/
abbrev homeq (T T' : TowerWithMin) : Type _ :=
  _root_.StructureTowerWithMin.Hom (T := T) (T' := T')

open CategoryTheory

/-! A tiny sanity check: composition is function composition on `map`. -/
example (T T' T'' : TowerWithMin) (f : T ⟶ T') (g : T' ⟶ T'') :
    (f ≫ g).map = g.map ∘ f.map := rfl

end ST
