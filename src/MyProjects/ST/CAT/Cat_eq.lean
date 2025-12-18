import MyProjects.ST.CAT.Cat_WithMin

/-!
# Cat_eq: the `minLayer`-equality lane

This module name is kept as a convenient entry point for the lane where structure towers carry a
chosen `minLayer` and morphisms preserve it **by equality** (your `homeq` intuition).

Concretely, it re-exports `MyProjects.ST.CAT.Cat_WithMin`, which itself re-exports
`MyProjects.ST.CAT2_complete`.

## If you wanted bijectivity on `TowerD`

The old “bijective lane on `TowerD`” has been moved to `MyProjects.ST.CAT.Cat_TowerD_Bij` (built
on top of `MyProjects.ST.CAT.Cat_LeBij`).
-/

