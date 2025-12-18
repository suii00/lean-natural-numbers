import MyProjects.ST.CAT.Cat_LeBij

/-!
# Cat_TowerD_Bij: bijective morphisms on `TowerD`

This file provides a stable name for the “bijective lane” on `TowerD`:
morphisms are `Cat_le` morphisms together with bijectivity of both the carrier map and the index
map.

Historically, this notion lived in `MyProjects.ST.CAT.Cat_eq` under the name “`Cat_eq` / `HomEq`”,
but that was misleading: it is not the `minLayer`-equality lane (see `MyProjects.ST.CAT2_complete`)
and it is not a genuine groupoid of isomorphisms in `Cat_le` in general.

The authoritative implementation is `MyProjects.ST.CAT.Cat_LeBij`; this file is a thin re-export
and naming adapter.
-/

namespace ST

open CategoryTheory

/-! Objects (wrapper type) -/

/-- Object wrapper for the `TowerD` bijective lane. -/
abbrev TowerD_Bij := TowerD_LeBij

/-! Morphisms -/

namespace TowerD

/-- `TowerD` bijective morphisms (same as `HomLeBij`). -/
abbrev HomBij (T T' : TowerD) : Type :=
  HomLeBij T T'

end TowerD

/-! A tiny sanity check: `forgetToLe` keeps the underlying carrier map. -/
example {T T' : TowerD_Bij} (f : T ⟶ T') (x : (T : TowerD).carrier) :
    (ST.Functors.forgetToLe.map f).map x = f.map x := rfl

end ST
