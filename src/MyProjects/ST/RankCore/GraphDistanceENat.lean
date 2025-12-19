import Mathlib
import MyProjects.ST.RankCore.RankCore

namespace ST

open scoped Classical

/-
  Example A3: a "distance-to-target" rank valued in ℕ∞ (= ENat / WithTop Nat),
  typically noncomputable if defined via existence/minimization.
-/

-- A minimal graph interface (you can replace with your graph defs).
variable {V : Type} (adj : V → V → Prop) (target : Set V)

-- Placeholder: "reachable in ≤ n steps" (you will define properly).
def reachableWithin (n : Nat) (v : V) : Prop := True  -- TODO

noncomputable
def distRank (v : V) : WithTop Nat :=
  if h : (∃ n, reachableWithin (adj := adj) (target := target) n v) then
    some (Nat.find h)   -- minimal n, hence noncomputable
  else
    ⊤

noncomputable
def graphDistanceRanked : Ranked (WithTop Nat) V where
  rank := distRank (adj := adj) (target := target)

end ST
