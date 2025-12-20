import Mathlib
import MyProjects.ST.RankCore.Basic

/-!
Ranked graph distance valued in `WithTop Nat`.

`reachableWithin` is a placeholder (currently always `True`), so `distRank` is
defined but intentionally noncomputable via `Nat.find`.
-/

namespace ST

open scoped Classical

/-
  Example A3: a "distance-to-target" rank valued in ℕ∞ (= ENat / WithTop Nat),
  typically noncomputable if defined via existence/minimization.
-/

variable {V : Type}

-- Placeholder: "reachable in ≤ n steps" (you will define properly).
def reachableWithin (_adj : V → V → Prop) (_target : Set V) (_n : Nat) (_v : V) : Prop :=
  True  -- TODO

noncomputable
def distRank (adj : V → V → Prop) (target : Set V) (v : V) : WithTop Nat :=
  if h : (∃ n, reachableWithin adj target n v) then
    some (Nat.find h)   -- minimal n, hence noncomputable
  else
    ⊤

noncomputable
def graphDistanceRanked (adj : V → V → Prop) (target : Set V) : Ranked (WithTop Nat) V where
  rank := distRank adj target

example (adj : V → V → Prop) (target : Set V) (v : V) :
    distRank adj target v ≠ (⊤ : WithTop Nat) := by
  classical
  have h : ∃ n, reachableWithin adj target n v := by
    exact ⟨0, by simp [reachableWithin]⟩
  have h' : distRank adj target v = some (Nat.find h) := by
    simp [distRank, h]
  simp [h']

end ST
