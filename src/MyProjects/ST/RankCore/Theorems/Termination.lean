import Mathlib
import MyProjects.ST.RankCore.RankCore

namespace ST

open scoped Classical

universe u v

/-- A step relation decreases rank. -/
structure RankDecreases {X : Type u} (R : Ranked Nat X) (step : X → X) : Prop :=
  (dec : ∀ x : X, R.rank (step x) < R.rank x)

namespace Termination

variable {X : Type u} (R : Ranked Nat X) (step : X → X)

/-- The "rank-descending" relation induced by R. -/
def Desc : X → X → Prop := fun x y => R.rank x < R.rank y

/-- Well-foundedness of Desc (standard `measure` argument). -/
theorem wf_desc : WellFounded (Desc (R := R)) := by
  -- `measure` provides WF for (fun x y => f x < f y)
  simpa [Desc] using (measure R.rank).wf

/-
  A concrete "terminates" statement (skeleton):
  repeated stepping cannot go on forever if rank strictly decreases.
-/

/-- One possible notion: no infinite chain x₀, x₁=step x₀, x₂=step x₁, ... -/
theorem no_infinite_iter (hdec : RankDecreases R step) :
    ¬ (∃ x0 : X, True) := by
  -- TODO: replace `True` with a proper infinite-sequence formulation you use
  -- (e.g. `∃ f : Nat → X, f (n+1)=step (f n)`).
  -- Then use `wf_desc` to contradict infinite descending chain of ranks.
  intro h
  cases h with
  | intro x0 _ =>
    -- placeholder contradiction
    have : False := by
      -- TODO
      admit
    exact this

end Termination

end ST
