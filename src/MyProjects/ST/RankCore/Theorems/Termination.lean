import Mathlib
import MyProjects.ST.RankCore.Basic

/-!
Termination via rank.

Key defs: `Desc`, `StepRel`.
Key lemmas: `wf_desc`, `wf_of_rank_decreasing`, `wf_stepRel`, `acc_of_rank`.
Example: `acc_of_rank` gives accessibility for any element.
-/

namespace ST

open scoped Classical

universe u v

/-- A step relation decreases rank. -/
structure RankDecreases {X : Type u} (R : Ranked Nat X) (step : X → X) : Prop where
  dec : ∀ x : X, R.rank (step x) < R.rank x

namespace Termination

variable {X : Type u} (R : Ranked Nat X) (step : X → X)

/-- The "rank-descending" relation induced by R. -/
def Desc : X → X → Prop := fun x y => R.rank x < R.rank y

/-- Well-foundedness of Desc (standard `measure` argument). -/
theorem wf_desc : WellFounded (Desc (R := R)) := by
  -- `measure` provides WF for (fun x y => f x < f y)
  simpa [Desc] using (measure R.rank).wf

/-- No infinite descending chain from an accessible element. -/
theorem acc_no_infinite {r : X → X → Prop} {x : X} (hx : Acc r x) :
    ¬ ∃ f : ℕ → X, f 0 = x ∧ ∀ n, r (f (n + 1)) (f n) := by
  induction hx with
  | intro x hx ih =>
      intro h
      rcases h with ⟨f, hf0, hstep⟩
      have h1 : r (f 1) x := by
        simpa [hf0] using hstep 0
      have h' :
          ∃ g : ℕ → X, g 0 = f 1 ∧ ∀ n, r (g (n + 1)) (g n) := by
        refine ⟨fun n => f (Nat.succ n), rfl, ?_⟩
        intro n
        simpa using hstep (Nat.succ n)
      exact (ih _ h1) h'

/-- No infinite descending chain for a well-founded relation. -/
theorem no_infinite_desc {r : X → X → Prop} (h : WellFounded r) :
    ¬ ∃ f : ℕ → X, ∀ n, r (f (n + 1)) (f n) := by
  intro hseq
  rcases hseq with ⟨f, hstep⟩
  have hx : Acc r (f 0) := h.apply _
  have hx' :
      ¬ ∃ g : ℕ → X, g 0 = f 0 ∧ ∀ n, r (g (n + 1)) (g n) :=
    acc_no_infinite (x := f 0) hx
  exact hx' ⟨f, rfl, hstep⟩

theorem wf_of_rank_decreasing (r : X → X → Prop)
    (h : ∀ {x y}, r x y → R.rank x < R.rank y) : WellFounded r := by
  refine (wf_desc (R := R)).mono ?_
  intro x y hxy
  exact h hxy

def StepRel : X → X → Prop := fun x y => x = step y

theorem wf_stepRel (hdec : RankDecreases R step) : WellFounded (StepRel (step := step)) := by
  refine wf_of_rank_decreasing (R := R) (r := StepRel (step := step)) ?_
  intro x y hxy
  subst hxy
  exact hdec.dec y

/-
  A concrete "terminates" statement:
  every point is accessible in the rank-descending relation.
-/

theorem acc_of_rank (x : X) : Acc (Desc (R := R)) x :=
  (wf_desc (R := R)).apply x

example (x : X) : Acc (Desc (R := R)) x :=
  acc_of_rank (R := R) x

end Termination

end ST
