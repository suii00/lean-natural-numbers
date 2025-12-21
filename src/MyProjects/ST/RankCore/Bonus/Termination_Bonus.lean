import MyProjects.ST.RankCore.Theorems.Termination

/-!
# Termination_Bonus - extra termination examples

This file keeps optional examples out of the core Termination file.
-/

namespace ST

open Termination

def PredRel : Nat → Nat → Prop := fun x y => y = x + 1

theorem wf_predRel : WellFounded PredRel := by
  let R : Ranked Nat Nat := { rank := id }
  refine wf_of_rank_decreasing (R := R) (r := PredRel) ?_
  intro x y h
  rcases h with rfl
  change x < Nat.succ x
  exact Nat.lt_succ_self x

end ST
