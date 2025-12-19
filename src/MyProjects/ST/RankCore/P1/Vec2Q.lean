import Mathlib
import MyProjects.ST.RankCore.P1.List
import MyProjects.ST.Closure.P1.Basic

/-!
RankCore instance for ℚ² based on minimal basis count.

This mirrors `Closure.P1.Basic` and keeps the rank definition explicit.
-/

namespace RankCore

def vec2QCore : Core (ℚ × ℚ) where
  rank v :=
    if v.1 = 0 ∧ v.2 = 0 then 0
    else if v.1 = 0 ∨ v.2 = 0 then 1
    else 2

lemma rank_general (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    vec2QCore.rank (a, b) = 2 := by
  simpa [vec2QCore, ClosureTowerExample.minBasisCount] using
    (ClosureTowerExample.minBasisCount_general a b ha hb)

example : vec2QCore.rank (0, 0) = 0 := by
  simp [vec2QCore]

#eval vec2QCore.rank (3, 5)  -- 2
#eval vec2QCore.rank (3, 0)  -- 1
#eval vec2QCore.rank (0, 0)  -- 0

end RankCore
