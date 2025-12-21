import MyProjects.ST.RankCore.Basic
import MyProjects.ST.RankCore.RankHomLe

import MyProjects.ST.RankCore.P3.ListLength -- A3 (already existing)
import MyProjects.ST.RankCore.P3.FinsetCard
import MyProjects.ST.RankCore.P3.PolyDegree
import MyProjects.ST.RankCore.P3.IntAbs
import MyProjects.ST.RankCore.P3.ClosureIteration

import MyProjects.ST.RankCore.P4.GraphDistanceENat -- A4 (this batch)
import MyProjects.ST.RankCore.P4.VectorSpaceSparseRank
import MyProjects.ST.RankCore.P4.OpenSetTower
import MyProjects.ST.RankCore.P4.SubgroupTower
import MyProjects.ST.RankCore.P4.PrincipalIdeal

namespace ST

/-!
# Examples/Smoke (A4)

This file is a single entry point that imports the full example catalog.

DoD (A4):
- Example count reaches 10 (A3: 5 examples + A4: 5 additional examples).
- This file compiles, ensuring all example modules can be imported together.

Adjust the import paths if your A3 modules live elsewhere.
-/
-- Minimal smoke checks (avoid heavy proofs here).

#check Ranked
#check RankHomLe

end ST
