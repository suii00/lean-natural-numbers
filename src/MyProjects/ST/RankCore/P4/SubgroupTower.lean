import Mathlib.Algebra.Group.Subgroup.Basic
import MyProjects.ST.RankCore.Basic

/-!
# SubgroupTower (A4 skeleton)

A computable "subgroup tower" by generators.

Carrier: `Finset G` (a finite generating family)
Evaluation: `Subgroup.closure (S : Set G)`
Rank: `S.card`

This is a stable bridge toward ACC-style statements later:
chains can be controlled by rank on generating families, before proving minimality facts.
-/

namespace ST

universe u

namespace SubgroupTower

variable {G : Type u} [Group G]

/-- Evaluate a finite generating set into the subgroup it generates. -/
def toSubgroup (S : Finset G) : Subgroup G :=
  Subgroup.closure (S : Set G)

/-- Ranked structure: rank = size of the generating family. -/
def genRanked : Ranked Nat (Finset G) where
  rank := fun S => S.card

@[simp] lemma rank_def (S : Finset G) : (genRanked (G := G)).rank S = S.card := rfl

end SubgroupTower

end ST
