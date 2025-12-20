import MyProjects.ST.RankCore.Basic

namespace ST

open scoped BigOperators

/-- Example A2: Finset cardinality as a rank. -/
def finsetCardRanked (A : Type) : Ranked Nat (Finset A) where
  rank := Finset.card

example (A : Type) (s : Finset A) : (finsetCardRanked A).rank s = s.card := rfl

end ST
