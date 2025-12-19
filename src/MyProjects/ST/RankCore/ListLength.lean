import MyProjects.ST.RankCore.RankCore

namespace ST

/-- Example A1: list length as a rank. -/
def listLengthRanked (A : Type) : Ranked Nat (List A) where
  rank := List.length

example (A : Type) (xs : List A) : (listLengthRanked A).rank xs = xs.length := rfl

example (A : Type) (n : Nat) :
    (listLengthRanked A).layer n = {xs : List A | xs.length ≤ n} := rfl

end ST
