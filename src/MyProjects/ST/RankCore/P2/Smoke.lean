import MyProjects.ST.RankCore.RankCore
import MyProjects.ST.RankCore.RankHomLe

namespace ST

/-- Smoke example: list length as a rank. -/
def listLengthRanked (A : Type) : Ranked Nat (List A) where
  rank := List.length

example (A : Type) (xs : List A) : (listLengthRanked A).rank xs = xs.length := rfl

/-- Smoke: identity morphism in the data lane. -/
def listId (A : Type) : RankHomLe (listLengthRanked A) (listLengthRanked A) :=
  RankHomLe.id (listLengthRanked A)

/-- Smoke: composition behaves on the underlying carrier map. -/
example (A : Type) (xs : List A) :
    (RankHomLe.comp (listId A) (listId A)).map xs = xs := rfl

end ST
