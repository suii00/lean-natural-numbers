import Mathlib.Data.Finsupp.Basic
import MyProjects.ST.RankCore.Basic

/-!
# VectorSpaceSparseRank (A4 skeleton)

A computable example: sparse vectors (finitely-supported functions) ranked by support size.

Carrier: `ι →₀ K`
Rank: `support.card : ℕ`

This is designed to reuse existing "finite basis / sparse set" assets later:
you can map actual vector spaces with a chosen basis into `ι →₀ K` and inherit this rank.
-/

namespace ST

universe u v

namespace VectorSpaceSparseRank

variable {ι : Type u} {K : Type v} [DecidableEq ι] [Zero K]

/-- Sparse rank: number of nonzero coordinates. -/
def sparseRanked : Ranked Nat (ι →₀ K) where
  rank := fun x => x.support.card

@[simp] lemma rank_def (x : ι →₀ K) :
    (sparseRanked (ι := ι) (K := K)).rank x = x.support.card := rfl

end VectorSpaceSparseRank

end ST
