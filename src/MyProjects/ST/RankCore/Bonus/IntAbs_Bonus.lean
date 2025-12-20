import MyProjects.ST.RankCore.P3.IntAbs

/-!
# IntAbs_Bonus - Optional lemmas for IntAbs

注意: mathlib 依存が重く壊れやすい補題を含むため、T1 本文から切り離している。

This file contains heavier lemmas that are not needed for the T1 core text.
Import it only when you need the explicit layer cardinality.
-/

namespace ST

open scoped BigOperators

/-- Layer cardinality for the integer-absolute-value rank. -/
lemma layer_card (n : ℕ) :
    Set.ncard ((instRankedInt : Ranked ℕ ℤ).layer n) = 2 * n + 1 := by
  classical
  have hset :
      (instRankedInt : Ranked ℕ ℤ).layer n = Set.Icc (-(n : ℤ)) (n : ℤ) := by
    ext z
    simp [Set.Icc, int_layer_eq_interval]
  have hfinite : (Set.Icc (-(n : ℤ)) (n : ℤ)).Finite := Set.finite_Icc _ _
  let _ : Fintype (Set.Icc (-(n : ℤ)) (n : ℤ)) := hfinite.fintype
  have hcard_set :
      Set.ncard (Set.Icc (-(n : ℤ)) (n : ℤ)) =
        (Finset.Icc (-(n : ℤ)) (n : ℤ)).card := by
    simpa [Set.toFinset_Icc] using
      (Set.ncard_eq_toFinset_card (Set.Icc (-(n : ℤ)) (n : ℤ)) hfinite)
  have hcard_finset :
      (Finset.Icc (-(n : ℤ)) (n : ℤ)).card =
        ((n : ℤ) + 1 - (-(n : ℤ))).toNat := by
    simpa using (Int.card_Icc (a := (-(n : ℤ))) (b := (n : ℤ)))
  have hcalc :
      ((n : ℤ) + 1 - (-(n : ℤ))).toNat = 2 * n + 1 := by
    have hrewrite :
        (n : ℤ) + 1 - (-(n : ℤ)) = (2 * n + 1 : ℤ) := by
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, two_mul]
    have hnonneg : 0 ≤ (n : ℤ) + 1 - (-(n : ℤ)) := by
      simpa [hrewrite] using (Int.natCast_nonneg (2 * n + 1))
    apply (Int.ofNat_inj).1
    calc
      (((n : ℤ) + 1 - (-(n : ℤ))).toNat : ℤ)
          = (n : ℤ) + 1 - (-(n : ℤ)) := Int.toNat_of_nonneg hnonneg
      _ = (2 * n + 1 : ℤ) := hrewrite
  calc
    Set.ncard ((instRankedInt : Ranked ℕ ℤ).layer n)
        = Set.ncard (Set.Icc (-(n : ℤ)) (n : ℤ)) := by simpa [hset]
    _ = (Finset.Icc (-(n : ℤ)) (n : ℤ)).card := hcard_set
    _ = ((n : ℤ) + 1 - (-(n : ℤ))).toNat := hcard_finset
    _ = 2 * n + 1 := hcalc

end ST
