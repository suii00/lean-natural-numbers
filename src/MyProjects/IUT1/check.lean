import Mathlib

example : padicNorm 5 (1 / 8 : ℚ) = 1 := by
  have hprime : Nat.Prime 5 := by decide
  haveI : Fact (Nat.Prime 5) := ⟨hprime⟩
  have hpadic8_nat : padicValNat 5 8 = 0 := padicValNat.eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 8)
  have hpadic8 : padicValRat 5 (8 : ℚ) = 0 := by
    simpa [hpadic8_nat] using (padicValRat.of_nat (p := 5) (n := 8))
  have hpadic_one : padicValRat 5 (1 : ℚ) = 0 := by simpa using (padicValRat.one (p := 5))
  have hval : padicValRat 5 (1 / 8 : ℚ) = 0 := by
    have hq : (1 : ℚ) ≠ 0 := by norm_num
    have hr : (8 : ℚ) ≠ 0 := by norm_num
    simpa [hpadic_one, hpadic8] using
      (padicValRat.div (p := 5) (q := (1 : ℚ)) (r := (8 : ℚ)) hq hr)
  have hnonzero : (1 / 8 : ℚ) ≠ 0 := by norm_num
  have hnorm := padicNorm.eq_zpow_of_nonzero (p := 5) (q := (1 / 8 : ℚ)) hnonzero
  have hpow : padicNorm 5 (1 / 8 : ℚ) = (5 : ℚ) ^ 0 := by
    simpa [hval] using hnorm
  have hconst : (5 : ℚ) ^ 0 = 1 := by norm_num
  exact hpow.trans hconst
