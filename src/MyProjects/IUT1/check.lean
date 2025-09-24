import Mathlib

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

lemma test : (5 : ℚ) ^ (-padicValRat 5 (1 / 8 : ℚ)) = 1 := by
  have hq : (1 : ℚ) ≠ 0 := by norm_num
  have hr : (8 : ℚ) ≠ 0 := by norm_num
  have hpadic_one : padicValRat 5 (1 : ℚ) = 0 := by simpa using (padicValRat.one (p := 5))
  have hpadic8_nat : padicValNat 5 8 = 0 := padicValNat.eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 8)
  have hpadic8 : padicValRat 5 (8 : ℚ) = 0 := by
    simpa [hpadic8_nat] using (padicValRat.of_nat (p := 5) (n := 8))
  have hpadicVal : padicValRat 5 (1 / 8 : ℚ) = 0 := by
    simpa [hpadic_one, hpadic8] using
      (padicValRat.div (p := 5) (q := (1 : ℚ)) (r := (8 : ℚ)) hq hr)
  have hpadic8_inv : padicValRat 5 ((8 : ℚ)⁻¹) = 0 := by
    simpa [hpadic8] using (padicValRat.inv (p := 5) (8 : ℚ))
  have hexp : (-padicValRat 5 (1 / 8 : ℚ)) = padicValRat 5 ((8 : ℚ)⁻¹) := by
    simpa [div_eq_mul_inv] using (padicValRat.inv (p := 5) (1 / 8 : ℚ))
  -- ???
  }
