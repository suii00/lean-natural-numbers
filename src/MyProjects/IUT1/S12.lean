import Mathlib

namespace HW_IUT1_S12

-- P01: p進付値の計算
theorem S12_P01 : padicValNat 2 360 = 3 ∧ padicValNat 3 360 = 2 ∧ padicValNat 5 360 = 1 := by
  classical
  have h2 : padicValNat 2 360 = 3 := by
    haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
    have hpow : padicValNat 2 (2 ^ 3) = 3 :=
      by simpa using (padicValNat.prime_pow (p := 2) (n := 3))
    have hrest : padicValNat 2 45 = 0 :=
      padicValNat.eq_zero_of_not_dvd (by decide : ¬(2 ∣ 45))
    have hmul : padicValNat 2 ((2 ^ 3) * 45) =
        padicValNat 2 (2 ^ 3) + padicValNat 2 45 := by
      simpa using padicValNat.mul (p := 2) (a := 2 ^ 3) (b := 45)
        (by decide : (2 : ℕ) ^ 3 ≠ 0) (by decide : (45 : ℕ) ≠ 0)
    have hfactor : (2 ^ 3 : ℕ) * 45 = 360 := by norm_num
    calc
      padicValNat 2 360 = padicValNat 2 ((2 ^ 3) * 45) := by simpa [hfactor]
      _ = padicValNat 2 (2 ^ 3) + padicValNat 2 45 := hmul
      _ = 3 := by simpa [hpow, hrest]
  have h3 : padicValNat 3 360 = 2 := by
    haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
    have hpow : padicValNat 3 (3 ^ 2) = 2 :=
      by simpa using (padicValNat.prime_pow (p := 3) (n := 2))
    have hrest : padicValNat 3 40 = 0 :=
      padicValNat.eq_zero_of_not_dvd (by decide : ¬(3 ∣ 40))
    have hmul : padicValNat 3 ((3 ^ 2) * 40) =
        padicValNat 3 (3 ^ 2) + padicValNat 3 40 := by
      simpa using padicValNat.mul (p := 3) (a := 3 ^ 2) (b := 40)
        (by decide : (3 : ℕ) ^ 2 ≠ 0) (by decide : (40 : ℕ) ≠ 0)
    have hfactor : (3 ^ 2 : ℕ) * 40 = 360 := by norm_num
    calc
      padicValNat 3 360 = padicValNat 3 ((3 ^ 2) * 40) := by simpa [hfactor]
      _ = padicValNat 3 (3 ^ 2) + padicValNat 3 40 := hmul
      _ = 2 := by simpa [hpow, hrest]
  have h5 : padicValNat 5 360 = 1 := by
    haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hpow : padicValNat 5 (5 ^ 1) = 1 :=
      by simpa using (padicValNat.prime_pow (p := 5) (n := 1))
    have hrest : padicValNat 5 72 = 0 :=
      padicValNat.eq_zero_of_not_dvd (by decide : ¬(5 ∣ 72))
    have hmul : padicValNat 5 (5 * 72) =
        padicValNat 5 5 + padicValNat 5 72 := by
      simpa using padicValNat.mul (p := 5) (a := 5) (b := 72)
        (by decide : (5 : ℕ) ≠ 0) (by decide : (72 : ℕ) ≠ 0)
    have hfactor : (5 : ℕ) * 72 = 360 := by norm_num
    calc
      padicValNat 5 360 = padicValNat 5 (5 * 72) := by simpa [hfactor]
      _ = padicValNat 5 5 + padicValNat 5 72 := hmul
      _ = 1 := by simpa [hpow, hrest]
  exact ⟨h2, h3, h5⟩

-- P02: p進ノルムの性質
theorem S12_P02 : padicNorm 5 (25 : ℚ) = 1 / 25 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hnorm5 : padicNorm 5 (5 : ℚ) = (5 : ℚ)⁻¹ :=
    by simpa using (padicNorm.padicNorm_p_of_prime (p := 5))
  have h25 : (25 : ℚ) = (5 : ℚ) * (5 : ℚ) := by norm_num
  calc
    padicNorm 5 (25 : ℚ)
        = padicNorm 5 ((5 : ℚ) * (5 : ℚ)) := by simpa [h25]
    _ = padicNorm 5 (5 : ℚ) * padicNorm 5 (5 : ℚ) := by
      simpa using padicNorm.mul (p := 5) (q := (5 : ℚ)) (r := (5 : ℚ))
    _ = (5 : ℚ)⁻¹ * (5 : ℚ)⁻¹ := by
      simp only [hnorm5]
    _ = 1 / 25 := by norm_num


-- P03: p進距離の計算
theorem S12_P03 : padicNorm 3 (26 - 35 : ℤ) = 1 / 9 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hdiff : ((26 - 35 : ℤ) : ℚ) = (-9 : ℚ) := by norm_num
  have hnorm3 : padicNorm 3 (3 : ℚ) = (3 : ℚ)⁻¹ :=
    by simpa using (padicNorm.padicNorm_p_of_prime (p := 3))
  have h9 : (9 : ℚ) = (3 : ℚ) * (3 : ℚ) := by norm_num
  calc
    padicNorm 3 (26 - 35 : ℤ) = padicNorm 3 (-9 : ℚ) := by simpa [hdiff]
    _ = padicNorm 3 (9 : ℚ) := by
      simpa using padicNorm.neg (p := 3) (q := (9 : ℚ))
    _ = padicNorm 3 ((3 : ℚ) * (3 : ℚ)) := by simpa [h9]
    _ = padicNorm 3 (3 : ℚ) * padicNorm 3 (3 : ℚ) := by
      simpa using padicNorm.mul (p := 3) (q := (3 : ℚ)) (r := (3 : ℚ))
    _ = (3 : ℚ)⁻¹ * (3 : ℚ)⁻¹ := by
      simp only [hnorm3]
    _ = 1 / 9 := by norm_num

-- P04: p進展開の初項（修正版）
theorem S12_P04 : 17 % 3 = 2 ∧ 17 % 9 = 8 ∧ 17 % 27 = 17 := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · decide

-- P05: ヘンゼルの補題の準備
theorem S12_P05 : (3 : ℤ)^2 % 7 = 2 ∧ (10 : ℤ)^2 % 49 = 2 := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

-- CH: p進整数の稠密性
theorem S12_CH : (2 : ZMod 125) * 63 = 1 ∧
    Nat.Coprime 2 5 ∧
    ∃ (u : (ZMod 5)ˣ), (u : ZMod 5) = 2 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · refine ⟨⟨2, 3, ?_, ?_⟩, rfl⟩
    · decide
    · decide

end HW_IUT1_S12
