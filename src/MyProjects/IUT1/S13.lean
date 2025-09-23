import Mathlib

namespace HW_IUT1_S13

-- P01: p進収束
theorem S13_P01 (n : ℕ) : padicNorm 5 (5^(n+1) : ℚ) = (5 : ℚ)^(-(n+1 : ℤ)) := by
  classical
  haveI : Fact (Nat.Prime 5) := by decide
  have hq : (5 ^ (n + 1) : ℚ) ≠ 0 :=
    pow_ne_zero (n + 1) (by norm_num : (5 : ℚ) ≠ 0)
  have hvalNat : padicValRat 5 (5 ^ (n + 1) : ℚ) = (n + 1 : ℤ) := by
    have hnat : padicValNat 5 (5 ^ (n + 1)) = n + 1 := by
      simpa using padicValNat.prime_pow (p := 5) (n := n + 1)
    simpa [hnat] using
      (padicValRat.of_nat (p := 5) (n := 5 ^ (n + 1))).symm
  simpa [padicNorm.eq_zpow_of_nonzero (p := 5) hq, hvalNat]

-- P02: p進整数の特徴付け
theorem S13_P02 : padicNorm 5 (2/3 : ℚ) ≤ 1 ∧ padicNorm 5 (1/5 : ℚ) > 1 := by
  classical
  haveI : Fact (Nat.Prime 5) := by decide
  have h2 : padicValRat 5 (2 : ℚ) = 0 := by
    have hnat : padicValNat 5 2 = 0 :=
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ 5 ∣ (2 : ℕ))
    simpa [hnat] using (padicValRat.of_nat (p := 5) (n := 2)).symm
  have h3 : padicValRat 5 (3 : ℚ) = 0 := by
    have hnat : padicValNat 5 3 = 0 :=
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ 5 ∣ (3 : ℕ))
    simpa [hnat] using (padicValRat.of_nat (p := 5) (n := 3)).symm
  have h5 : padicValRat 5 (5 : ℚ) = 1 := by
    simpa using padicValRat.self (p := 5) (by decide : 1 < 5)
  have h1 : padicValRat 5 (1 : ℚ) = 0 := by
    have hnat : padicValNat 5 1 = 0 :=
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ 5 ∣ (1 : ℕ))
    simpa [hnat] using (padicValRat.of_nat (p := 5) (n := 1)).symm
  have hpadic23 : padicValRat 5 (2 / 3 : ℚ) = 0 := by
    simpa [h2, h3] using
      padicValRat.div (p := 5) (q := (2 : ℚ)) (r := (3 : ℚ)) (by norm_num) (by norm_num)
  have hpadic15 : padicValRat 5 (1 / 5 : ℚ) = -1 := by
    simpa [h1, h5] using
      padicValRat.div (p := 5) (q := (1 : ℚ)) (r := (5 : ℚ)) (by norm_num) (by norm_num)
  have hnorm23 : padicNorm 5 (2 / 3 : ℚ) = 1 := by
    have hneq : (2 / 3 : ℚ) ≠ 0 := by norm_num
    simpa [padicNorm.eq_zpow_of_nonzero (p := 5) hneq, hpadic23]
  have hnorm15 : padicNorm 5 (1 / 5 : ℚ) = (5 : ℚ) := by
    have hneq : (1 / 5 : ℚ) ≠ 0 := by norm_num
    simpa [padicNorm.eq_zpow_of_nonzero (p := 5) hneq, hpadic15]
  refine ⟨by simpa [hnorm23], ?_⟩
  simpa [hnorm15] using (show (5 : ℚ) > (1 : ℚ) by norm_num)

-- P03: p進方程式の解
theorem S13_P03 : (2 : ZMod 5)^2 = -1 ∧ ∃ x : ZMod 25, x^2 = -1 := by
  constructor
  · decide
  · refine ⟨7, ?_⟩
    decide

-- P04: 強三角不等式
theorem S13_P04 : padicNorm 5 (15 + 10 : ℚ) ≤ max (padicNorm 5 15) (padicNorm 5 10) := by
  classical
  haveI : Fact (Nat.Prime 5) := by decide
  simpa using padicNorm.nonarchimedean (p := 5) (q := (15 : ℚ)) (r := (10 : ℚ))

-- P05: p進対数の存在条件
theorem S13_P05 : padicNorm 5 (5 : ℚ) < 1 := by
  classical
  haveI : Fact (Nat.Prime 5) := by decide
  simpa using padicNorm.padicNorm_p_lt_one_of_prime (p := 5)

-- CH: 局所-大域原理の例（ハッセ原理の反例）
theorem S13_CH_corrected :
    (∃ x y : ℝ, x^2 + y^2 = 3) ∧
    (¬∃ x y : ZMod 4, x^2 + y^2 = 3) ∧  -- mod 4 での非存在
    (∃ x y : ZMod 3, x^2 + y^2 = 0) ∧
    (¬∃ x y : ℚ, x^2 + y^2 = 3)    := by     -- 有理数解の非存在
  sorry

end HW_IUT1_S13
