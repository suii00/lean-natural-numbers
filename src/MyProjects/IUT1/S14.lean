import Mathlib

namespace HW_IUT1_S14

open scoped BigOperators

-- P01: p進 L関数の特殊値
theorem S14_P01 : IsUnit (-24 : ZMod 125) ∧ Nat.Coprime 24 5 := by
  constructor
  ·
    have h : (-24 : ZMod 125) * 26 = 1 := by decide
    refine ⟨⟨(-24 : ZMod 125), 26, h, ?_⟩, rfl⟩
    simpa [mul_comm] using h
  · decide

-- P02: クンマーの合同式（修正）
theorem S14_P02_corrected : padicNorm 5 (15/120 : ℚ) = 1 := by
  have hprime : Nat.Prime 5 := by decide
  haveI : Fact (Nat.Prime 5) := ⟨hprime⟩
  have hratio : (15/120 : ℚ) = 1 / 8 := by norm_num
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
  have hpow : (5 : ℚ) ^ (-padicValRat 5 (1 / 8 : ℚ)) = 1 := by simp [hval]
  have hquot : padicNorm 5 (1 / 8 : ℚ) = 1 := hnorm.trans hpow
  calc
    padicNorm 5 (15/120 : ℚ)
        = padicNorm 5 (1 / 8 : ℚ) := by simpa [hratio]
    _ = 1 := hquot

theorem S14_P02_alternative : padicNorm 5 (25/120 : ℚ) = 1/5 := by
  have hprime : Nat.Prime 5 := by decide
  haveI : Fact (Nat.Prime 5) := ⟨hprime⟩
  have hratio : (25/120 : ℚ) = 5 / 24 := by norm_num
  have hpadic24_nat : padicValNat 5 24 = 0 := padicValNat.eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 24)
  have hpadic24 : padicValRat 5 (24 : ℚ) = 0 := by
    simpa [hpadic24_nat] using (padicValRat.of_nat (p := 5) (n := 24))
  have hpadic5_nat : padicValNat 5 5 = 1 := padicValNat_self (p := 5)
  have hpadic5 : padicValRat 5 (5 : ℚ) = 1 := by
    simpa [hpadic5_nat] using (padicValRat.of_nat (p := 5) (n := 5))
  have hval : padicValRat 5 (5 / 24 : ℚ) = 1 := by
    have hq : (5 : ℚ) ≠ 0 := by norm_num
    have hr : (24 : ℚ) ≠ 0 := by norm_num
    simpa [hpadic5, hpadic24] using
      (padicValRat.div (p := 5) (q := (5 : ℚ)) (r := (24 : ℚ)) hq hr)
  have hnonzero : (5 / 24 : ℚ) ≠ 0 := by norm_num
  have hnorm := padicNorm.eq_zpow_of_nonzero (p := 5) (q := (5 / 24 : ℚ)) hnonzero
  have hpow : (5 : ℚ) ^ (-padicValRat 5 (5 / 24 : ℚ)) = (5 : ℚ)⁻¹ := by simp [hval]
  have hquot : padicNorm 5 (5 / 24 : ℚ) = (5 : ℚ)⁻¹ := hnorm.trans hpow
  calc
    padicNorm 5 (25/120 : ℚ)
        = padicNorm 5 (5 / 24 : ℚ) := by simpa [hratio]
    _ = (5 : ℚ)⁻¹ := hquot
    _ = 1 / 5 := by norm_num

-- P03: 局所ゼータ関数（修正）
theorem S14_P03_corrected : Fintype.card (Option (Fin 5)) = 6 := by
  simpa using (Fintype.card_option (Fin 5))

-- P04: p進測度
theorem S14_P04 : (5 : ℚ)^(-3 : ℤ) = 1/125 := by
  have hpow : (5 : ℚ) ^ (3 : ℕ) = 125 := by norm_num
  calc
    (5 : ℚ)^(-3 : ℤ)
        = ((5 : ℚ) ^ (3 : ℕ))⁻¹ := by
          simpa [Int.negSucc] using (zpow_negSucc (5 : ℚ) 2)
    _ = (125 : ℚ)⁻¹ := by simp [hpow]
    _ = 1 / 125 := by norm_num

-- P05: p進補間
theorem S14_P05 : (24 : ℤ) % 5 = 4 ∧ (25 : ℤ) % 25 = 0 := by
  constructor <;> norm_num

-- CH: 岩澤理論への入門
theorem S14_CH :
    (Nat.totient 5 = 4) ∧
    (∃ (ζ : ℂ), ζ^5 = 1 ∧ ζ ≠ 1 ∧ 1 + ζ + ζ^2 + ζ^3 + ζ^4 = 0) ∧
    (IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ)) := by
  classical
  constructor
  ·
    have hprime : Nat.Prime 5 := by decide
    simpa using Nat.totient_prime hprime
  constructor
  ·
    have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 5)) 5 :=
      Complex.isPrimitiveRoot_exp 5 (by decide : (5 : ℕ) ≠ 0)
    refine ⟨Complex.exp (2 * Real.pi * Complex.I / 5), ?_, ?_, ?_⟩
    · simpa using hζ.pow_eq_one
    · simpa using hζ.ne_one
    ·
      have hprod := geom_sum_mul_neg (Complex.exp (2 * Real.pi * Complex.I / 5)) 5
      have hpow : Complex.exp (2 * Real.pi * Complex.I / 5) ^ 5 = 1 := by
        simpa using hζ.pow_eq_one
      have hneq₁ : 1 ≠ Complex.exp (2 * Real.pi * Complex.I / 5) := by
        simpa [ne_comm] using hζ.ne_one
      have hneq : 1 - Complex.exp (2 * Real.pi * Complex.I / 5) ≠ 0 :=
        sub_ne_zero_of_ne hneq₁
      have hprod' :
          (∑ i ∈ Finset.range 5, Complex.exp (2 * Real.pi * Complex.I / 5) ^ i) *
              (1 - Complex.exp (2 * Real.pi * Complex.I / 5)) = 0 := by
        simpa [hpow] using hprod
      have hsum_zero :
          ∑ i ∈ Finset.range 5, Complex.exp (2 * Real.pi * Complex.I / 5) ^ i = 0 := by
        obtain hsum_zero | hcontr := mul_eq_zero.mp hprod'
        · exact hsum_zero
        · exact False.elim (hneq hcontr)
      simpa [Finset.range_add_one, pow_succ, pow_zero, add_comm, add_left_comm, add_assoc]
        using hsum_zero
  ·
    simpa using (CyclotomicField.isCyclotomicExtension (n := 5) (K := ℚ))

end HW_IUT1_S14
