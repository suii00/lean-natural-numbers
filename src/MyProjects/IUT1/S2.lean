import Mathlib

namespace HW_IUT1_S02

-- P01: 整数環の単元
theorem S2_P01 (u : Int) (h : IsUnit u) : u = 1 ∨ u = -1 := by
  exact (Int.isUnit_iff.mp h)

-- P02: 整数環は整域
theorem S2_P02 (a b : Int) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  exact (mul_eq_zero.mp h)

-- P03: 素数の基本性質
theorem S2_P03 (p : Nat) (hp : Nat.Prime p) : 2 ≤ p := by
  exact hp.two_le

-- P04: 最大公約数の存在
theorem S2_P04 : Nat.gcd 12 18 = 6 := by
  decide

-- P05: ベズー恒等式の具体例
theorem S2_P05 : ∃ (x y : Int), 15 * x + 10 * y = Nat.gcd 15 10 := by
  refine ⟨1, -1, ?_⟩
  have hgcd_nat : Nat.gcd 15 10 = 5 := by decide
  have hcalc : 15 * (1 : Int) + 10 * (-1 : Int) = (5 : Int) := by norm_num
  have hgcd_int : (Nat.gcd 15 10 : Int) = 5 := by exact_mod_cast hgcd_nat
  exact hcalc.trans hgcd_int.symm

-- CH: ユークリッドの補題の特殊ケース
theorem S2_CH (a b : Nat) (h : 3 ∣ a * b) : 3 ∣ a ∨ 3 ∣ b := by
  have hprime : Nat.Prime 3 := by decide
  have hmul : 3 ∣ a * b := h
  exact (hprime.dvd_mul).1 hmul

end HW_IUT1_S02
