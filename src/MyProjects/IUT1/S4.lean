import Mathlib

namespace HW_IUT1_S04

-- P01: 除法定理の基本
theorem S4_P01 : 17 = 5 * 3 + 2 ∧ 0 ≤ 2 ∧ 2 < 5 := by
  constructor
  · decide
  · constructor <;> decide

-- P02: 剰余の非負性
theorem S4_P02 (n m : Nat) (hm : 0 < m) : n % m < m := by
  exact Nat.mod_lt _ hm

-- P03: 除法の一意性（剰余の一意性）
theorem S4_P03 (a b q₁ q₂ r₁ r₂ : Nat) (hb : 0 < b)
    (h₁ : a = b * q₁ + r₁) (h₂ : a = b * q₂ + r₂)
    (hr₁ : r₁ < b) (hr₂ : r₂ < b) : r₁ = r₂ := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have remainder_unique :
      ∀ {q₁ q₂ r₁ r₂ : Nat},
        q₁ ≤ q₂ → b * q₁ + r₁ = b * q₂ + r₂ →
          r₁ < b → r₂ < b → r₁ = r₂ := by
    intro q₁' q₂' r₁' r₂' hle hsum hr₁' hr₂'
    have hsum' : b * q₁' + r₁' = b * q₁' + (b * (q₂' - q₁') + r₂') := by
      have hmul : b * q₂' = b * q₁' + b * (q₂' - q₁') := by
        calc
          b * q₂' = b * (q₁' + (q₂' - q₁')) := by
            simp [Nat.add_sub_of_le hle]
          _ = b * q₁' + b * (q₂' - q₁') := by
            simp [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      simpa [hmul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum
    have hrem : r₁' = b * (q₂' - q₁') + r₂' :=
      Nat.add_left_cancel hsum'
    have hmul_zero : b * (q₂' - q₁') = 0 := by
      by_contra hmul_ne
      have hdiff_ne : q₂' - q₁' ≠ 0 := by
        intro hzero
        apply hmul_ne
        simp [hzero]
      have hdiff_pos : 0 < q₂' - q₁' := Nat.pos_of_ne_zero hdiff_ne
      have hdiff_ge : 1 ≤ q₂' - q₁' := Nat.succ_le_of_lt hdiff_pos
      have hb_le_prod : b ≤ b * (q₂' - q₁') := by
        have := Nat.mul_le_mul_left b hdiff_ge
        simpa [Nat.one_mul] using this
      have hprod_le : b * (q₂' - q₁') ≤ r₁' := by
        have := Nat.le_add_right (b * (q₂' - q₁')) r₂'
        simpa [hrem] using this
      have hle : b ≤ r₁' := le_trans hb_le_prod hprod_le
      exact (not_lt_of_ge hle) hr₁'
    have hdiff_zero : q₂' - q₁' = 0 := by
      rcases Nat.mul_eq_zero.mp hmul_zero with hzero | hzero
      · cases hb0 hzero
      · exact hzero
    have hqeq : q₂' = q₁' := by
      have := (Nat.add_sub_of_le hle).symm
      simpa [hdiff_zero] using this
    simpa [hrem, hdiff_zero]
  obtain hle | hle := le_total q₁ q₂
  · exact remainder_unique hle (h₁.symm.trans h₂) hr₁ hr₂
  · have := remainder_unique hle (h₂.symm.trans h₁) hr₂ hr₁
    simpa using this.symm

-- P04: ユークリッド互除法の一歩
theorem S4_P04 : Nat.gcd 21 15 = Nat.gcd 15 (21 % 15) := by
  simpa using Nat.gcd_rec 21 15

-- P05: 整除と剰余の関係
theorem S4_P05 (a b : Nat) (hb : 0 < b) (h : b ∣ a) : a % b = 0 := by
  obtain ⟨k, rfl⟩ := h
  have hb0 : b ≠ 0 := ne_of_gt hb
  simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, hb0]

-- CH: 拡張ユークリッド互除法
theorem S4_CH : ∃ (x y : Int), 35 * x + 15 * y = Nat.gcd 35 15 ∧
    Int.natAbs x ≤ 3 ∧ Int.natAbs y ≤ 7 := by
  refine ⟨1, -2, ?_, ?_, ?_⟩
  · have hgcd : Nat.gcd 35 15 = 5 := by decide
    calc
      35 * (1 : Int) + 15 * (-2 : Int)
          = 5 := by norm_num
      _ = (Nat.gcd 35 15 : Int) := by simpa [hgcd]
  · simpa using (show Int.natAbs (1 : Int) ≤ 3 by decide)
  · simpa using (show Int.natAbs (-2 : Int) ≤ 7 by decide)

end HW_IUT1_S04







