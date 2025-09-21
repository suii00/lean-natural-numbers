import Mathlib

namespace HW_IUT1_S05

open Ideal

-- P01: 5 が生成するイデアルは素イデアル
theorem S5_P01 : Ideal.IsPrime (Ideal.span ({(5 : ℤ)} : Set ℤ) : Ideal ℤ) := by
  classical
  have hne : (5 : ℤ) ≠ 0 := by norm_num
  have hprimeNat : Nat.Prime (Int.natAbs (5 : ℤ)) := by
    simpa [Int.natAbs_natCast] using (by decide : Nat.Prime 5)
  have hprime : Prime (5 : ℤ) := (Int.prime_iff_natAbs_prime).2 hprimeNat
  exact (Ideal.span_singleton_prime (α := ℤ) (p := (5 : ℤ)) hne).2 hprime

-- P02: 7 が生成するイデアルは極大イデアル
theorem S5_P02 : Ideal.IsMaximal (Ideal.span ({(7 : ℤ)} : Set ℤ) : Ideal ℤ) := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  simpa using (Int.ideal_span_isMaximal_of_prime (p := 7))

-- P03: 6 が生成するイデアルは素でない
theorem S5_P03 : ¬Ideal.IsPrime (Ideal.span ({(6 : ℤ)} : Set ℤ) : Ideal ℤ) := by
  classical
  have hne : (6 : ℤ) ≠ 0 := by norm_num
  have hnot : ¬Prime (6 : ℤ) := by
    simpa [Int.prime_iff_natAbs_prime, Int.natAbs_natCast] using
      (by decide : ¬Nat.Prime 6)
  intro hprime
  exact hnot ((Ideal.span_singleton_prime (α := ℤ) (p := (6 : ℤ)) hne).mp hprime)

-- P04: 極大イデアルなら素イデアル
theorem S5_P04 (I : Ideal ℤ) (h : Ideal.IsMaximal I) : Ideal.IsPrime I :=
  h.isPrime

-- P05: 零イデアルは素イデアル
theorem S5_P05 : Ideal.IsPrime (⊥ : Ideal ℤ) := by
  simpa using (Ideal.bot_prime (α := ℤ))

-- CH: 素数 p に対する (p) の極大性と素性
theorem S5_CH (p : Nat) (hp : Nat.Prime p) :
    Ideal.IsMaximal (Ideal.span ({(p : ℤ)} : Set ℤ) : Ideal ℤ) ∧
    Ideal.IsPrime (Ideal.span ({(p : ℤ)} : Set ℤ) : Ideal ℤ) := by
  classical
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  constructor
  · simpa using (Int.ideal_span_isMaximal_of_prime (p := p))
  ·
    have hne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hprimeNat : Nat.Prime (Int.natAbs (p : ℤ)) := by
      simpa [Int.natAbs_natCast] using hp
    have hprime : Prime (p : ℤ) := (Int.prime_iff_natAbs_prime).2 hprimeNat
    exact (Ideal.span_singleton_prime (α := ℤ) (p := (p : ℤ)) hne).2 hprime

end HW_IUT1_S05
