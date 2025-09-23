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
      (padicValRat.of_nat (p := 5) (n := 5 ^ (n + 1)))
  simpa [padicNorm.eq_zpow_of_nonzero (p := 5) hq, hvalNat]

-- P02: p進整数の特徴付け
theorem S13_P02 : padicNorm 5 (2/3 : ℚ) ≤ 1 ∧ padicNorm 5 (1/5 : ℚ) > 1 := by
  classical
  haveI : Fact (Nat.Prime 5) := by decide
  have h2 : padicValRat 5 (2 : ℚ) = 0 := by
    have hnat : padicValNat 5 2 = 0 :=
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ 5 ∣ (2 : ℕ))
    simpa [hnat] using (padicValRat.of_nat (p := 5) (n := 2))
  have h3 : padicValRat 5 (3 : ℚ) = 0 := by
    have hnat : padicValNat 5 3 = 0 :=
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ 5 ∣ (3 : ℕ))
    simpa [hnat] using (padicValRat.of_nat (p := 5) (n := 3))
  have h5 : padicValRat 5 (5 : ℚ) = 1 := by
    simpa using padicValRat.self (p := 5) (by decide : 1 < 5)
  have h1 : padicValRat 5 (1 : ℚ) = 0 := by
    have hnat : padicValNat 5 1 = 0 :=
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ 5 ∣ (1 : ℕ))
    simpa [hnat] using (padicValRat.of_nat (p := 5) (n := 1))
  have hpadic23 : padicValRat 5 (2 / 3 : ℚ) = 0 := by
    simpa [h2, h3] using
      padicValRat.div (p := 5) (q := (2 : ℚ)) (r := (3 : ℚ)) (by norm_num) (by norm_num)
  have hpadicInv5 : padicValRat 5 ((5 : ℚ)⁻¹) = -1 := by
    simpa [one_div, h1, h5] using
      padicValRat.div (p := 5) (q := (1 : ℚ)) (r := (5 : ℚ)) (by norm_num) (by norm_num)
  have hnorm23 : padicNorm 5 (2 / 3 : ℚ) = 1 := by
    have hneq : (2 / 3 : ℚ) ≠ 0 := by norm_num
    calc
      padicNorm 5 (2 / 3 : ℚ)
          = ((5 : ℚ) ^ padicValRat 5 (2 / 3 : ℚ))⁻¹ := by
            simpa using padicNorm.eq_zpow_of_nonzero (p := 5) hneq
      _ = ((5 : ℚ) ^ (0 : ℤ))⁻¹ := by simpa [hpadic23]
      _ = 1 := by simp
  have hnorm15_inv : padicNorm 5 ((5 : ℚ)⁻¹) = (5 : ℚ) := by
    have hneq : ((5 : ℚ)⁻¹) ≠ 0 := by
      have hp : (5 : ℚ) ≠ 0 := by norm_num
      simpa using inv_ne_zero hp
    have hpne : (5 : ℚ) ≠ 0 := by norm_num
    calc
      padicNorm 5 ((5 : ℚ)⁻¹)
          = ((5 : ℚ) ^ padicValRat 5 ((5 : ℚ)⁻¹))⁻¹ := by
            simpa using padicNorm.eq_zpow_of_nonzero (p := 5) hneq
      _ = ((5 : ℚ) ^ (-1 : ℤ))⁻¹ := by simpa [hpadicInv5]
      _ = ((5 : ℚ) ^ (1 : ℕ)) := by
        simpa [zpow_neg, hpne]
      _ = (5 : ℚ) := by simpa
  have hnorm15 : padicNorm 5 (1 / 5 : ℚ) = (5 : ℚ) := by
    simpa [one_div, h1, h5] using hnorm15_inv
  constructor
  · simpa [hpadic23, zpow_zero]
  ·
    have hpne : (5 : ℚ) ≠ 0 := by norm_num
    have hlt : (1 : ℚ) < (5 : ℚ) := by norm_num
    simpa [hpadicInv5, zpow_neg, hpne, pow_one] using hlt

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

private lemma sum_sq_mod3_zero :
    ∀ a b : ZMod 3, a ^ 2 + b ^ 2 = 0 → a = 0 ∧ b = 0 := by
  decide

private lemma sq_zero_mod3 : ∀ c : ZMod 3, c ^ 2 = 0 → c = 0 := by
  decide

private lemma factor_three (a b c : ℤ)
    (h : a ^ 2 + b ^ 2 = 3 * c ^ 2) :
    ∃ a' b' c',
      a = 3 * a' ∧
        b = 3 * b' ∧
          c = 3 * c' ∧
            a' ^ 2 + b' ^ 2 = 3 * c' ^ 2 := by
  classical
  have hmod : (a : ZMod 3) ^ 2 + (b : ZMod 3) ^ 2 = 0 := by
    simpa [show (3 : ZMod 3) = 0 by decide] using
      congrArg (fun z : ℤ => (z : ZMod 3)) h
  obtain ⟨ha0, hb0⟩ := sum_sq_mod3_zero (a := (a : ZMod 3)) (b := (b : ZMod 3)) hmod
  have ha_dvd : (3 : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a 3).1 ha0
  have hb_dvd : (3 : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).1 hb0
  obtain ⟨a', ha'⟩ := ha_dvd
  obtain ⟨b', hb'⟩ := hb_dvd
  have h0 : 9 * (a' ^ 2 + b' ^ 2) = 3 * c ^ 2 := by
    simpa [ha', hb', pow_two, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using h
  have h0' : 3 * (3 * (a' ^ 2 + b' ^ 2)) = 3 * c ^ 2 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using h0
  have h1 : 3 * (a' ^ 2 + b' ^ 2) = c ^ 2 :=
    mul_left_cancel₀ (show (3 : ℤ) ≠ 0 by decide) h0'
  have hc_sq : (c : ZMod 3) ^ 2 = 0 := by
    have := congrArg (fun z : ℤ => (z : ZMod 3)) h1
    have hc' : (0 : ZMod 3) = (c : ZMod 3) ^ 2 := by
      simpa [show (3 : ZMod 3) = 0 by decide, pow_two, mul_comm, mul_left_comm, mul_assoc] using this
    simpa [eq_comm] using hc'
  have hc0 : (c : ZMod 3) = 0 := sq_zero_mod3 (c := (c : ZMod 3)) hc_sq
  have hc_dvd : (3 : ℤ) ∣ c := (ZMod.intCast_zmod_eq_zero_iff_dvd c 3).1 hc0
  obtain ⟨c', hc'⟩ := hc_dvd
  have h1' : 3 * (a' ^ 2 + b' ^ 2) = 9 * c' ^ 2 := by
    simpa [hc', pow_two, mul_comm, mul_left_comm, mul_assoc] using h1
  have h1'' : 3 * (a' ^ 2 + b' ^ 2) = 3 * (3 * c' ^ 2) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using h1'
  have h2 : a' ^ 2 + b' ^ 2 = 3 * c' ^ 2 :=
    mul_left_cancel₀ (show (3 : ℤ) ≠ 0 by decide) h1''
  refine ⟨a', b', c', ?_, ?_, ?_, h2⟩
  · simpa [ha']
  · simpa [hb']
  · simpa [hc']

private lemma factor_three_iter (a b c : ℤ)
    (h : a ^ 2 + b ^ 2 = 3 * c ^ 2) :
    ∀ n : ℕ, ∃ a' b' c',
      a = (3 : ℤ) ^ n * a' ∧
        b = (3 : ℤ) ^ n * b' ∧
          c = (3 : ℤ) ^ n * c' ∧
            a' ^ 2 + b' ^ 2 = 3 * c' ^ 2 := by
  classical
  refine Nat.rec ?base ?step
  · exact ⟨a, b, c, by simp, by simp, by simp, h⟩
  · intro n ih
    obtain ⟨a', b', c', ha', hb', hc', h'⟩ := ih
    obtain ⟨aa, bb, cc, haa, hbb, hcc, h''⟩ := factor_three a' b' c' h'
    refine ⟨aa, bb, cc, ?_, ?_, ?_, h''⟩
    · have hpow : (3 : ℤ) ^ (n + 1) = (3 : ℤ) ^ n * (3 : ℤ) := by
        simpa [pow_succ] using (pow_succ (3 : ℤ) n)
      simp [ha', haa, hpow, mul_comm, mul_left_comm, mul_assoc]
    · have hpow : (3 : ℤ) ^ (n + 1) = (3 : ℤ) ^ n * (3 : ℤ) := by
        simpa [pow_succ] using (pow_succ (3 : ℤ) n)
      simp [hb', hbb, hpow, mul_comm, mul_left_comm, mul_assoc]
    · have hpow : (3 : ℤ) ^ (n + 1) = (3 : ℤ) ^ n * (3 : ℤ) := by
        simpa [pow_succ] using (pow_succ (3 : ℤ) n)
      simp [hc', hcc, hpow, mul_comm, mul_left_comm, mul_assoc]

private lemma three_pow_ge_succ (n : ℕ) : 3 ^ n ≥ n + 1 := by
  induction' n with n ih
  · simp
  · have : 3 ^ (n + 1) = 3 * 3 ^ n := by simpa [pow_succ]
    calc
      3 ^ (n + 1) = 3 * 3 ^ n := this
      _ ≥ 3 * (n + 1) := by gcongr; exact ih
      _ = (n + 1) + 2 * (n + 1) := by ring
      _ ≥ (n + 1) + 1 := by
        have : 0 < 2 * (n + 1) := by
          exact Nat.mul_pos (by decide) (Nat.succ_pos _)
        exact add_le_add_left (Nat.succ_le_of_lt this) _

-- CH: Local obstruction example for x^2 + y^2 = 3
theorem S13_CH :
    (∃ x y : ℝ, x^2 + y^2 = 3) ∧
    (∃ x y : ZMod 5, x^2 + y^2 = 3) ∧
    (¬ ∃ x y : ZMod 8, x^2 + y^2 = 3) ∧
    (¬ ∃ x y : ℚ, x^2 + y^2 = 3) := by
  classical
  constructor
  · refine ⟨Real.sqrt 3, 0, ?_⟩
    simp [pow_two, Real.mul_self_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  constructor
  · refine ⟨(2 : ZMod 5), 2, ?_⟩
    decide
  constructor
  · exact by decide
  · intro h
    obtain ⟨x, y, hxy⟩ := h
    set a0 : ℤ := x.num * (y.den : ℤ)
    set b0 : ℤ := y.num * (x.den : ℤ)
    set c0 : ℤ := (x.den : ℤ) * (y.den : ℤ)
    have hxden_pos : 0 < x.den := Rat.den_pos _
    have hyden_pos : 0 < y.den := Rat.den_pos _
    have hxden_ne : (x.den : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hxden_pos)
    have hyden_ne : (y.den : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hyden_pos)
    have hc0_ne : c0 ≠ 0 := by
      dsimp [c0]
      exact mul_ne_zero hxden_ne hyden_ne
    let cQ : ℚ := (c0 : ℚ)
    have hx_mul : x * cQ = a0 := by
      simp [cQ, a0, c0, Rat.num_div_den]
    have hy_mul : y * cQ = b0 := by
      simp [cQ, b0, c0, Rat.num_div_den]
    have hx_sq : x ^ 2 * cQ ^ 2 = (a0 : ℚ) ^ 2 := by
      have := congrArg (fun t : ℚ => t ^ 2) hx_mul
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this
    have hy_sq : y ^ 2 * cQ ^ 2 = (b0 : ℚ) ^ 2 := by
      have := congrArg (fun t : ℚ => t ^ 2) hy_mul
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this
    have hscaled : x ^ 2 * cQ ^ 2 + y ^ 2 * cQ ^ 2 = 3 * cQ ^ 2 := by
      have := congrArg (fun t : ℚ => t * cQ ^ 2) hxy
      simpa [mul_add, add_comm, add_left_comm, add_assoc] using this
    have hclearQ : (a0 : ℚ) ^ 2 + (b0 : ℚ) ^ 2 = 3 * (c0 : ℚ) ^ 2 := by
      simpa [hx_sq, hy_sq] using hscaled
    have hclear : a0 ^ 2 + b0 ^ 2 = 3 * c0 ^ 2 := by
      exact_mod_cast hclearQ
    let n : ℕ := Int.natAbs c0 + 1
    obtain ⟨a1, b1, c1, ha1, hb1, hc1, h1⟩ := factor_three_iter a0 b0 c0 hclear n
    have hc_abs : Int.natAbs c0 = (3 : ℕ) ^ n * Int.natAbs c1 := by
      have := congrArg Int.natAbs hc1
      simp [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_ofNat] at this
      simpa using this
    have hpow_gt : (3 : ℕ) ^ n > Int.natAbs c0 := by
      have hge := three_pow_ge_succ n
      have : (3 : ℕ) ^ n ≥ Int.natAbs c0 + 1 := by
        simpa [n, add_comm, add_left_comm, add_assoc] using hge
      exact Nat.lt_of_le_of_lt this (Nat.lt_succ_self _)
    have hc1_abs : Int.natAbs c1 = 0 := by
      by_contra hc1_pos
      have hc1_pos' : 0 < Int.natAbs c1 := Nat.pos_of_ne_zero hc1_pos
      have hm : 1 ≤ Int.natAbs c1 := Nat.succ_le_of_lt hc1_pos'
      have hle : (3 : ℕ) ^ n ≤ (3 : ℕ) ^ n * Int.natAbs c1 := by
        simpa using Nat.mul_le_mul_left ((3 : ℕ) ^ n) hm
      have hle' : (3 : ℕ) ^ n ≤ Int.natAbs c0 := by
        simpa [hc_abs, Nat.mul_comm] using hle
      exact (not_le_of_gt hpow_gt) hle'
    have hc1_zero : c1 = 0 := Int.natAbs_eq_zero.mp hc1_abs
    have hc0_zero : c0 = 0 := by
      simpa [hc1_zero] using hc1
    have : (x.den : ℤ) * (y.den : ℤ) = 0 := by simpa [c0] using hc0_zero
    have : (x.den : ℤ) = 0 ∨ (y.den : ℤ) = 0 := by
      exact mul_eq_zero.mp this
    cases this with
    | inl hxzero => exact (hxden_ne hxzero).elim
    | inr hyzero => exact (hyden_ne hyzero).elim


end HW_IUT1_S13
