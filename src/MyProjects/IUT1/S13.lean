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

private lemma descent_sum_sq (a b c : ℤ) (hc : c ≠ 0) (h : a ^ 2 + b ^ 2 = 3 * c ^ 2) :
    ∃ a' b' c',
      c' ≠ 0 ∧
        a' ^ 2 + b' ^ 2 = 3 * c' ^ 2 ∧
        Int.natAbs c' < Int.natAbs c := by
  classical
  have hmod : (a : ZMod 3) ^ 2 + (b : ZMod 3) ^ 2 = 0 := by
    simpa using congrArg (fun z : ℤ => (z : ZMod 3)) h
  obtain ⟨ha0, hb0⟩ :=
    sum_sq_mod3_zero (a := (a : ZMod 3)) (b := (b : ZMod 3)) hmod
  have ha_dvd : (3 : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a 3).1 ha0
  have hb_dvd : (3 : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).1 hb0
  obtain ⟨a₁, ha₁⟩ := ha_dvd
  obtain ⟨b₁, hb₁⟩ := hb_dvd
  have h0 : 9 * (a₁ ^ 2 + b₁ ^ 2) = 3 * c ^ 2 := by
    simpa [ha₁, hb₁, pow_two, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using h
  have h0' : 3 * (3 * (a₁ ^ 2 + b₁ ^ 2)) = 3 * c ^ 2 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using h0
  have h1 : 3 * (a₁ ^ 2 + b₁ ^ 2) = c ^ 2 :=
    mul_left_cancel₀ (show (3 : ℤ) ≠ 0 by decide) h0'
  have hc_sq : (c : ZMod 3) ^ 2 = 0 := by
    have := congrArg (fun z : ℤ => (z : ZMod 3)) h1
    simpa using this
  have hc0 : (c : ZMod 3) = 0 := sq_zero_mod3 (c := (c : ZMod 3)) hc_sq
  have hc_dvd : (3 : ℤ) ∣ c := (ZMod.intCast_zmod_eq_zero_iff_dvd c 3).1 hc0
  obtain ⟨c₁, hc₁⟩ := hc_dvd
  have hc₁_ne : c₁ ≠ 0 := by
    intro hzero
    apply hc
    simpa [hc₁, hzero]
  have h1' : 3 * (a₁ ^ 2 + b₁ ^ 2) = 9 * c₁ ^ 2 := by
    simpa [hc₁, pow_two, mul_comm, mul_left_comm, mul_assoc] using h1
  have h1'' : 3 * (a₁ ^ 2 + b₁ ^ 2) = 3 * (3 * c₁ ^ 2) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using h1'
  have h2 : a₁ ^ 2 + b₁ ^ 2 = 3 * c₁ ^ 2 :=
    mul_left_cancel₀ (show (3 : ℤ) ≠ 0 by decide) h1''
  have hNat : Int.natAbs c = 3 * Int.natAbs c₁ := by
    simpa [hc₁, Int.natAbs_mul, Int.natAbs_natCast] using Int.natAbs_mul (3 : ℤ) c₁
  have hc₁_lt : Int.natAbs c₁ < Int.natAbs c := by
    have hc₁_pos : 0 < Int.natAbs c₁ := Int.natAbs_pos.2 hc₁_ne
    have : Int.natAbs c₁ < 3 * Int.natAbs c₁ :=
      Nat.lt_mul_of_pos_left hc₁_pos (by decide : 0 < 3)
    simpa [Nat.mul_comm, hNat] using this
  refine ⟨a₁, b₁, c₁, hc₁_ne, h2, hc₁_lt⟩

private lemma no_int_sum_sq (a b c : ℤ) (hc : c ≠ 0)
    (h : a ^ 2 + b ^ 2 = 3 * c ^ 2) : False := by
  classical
  have aux :
      ∀ n : ℕ,
        ∀ {a b c : ℤ},
          c ≠ 0 →
            a ^ 2 + b ^ 2 = 3 * c ^ 2 → Int.natAbs c = n → False :=
    by
      refine fun n => Nat.strong_induction_on n ?_
      intro k IH a b c hc' hEq hAbs
      by_cases hk : k = 0
      · have hc_zero : c = 0 := by
          have : Int.natAbs c = 0 := by simpa [hk] using hAbs
          exact Int.natAbs_eq_zero.mp this
        exact (hc' hc_zero).elim
      · obtain ⟨a', b', c', hc'', hEq', hlt⟩ :=
          descent_sum_sq a b c hc' hEq
        have hlt' : Int.natAbs c' < k := by
          have hAbs' : Int.natAbs c = k := hAbs
          simpa [hAbs'] using hlt
        exact IH _ hlt' hc'' hEq' rfl
  exact aux (Int.natAbs c) (a := a) (b := b) (c := c) hc h rfl

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
    set a : ℤ := x.num * (y.den : ℤ)
    set b : ℤ := y.num * (x.den : ℤ)
    set c : ℤ := (x.den : ℤ) * (y.den : ℤ)
    have hxden_ne : (x.den : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt (Rat.den_pos x))
    have hyden_ne : (y.den : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt (Rat.den_pos y))
    have hc_ne : c ≠ 0 := by
      dsimp [c]
      exact mul_ne_zero hxden_ne hyden_ne
    have hscaled : x ^ 2 * (c : ℚ) ^ 2 + y ^ 2 * (c : ℚ) ^ 2 = 3 * (c : ℚ) ^ 2 := by
      have := congrArg (fun t : ℚ => t * (c : ℚ) ^ 2) hxy
      simpa [pow_two, mul_add, add_comm, add_left_comm, add_assoc] using this
    have hx_mul : x * (c : ℚ) = a := by
      simp [a, c, Rat.num_div_den, mul_comm, mul_left_comm, mul_assoc]
    have hy_mul : y * (c : ℚ) = b := by
      simp [b, c, Rat.num_div_den, mul_comm, mul_left_comm, mul_assoc]
    have hx_sq : x ^ 2 * (c : ℚ) ^ 2 = (a : ℚ) ^ 2 := by
      simp [pow_two, hx_mul, mul_comm, mul_left_comm, mul_assoc]
    have hy_sq : y ^ 2 * (c : ℚ) ^ 2 = (b : ℚ) ^ 2 := by
      simp [pow_two, hy_mul, mul_comm, mul_left_comm, mul_assoc]
    have hclearQ :
        (a : ℚ) ^ 2 + (b : ℚ) ^ 2 = 3 * (c : ℚ) ^ 2 := by
      simpa [hx_sq, hy_sq] using hscaled
    have hclear : a ^ 2 + b ^ 2 = 3 * c ^ 2 := by
      exact_mod_cast hclearQ
    exact no_int_sum_sq a b c hc_ne hclear

end HW_IUT1_S13





