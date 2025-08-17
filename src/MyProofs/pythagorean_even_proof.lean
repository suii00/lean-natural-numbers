-- 環論的な偶奇性の定義
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

theorem pythagorean_triple_has_even : ∀ a b c : ℕ,
  a > 0 → b > 0 → c > 0 → a^2 + b^2 = c^2 →
  (Even a ∨ Even b ∨ Even c) := by
  intro a b c _ _ _ h_pyth
  -- 背理法で証明: 全て奇数と仮定
  by_contra h_not
  push_neg at h_not
  
  -- 全て奇数であることから、2で割り切れない
  have ha_odd : ¬Even a := h_not.1
  have hb_odd : ¬Even b := h_not.2.1  
  have hc_odd : ¬Even c := h_not.2.2
  
  -- 偶数でない ⟺ 2で割り切れない
  rw [even_iff_two_dvd] at ha_odd hb_odd hc_odd
  
  -- 奇数なら mod 2 = 1
  have ha_mod2 : a % 2 = 1 := by
    have h := Nat.mod_two_eq_zero_or_one a
    cases h with
    | inl h => 
      exfalso
      apply ha_odd
      exact Nat.dvd_iff_mod_eq_zero.mpr h
    | inr h => exact h
    
  have hb_mod2 : b % 2 = 1 := by
    have h := Nat.mod_two_eq_zero_or_one b
    cases h with
    | inl h => 
      exfalso
      apply hb_odd
      exact Nat.dvd_iff_mod_eq_zero.mpr h
    | inr h => exact h
    
  have hc_mod2 : c % 2 = 1 := by
    have h := Nat.mod_two_eq_zero_or_one c
    cases h with
    | inl h => 
      exfalso
      apply hc_odd
      exact Nat.dvd_iff_mod_eq_zero.mpr h
    | inr h => exact h
  
  -- 奇数の平方は mod 4 で 1
  have ha_sq_mod4 : a^2 % 4 = 1 := by
    have : ∃ k, a = 2 * k + 1 := by
      use a / 2
      have eq : a = 2 * (a / 2) + a % 2 := (Nat.div_add_mod a 2).symm
      rw [ha_mod2] at eq
      exact eq
    obtain ⟨k, hk⟩ := this
    rw [hk]
    ring_nf
    norm_num
    
  have hb_sq_mod4 : b^2 % 4 = 1 := by
    have : ∃ k, b = 2 * k + 1 := by
      use b / 2
      have eq : b = 2 * (b / 2) + b % 2 := (Nat.div_add_mod b 2).symm
      rw [hb_mod2] at eq
      exact eq
    obtain ⟨k, hk⟩ := this
    rw [hk]
    ring_nf
    norm_num
    
  have hc_sq_mod4 : c^2 % 4 = 1 := by
    have : ∃ k, c = 2 * k + 1 := by
      use c / 2
      have eq : c = 2 * (c / 2) + c % 2 := (Nat.div_add_mod c 2).symm
      rw [hc_mod2] at eq
      exact eq
    obtain ⟨k, hk⟩ := this
    rw [hk]
    ring_nf
    norm_num
  
  -- a^2 + b^2 ≡ 2 (mod 4) だが c^2 ≡ 1 (mod 4) で矛盾
  have h_sum : (a^2 + b^2) % 4 = 2 := by
    calc (a^2 + b^2) % 4 = (a^2 % 4 + b^2 % 4) % 4 := Nat.add_mod _ _ _
    _ = (1 + 1) % 4 := by rw [ha_sq_mod4, hb_sq_mod4]
    _ = 2 := by norm_num
    
  rw [h_pyth] at h_sum
  rw [hc_sq_mod4] at h_sum
  -- 2 = 1 という矛盾
  exact absurd h_sum (by norm_num)

-- 検証例: 3-4-5 のピタゴラス数
example : 3^2 + 4^2 = 5^2 := by norm_num

example : Even 4 := by
  rw [even_iff_two_dvd]
  norm_num

-- 検証例: 5-12-13 のピタゴラス数  
example : 5^2 + 12^2 = 13^2 := by norm_num

example : Even 12 := by
  rw [even_iff_two_dvd]
  norm_num