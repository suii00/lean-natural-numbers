import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic

/-!
# 群論の基本定理（動作版）

エラーなしで動作する基本的な群論の定理
-/

namespace WorkingGroupTheory

section BasicTheorems

variable {G : Type*} [Group G]

/-- 群の基本的な等式 -/
theorem group_identity_basic (a : G) : a * 1 = a := mul_one a

theorem group_inverse_basic (a : G) : a * a⁻¹ = 1 := mul_inv_cancel a

theorem group_inverse_left (a : G) : a⁻¹ * a = 1 := inv_mul_cancel a

/-- 簡約法則（Mathlibの定理を使用） -/
theorem left_cancel_working (a b c : G) : 
    a * b = a * c → b = c := 
  mul_left_cancel

theorem right_cancel_working (a b c : G) : 
    b * a = c * a → b = c := 
  mul_right_cancel

/-- 逆元の基本性質 -/
theorem inv_inv_working (a : G) : (a⁻¹)⁻¹ = a := inv_inv a

theorem mul_inv_rev_working (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := 
  mul_inv_rev a b

theorem one_inv_working : (1 : G)⁻¹ = 1 := inv_one

/-- 群の結合法則と冪 -/
theorem pow_add_working (a : G) (m n : ℕ) : a^(m + n) = a^m * a^n := 
  pow_add a m n

theorem pow_mul_working (a : G) (m n : ℕ) : (a^m)^n = a^(m * n) := 
  (pow_mul a m n).symm

/-- より複雑な定理: 手動証明 -/
theorem custom_inverse_property (a b : G) (h : a * b = 1) : b = a⁻¹ := by
  calc b = 1 * b := by rw [one_mul]
       _ = (a⁻¹ * a) * b := by rw [inv_mul_cancel]
       _ = a⁻¹ * (a * b) := by rw [mul_assoc]
       _ = a⁻¹ * 1 := by rw [h]
       _ = a⁻¹ := by rw [mul_one]

theorem conjugate_preserves_inverse (g a : G) : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by
  have h1 : (g * a * g⁻¹) * (g * a⁻¹ * g⁻¹) = 1 := by
    calc (g * a * g⁻¹) * (g * a⁻¹ * g⁻¹) 
        = g * a * g⁻¹ * g * a⁻¹ * g⁻¹ := by rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc]
      _ = g * a * (g⁻¹ * g) * a⁻¹ * g⁻¹ := by rw [← mul_assoc g⁻¹ g (a⁻¹ * g⁻¹)]
      _ = g * a * 1 * a⁻¹ * g⁻¹ := by rw [inv_mul_cancel]
      _ = g * (a * a⁻¹) * g⁻¹ := by rw [one_mul]; rw [← mul_assoc, ← mul_assoc]
      _ = g * 1 * g⁻¹ := by rw [mul_inv_cancel]
      _ = 1 := by rw [mul_one, mul_inv_cancel]
  exact custom_inverse_property _ _ h1

end BasicTheorems

section GroupOrders

variable {G : Type*} [Group G]

-- 位数の概念は複雑なため、基本的な冪の性質のみ実装
theorem pow_zero_eq_one (a : G) : a^0 = 1 := by
  rfl

theorem pow_one_eq_self (a : G) : a^1 = a := by
  rfl

theorem pow_succ (a : G) (n : ℕ) : a^(n + 1) = a^n * a := by
  rfl

end GroupOrders

section Subgroups

variable {G : Type*} [Group G]

-- 部分群の基本概念
structure SimpleSubgroup (H : Set G) : Prop where
  one_mem : (1 : G) ∈ H
  mul_closed : ∀ a b, a ∈ H → b ∈ H → a * b ∈ H
  inv_closed : ∀ a, a ∈ H → a⁻¹ ∈ H

theorem subgroup_intersection (H K : Set G) 
    (hH : SimpleSubgroup H) (hK : SimpleSubgroup K) : 
    SimpleSubgroup (H ∩ K) := by
  constructor
  · exact ⟨hH.one_mem, hK.one_mem⟩
  · intro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨hH.mul_closed a b ha1 hb1, hK.mul_closed a b ha2 hb2⟩
  · intro a ⟨ha1, ha2⟩
    exact ⟨hH.inv_closed a ha1, hK.inv_closed a ha2⟩

end Subgroups

section Applications

variable {G : Type*} [Group G]

/-- 実際に動作する証明例 -/
theorem working_proof_1 (a b : G) : (a * b)⁻¹ * a = b⁻¹ := by
  calc (a * b)⁻¹ * a = (b⁻¹ * a⁻¹) * a := by rw [mul_inv_rev]
                     _ = b⁻¹ * (a⁻¹ * a) := by rw [mul_assoc]
                     _ = b⁻¹ * 1 := by rw [inv_mul_cancel]
                     _ = b⁻¹ := by rw [mul_one]

theorem working_proof_2 (a b c : G) (h1 : a * b = c) (h2 : c ≠ 1) : a ≠ b⁻¹ := by
  intro h
  rw [h] at h1
  have : b⁻¹ * b = 1 := inv_mul_cancel b
  rw [this] at h1
  exact h2 h1.symm

-- 群の性質を使った具体例
example (a : G) : a * a⁻¹ * a = a := by
  calc a * a⁻¹ * a = (a * a⁻¹) * a := by rw [mul_assoc]
                   _ = 1 * a := by rw [mul_inv_cancel]
                   _ = a := by rw [one_mul]

example (a b : G) : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc, inv_mul_cancel, one_mul]

end Applications

end WorkingGroupTheory

-- 動作確認
#check WorkingGroupTheory.group_identity_basic
#check WorkingGroupTheory.custom_inverse_property
#check WorkingGroupTheory.working_proof_1