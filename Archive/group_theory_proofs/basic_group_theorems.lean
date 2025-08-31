import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic

-- 群の基本性質を確認
-- variable {G : Type*} [Group G]
-- #check @inv_mul_cancel_left G
-- #check @mul_inv_cancel G

/-!
# 群論の基本定理

このファイルでは、群論の基本的な定理を証明します。

## 内容
1. 単位元の一意性
2. 逆元の一意性
3. 左単位元と右単位元の一致
4. 左逆元と右逆元の一致
5. 簡約法則
6. 逆元の性質
-/

namespace GroupTheory

section BasicTheorems

variable {G : Type*} [Group G]

/-- 単位元の一意性: 群の単位元は唯一である -/
theorem identity_unique (e e' : G) 
    (h1 : ∀ a : G, e * a = a) 
    (h2 : ∀ a : G, e' * a = a) : 
    e = e' := by
  -- e'は左単位元なので、e' * e = e
  -- eは左単位元なので、e * e' = e'
  -- したがってe = e' * e = e' 
  calc e = e' * e := by rw [h2 e]
       _ = e'     := by rw [h1 e']

/-- 逆元の一意性: 各元の逆元は唯一である -/
theorem inverse_unique (a b c : G) 
    (hb : a * b = 1) 
    (hc : a * c = 1) : 
    b = c := by
  -- a * b = 1からa⁻¹ = bである
  -- a * c = 1からa⁻¹ = cである
  -- したがってb = c
  have h1 : a⁻¹ = b := by
    rw [← hb, ← mul_assoc, inv_mul_cancel_left]
  have h2 : a⁻¹ = c := by
    rw [← hc, ← mul_assoc, inv_mul_cancel_left]
  rw [← h1, h2]

/-- 左単位元は右単位元でもある -/
theorem left_identity_is_right_identity (e : G) 
    (h : ∀ a : G, e * a = a) : 
    ∀ a : G, a * e = a := by
  intro a
  -- 左単位元が存在するなら、それは1である
  have he_eq_one : e = 1 := by
    have h' : e * e = e := by rw [h e]
    have h_inv : e * e⁻¹ = 1 := mul_inv_cancel e
    calc e = e * 1 := by rw [mul_one]
         _ = e * (e * e⁻¹) := by rw [h_inv]
         _ = (e * e) * e⁻¹ := by rw [mul_assoc]
         _ = e * e⁻¹ := by rw [h']
         _ = 1 := by rw [h_inv]
  rw [he_eq_one, mul_one]

/-- 左逆元は右逆元でもある -/
theorem left_inverse_is_right_inverse (a b : G) 
    (h : b * a = 1) : 
    a * b = 1 := by
  -- b * a = 1からb = a⁻¹である
  have hb : b = a⁻¹ := by
    apply inverse_unique a
    · exact inv_mul_cancel a
    · exact h
  rw [hb, mul_inv_cancel]

/-- 左簡約法則 -/
theorem left_cancel (a b c : G) : 
    a * b = a * c → b = c := by
  intro h
  calc b = 1 * b := by rw [one_mul]
       _ = (a⁻¹ * a) * b := by rw [inv_mul_cancel]
       _ = a⁻¹ * (a * b) := by rw [mul_assoc]
       _ = a⁻¹ * (a * c) := by rw [h]
       _ = (a⁻¹ * a) * c := by rw [← mul_assoc]
       _ = 1 * c := by rw [inv_mul_cancel]
       _ = c := by rw [one_mul]

/-- 右簡約法則 -/
theorem right_cancel (a b c : G) : 
    b * a = c * a → b = c := by
  intro h
  calc b = b * 1 := by rw [mul_one]
       _ = b * (a * a⁻¹) := by rw [mul_inv_cancel]
       _ = (b * a) * a⁻¹ := by rw [← mul_assoc]
       _ = (c * a) * a⁻¹ := by rw [h]
       _ = c * (a * a⁻¹) := by rw [mul_assoc]
       _ = c * 1 := by rw [mul_inv_cancel]
       _ = c := by rw [mul_one]

/-- 逆元の逆元は元の元素に等しい -/
theorem inv_inv (a : G) : (a⁻¹)⁻¹ = a := by
  -- (a⁻¹)⁻¹は、a⁻¹の逆元
  -- a * a⁻¹ = 1 なので、aはa⁻¹の逆元
  -- 逆元の一意性より、(a⁻¹)⁻¹ = a
  apply inverse_unique a⁻¹
  · exact inv_mul_cancel a⁻¹
  · exact mul_inv_cancel a

/-- 積の逆元は逆順の積 -/
theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  -- (a * b) * (b⁻¹ * a⁻¹) = 1 を示す
  apply inverse_unique (a * b)
  · exact mul_inv_cancel (a * b)
  · calc (a * b) * (b⁻¹ * a⁻¹) = a * (b * (b⁻¹ * a⁻¹)) := by rw [mul_assoc]
                                _ = a * ((b * b⁻¹) * a⁻¹) := by rw [← mul_assoc b b⁻¹ a⁻¹]
                                _ = a * (1 * a⁻¹) := by rw [mul_inv_cancel]
                                _ = a * a⁻¹ := by rw [one_mul]
                                _ = 1 := by rw [mul_inv_cancel]

/-- 単位元の逆元は単位元自身 -/
theorem one_inv : (1 : G)⁻¹ = 1 := by
  apply inverse_unique 1
  · exact mul_inv_cancel 1
  · exact mul_one 1

end BasicTheorems

section PowersAndOrders

variable {G : Type*} [Group G]

/-- 冪の性質: a^(m+n) = a^m * a^n -/
theorem pow_add (a : G) (m n : ℕ) : a^(m + n) = a^m * a^n := by
  induction n with
  | zero => 
    simp [pow_zero, mul_one]
  | succ n ih =>
    calc a^(m + (n + 1)) = a^((m + n) + 1) := by rw [add_assoc]
                        _ = a^(m + n) * a := by rw [pow_succ]
                        _ = (a^m * a^n) * a := by rw [ih]
                        _ = a^m * (a^n * a) := by rw [mul_assoc]
                        _ = a^m * a^(n + 1) := by rw [← pow_succ]

/-- 冪の性質: (a^m)^n = a^(m*n) -/
theorem pow_mul (a : G) (m n : ℕ) : (a^m)^n = a^(m * n) := by
  induction n with
  | zero => 
    simp [pow_zero]
  | succ n ih =>
    calc (a^m)^(n + 1) = (a^m)^n * a^m := by rw [pow_succ]
                       _ = a^(m * n) * a^m := by rw [ih]
                       _ = a^(m * n + m) := by rw [← pow_add]
                       _ = a^(m * (n + 1)) := by ring_nf

end PowersAndOrders

section Subgroups

variable {G : Type*} [Group G]

/-- 部分群の判定条件 -/
structure IsSubgroup (H : Set G) where
  one_mem : (1 : G) ∈ H
  mul_mem : ∀ {a b}, a ∈ H → b ∈ H → a * b ∈ H
  inv_mem : ∀ {a}, a ∈ H → a⁻¹ ∈ H

/-- 部分群の交わりは部分群 -/
theorem subgroup_inter (H K : Set G) 
    (hH : IsSubgroup H) (hK : IsSubgroup K) : 
    IsSubgroup (H ∩ K) := by
  constructor
  · -- 1 ∈ H ∩ K
    constructor
    · exact hH.one_mem
    · exact hK.one_mem
  · -- a, b ∈ H ∩ K ⇒ a * b ∈ H ∩ K
    intro a b ha hb
    constructor
    · exact hH.mul_mem ha.1 hb.1
    · exact hK.mul_mem ha.2 hb.2
  · -- a ∈ H ∩ K ⇒ a⁻¹ ∈ H ∩ K
    intro a ha
    constructor
    · exact hH.inv_mem ha.1
    · exact hK.inv_mem ha.2

end Subgroups

end GroupTheory