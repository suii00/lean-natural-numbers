/-
課題H: 戦術習得による構成的証明
段階3: 非自明な関係
-/

import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Prime

namespace TacticLearningStage3

variable {R : Type*} [CommRing R]

/-! ## 段階3: 非自明な関係 -/

-- 非自明な関係1: 素イデアルの特徴付け（部分的）
lemma prime_ideal_characterization (P : Ideal R) [P.IsPrime] (a b : R) :
    a * b ∈ P → a ∈ P ∨ b ∈ P := 
  Ideal.IsPrime.mem_or_mem ‹P.IsPrime› 

-- 非自明な関係2: 素イデアルは真のイデアル
lemma prime_ideal_proper (P : Ideal R) [P.IsPrime] : P ≠ ⊤ := 
  Ideal.IsPrime.ne_top ‹P.IsPrime›

-- 非自明な関係3: 1は素イデアルに含まれない
lemma one_not_in_prime_ideal (P : Ideal R) [P.IsPrime] : (1 : R) ∉ P := by
  intro h_one_in_P  -- 仮定: 1 ∈ P を導入
  have h_top : P = ⊤ := Ideal.eq_top_of_isUnit_mem P h_one_in_P isUnit_one
  exact Ideal.IsPrime.ne_top ‹P.IsPrime› h_top  -- 素イデアルは ⊤ でないという性質と矛盾

-- 非自明な関係4: より直接的な素イデアルの性質証明  
lemma prime_ideal_contains_product_of_contains_factor (P : Ideal R) [P.IsPrime] 
    (a b : R) (ha : a ∈ P) : a * b ∈ P := by
  exact P.mul_mem_right b ha  -- イデアルのインスタンスメソッドを使用

-- 非自明な関係5: イデアルの和の美しい性質（創造的構成）
lemma ideal_sup_beauty (I J : Ideal R) (a b : R) 
    (ha : a ∈ I) (hb : b ∈ J) : a + b ∈ I ⊔ J := by
  -- 和の本質: 両方の要素を含む最小のイデアル
  apply Ideal.add_mem
  · exact Ideal.mem_sup_left ha  -- I ⊆ I ⊔ J より a ∈ I ⊔ J  
  · exact Ideal.mem_sup_right hb -- J ⊆ I ⊔ J より b ∈ I ⊔ J

-- 非自明な関係6: イデアルの包含関係
lemma ideal_le_sup_left (I J : Ideal R) : I ≤ I ⊔ J := by
  exact le_sup_left

-- 非自明な関係7: 素イデアルと最大イデアルの関係  
lemma maximal_is_prime (M : Ideal R) [M.IsMaximal] : M.IsPrime := by
  infer_instance  -- 型クラス推論で自動解決

-- 非自明な関係8: より複雑な戦術組み合わせ（創造的アプローチ）
lemma advanced_prime_ideal_property (P : Ideal R) [P.IsPrime] (a b c : R) :
    a * b * c ∈ P → (a ∈ P ∨ b ∈ P ∨ c ∈ P) := by
  intro h_abc_in_P
  -- 美しい対称性を活用: a * b * c は既に左結合
  -- Leanの演算子優先順位により (a * b) * c として解釈される
  cases' Ideal.IsPrime.mem_or_mem ‹P.IsPrime› h_abc_in_P with h_ab h_c
  · -- Case 1: a * b ∈ P → さらに分解
    cases' Ideal.IsPrime.mem_or_mem ‹P.IsPrime› h_ab with h_a h_b
    · left; exact h_a      -- a ∈ P
    · right; left; exact h_b  -- b ∈ P  
  · right; right; exact h_c   -- c ∈ P

-- 非自明な関係9: 戦術練習のための基本的論理操作
lemma logical_equivalence_practice (P : Ideal R) [P.IsPrime] :
    (∀ a b : R, a * b ∈ P → a ∈ P ∨ b ∈ P) ↔ 
    (∀ x y : R, x * y ∈ P → ¬(x ∉ P ∧ y ∉ P)) := by
  constructor
  · intro h x y hxy hnot
    cases' hnot with hx_not hy_not
    cases' h x y hxy with hx hy
    · exact hx_not hx
    · exact hy_not hy
  · intro h a b hab
    by_contra h_neither
    push_neg at h_neither
    exact h a b hab ⟨h_neither.1, h_neither.2⟩

end TacticLearningStage3