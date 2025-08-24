/-
課題H: 戦術習得による構成的証明  
段階2: constructor, intro, rw戦術の習得
-/

import Mathlib.RingTheory.Ideal.Basic

namespace TacticLearningStage2

variable {R : Type*} [CommRing R]

/-! ## 段階2: 実際の証明戦術の習得 -/

-- 戦術習得4: 同値証明でのconstructor使用
lemma mem_span_singleton_iff (r s : R) :
    r ∈ Ideal.span {s} ↔ s ∣ r := by
  constructor  -- ↔を2つの方向に分解
  · -- 左から右: r ∈ Ideal.span {s} → s ∣ r
    intro hr   -- 仮定 hr : r ∈ Ideal.span {s} を導入
    rw [Ideal.mem_span_singleton] at hr  -- 定義を書き換え
    exact hr   -- hrがまさに s ∣ r の証明
  · -- 右から左: s ∣ r → r ∈ Ideal.span {s}  
    intro h_div  -- h_div : s ∣ r を導入
    rw [Ideal.mem_span_singleton]  -- 目標を書き換え
    exact h_div  -- 証明を提供

-- 戦術習得5: 論理構造の分解と構成
lemma ideal_mem_inter_iff (I J : Ideal R) (r : R) :
    r ∈ I ⊓ J ↔ r ∈ I ∧ r ∈ J := by
  constructor  -- ↔を分解
  · -- 左から右
    intro h    -- h : r ∈ I ⊓ J を導入
    exact Ideal.mem_inf.mp h  -- 交集合の定義を使用
  · -- 右から左  
    intro ⟨hI, hJ⟩  -- ∧を分解: hI : r ∈ I, hJ : r ∈ J
    exact Ideal.mem_inf.mpr ⟨hI, hJ⟩  -- 交集合の定義を使用

-- 戦術習得6: より複雑な書き換え証明
lemma ideal_span_union (s t : Set R) :
    Ideal.span (s ∪ t) = Ideal.span s ⊔ Ideal.span t := by
  rw [Ideal.span_union]  -- Mathlibの定理を直接適用

-- 戦術習得7: 段階的な書き換えの練習
lemma ideal_span_insert (s : Set R) (r : R) :
    Ideal.span (insert r s) = Ideal.span {r} ⊔ Ideal.span s := by
  rw [← Set.singleton_union]  -- {r} ∪ s = insert r s を逆方向に使用
  rw [Ideal.span_union]       -- 和集合のスパンは上限

end TacticLearningStage2