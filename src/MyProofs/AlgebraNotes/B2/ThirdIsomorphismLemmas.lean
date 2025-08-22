-- 🎓 第三同型定理に必要な10補題の体系的証明
-- Mode: explore
-- Goal: "第三同型定理の基盤となる補題群を段階的に構築"

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Finite.Card

variable {G : Type*} [Group G]

-- 🔥 補題1: Subgroup.Normal の継承性
-- 商群における部分群の像が正規部分群になることを示す
-- 💡 第三同型定理の基本定理（Mathlibから直接使用）
#check QuotientGroup.quotientQuotientEquivQuotient

-- ✅ 第三同型定理のメイン定理
def third_isomorphism_theorem (H K : Subgroup G) [H.Normal] [K.Normal] (h : H ≤ K) :
    (G ⧸ H) ⧸ (K.map (QuotientGroup.mk' H)) ≃* G ⧸ K :=
  QuotientGroup.quotientQuotientEquivQuotient H K h

-- ✅ 補助的な補題群

-- 補題1: 部分群の像は正規部分群 
lemma quotient_map_normal (H K : Subgroup G) [H.Normal] [K.Normal] (_ : H ≤ K) :
    (K.map (QuotientGroup.mk' H)).Normal := by
  -- Mathlibの自動推論を使用
  infer_instance

-- 補題2: 商群のサイズ関係（有限群の場合）
lemma quotient_card_relation (H K : Subgroup G) [H.Normal] [K.Normal] (h : H ≤ K) [Finite G] :
    Nat.card (G ⧸ K) = Nat.card ((G ⧸ H) ⧸ (K.map (QuotientGroup.mk' H))) := by
  exact Nat.card_congr (third_isomorphism_theorem H K h).toEquiv.symm

-- ✅ 実用的な例とテストケース

-- 例1: 有限群での応用（シンプル版）
section FiniteGroupExamples

-- 有限群での第三同型定理の応用例
example (H K : Subgroup G) [H.Normal] [K.Normal] (h : H ≤ K) [Finite G] :
    Nat.card (G ⧸ K) = Nat.card ((G ⧸ H) ⧸ (K.map (QuotientGroup.mk' H))) :=
  quotient_card_relation H K h

end FiniteGroupExamples

-- 例2: 一般的なテスト
example (H K : Subgroup G) [H.Normal] [K.Normal] (h : H ≤ K) :
    (G ⧸ H) ⧸ (K.map (QuotientGroup.mk' H)) ≃* G ⧸ K :=
  third_isomorphism_theorem H K h

-- 例3: 正規性の自動証明テスト
example (H K : Subgroup G) [H.Normal] [K.Normal] (h : H ≤ K) :
    (K.map (QuotientGroup.mk' H)).Normal :=
  quotient_map_normal H K h

-- ✅ 追加の補助補題群

-- 補題3: 商写像の全射性
lemma quotient_map_surjective (H : Subgroup G) [H.Normal] :
    Function.Surjective (QuotientGroup.mk' H) :=
  QuotientGroup.mk_surjective

-- 補題4: 核の特徴付け  
lemma kernel_characterization (H K : Subgroup G) [H.Normal] [K.Normal] (_ : H ≤ K) :
    (QuotientGroup.mk' (K.map (QuotientGroup.mk' H))).ker = 
    K.map (QuotientGroup.mk' H) := by
  rw [QuotientGroup.ker_mk']

-- 補題5: 誘導写像の性質
lemma induced_map_bijective (H K : Subgroup G) [H.Normal] [K.Normal] (h : H ≤ K) :
    Function.Bijective (third_isomorphism_theorem H K h).toMonoidHom := 
  (third_isomorphism_theorem H K h).bijective

-- 補題6: 商写像の単射性（kernel が自明な場合）
lemma quotient_map_injective_of_trivial_ker (H : Subgroup G) [H.Normal] :
    Function.Injective (QuotientGroup.mk' H) ↔ H = ⊥ := by
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']

-- 補題7: 第三同型定理の同型写像としての完全性
lemma third_iso_is_equiv (H K : Subgroup G) [H.Normal] [K.Normal] (h : H ≤ K) :
    Function.Bijective (third_isomorphism_theorem H K h) := by
  exact (third_isomorphism_theorem H K h).bijective

-- 補題8: lift の基本性質
lemma lift_commutes (H : Subgroup G) [H.Normal] {L : Type*} [Group L] 
    (φ : G →* L) (hφ : H ≤ φ.ker) :
    (QuotientGroup.lift H φ hφ).comp (QuotientGroup.mk' H) = φ := 
  QuotientGroup.lift_comp_mk' H φ hφ

-- 💡 最終テスト例
example (H K : Subgroup G) [H.Normal] [K.Normal] (h : H ≤ K) :
    -- 第三同型定理の基本性質を全て満たす
    ∃ (φ : (G ⧸ H) ⧸ (K.map (QuotientGroup.mk' H)) ≃* G ⧸ K),
    Function.Bijective φ ∧ 
    (K.map (QuotientGroup.mk' H)).Normal ∧
    Function.Surjective (QuotientGroup.mk' H) := by
  use third_isomorphism_theorem H K h
  exact ⟨(third_isomorphism_theorem H K h).bijective, 
         quotient_map_normal H K h, 
         quotient_map_surjective H⟩