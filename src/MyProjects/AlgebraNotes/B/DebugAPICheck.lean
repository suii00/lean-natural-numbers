-- デバッグ戦略 - API段階的チェック
-- Mode: stable
-- Goal: 根本的なAPI問題を特定し解決

import Mathlib.GroupTheory.QuotientGroup.Basic

namespace DebugAPICheck

variable {G : Type*} [Group G]

-- ===============================
-- 🔍 Section 1: 基本API存在確認
-- ===============================

-- ✅ 部分群の上確界API確認
#check @Subgroup.sup
#check @Subgroup.mem_sup_right
#check @Subgroup.mem_sup_left

-- ✅ 商群API確認
#check @QuotientGroup.mk
#check @QuotientGroup.lift
#check @QuotientGroup.quotientKerEquivRange

-- ===============================
-- 🔍 Section 2: 最小例でのテスト
-- ===============================

-- ✅ 上確界の基本動作確認
example (H K : Subgroup G) : H ⊔ K = Subgroup.sup H K := rfl

-- ✅ 下確界の基本動作確認
example (H K : Subgroup G) : H ⊓ K = Subgroup.inf H K := rfl

-- ✅ メンバーシップの動作確認
example (H K : Subgroup G) (h : H) : h.val ∈ H ⊔ K := Subgroup.mem_sup_left h.property

example (H K : Subgroup G) (k : K) : k.val ∈ H ⊔ K := Subgroup.mem_sup_right k.property

-- ===============================
-- 🔍 Section 3: 商群構成の段階的テスト
-- ===============================

-- ✅ 基本的な商群
example (N : Subgroup G) [N.Normal] : Type* := G ⧸ N

-- ✅ 部分群の商群（subgroupOf使用）
example (H K : Subgroup G) [H.Normal] : Type* := 
  (H ⊔ K) ⧸ H.subgroupOf (H ⊔ K)

-- ✅ 商群への写像
example (H K : Subgroup G) [H.Normal] : (H ⊔ K) →* (H ⊔ K) ⧸ H.subgroupOf (H ⊔ K) := 
  QuotientGroup.mk

-- ===============================
-- 🔍 Section 4: MonoidHomの構成テスト
-- ===============================

-- ✅ 包含写像の構成
def inclusion_map_test (H K : Subgroup G) : K →* (H ⊔ K) := 
  Subgroup.inclusion (le_sup_right : K ≤ H ⊔ K)

-- ✅ 合成写像の構成
def composition_test (H K : Subgroup G) [H.Normal] : K →* (H ⊔ K) ⧸ H.subgroupOf (H ⊔ K) := 
  QuotientGroup.mk.comp (inclusion_map_test H K)

-- ===============================
-- 🔍 Section 5: 核の計算テスト
-- ===============================

-- ✅ 核の基本性質
example (H K : Subgroup G) [H.Normal] : 
    (composition_test H K).ker ≤ K.subgroupOf (H ⊓ K) := by
  intro ⟨k, hk⟩ h_ker
  simp only [composition_test, MonoidHom.mem_ker, MonoidHom.comp_apply] at h_ker
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · -- k ∈ H の証明
    rw [QuotientGroup.eq_one_iff] at h_ker
    simp only [Subgroup.mem_subgroupOf] at h_ker
    exact h_ker
  · -- k ∈ K の証明（仮定より）
    exact hk

-- ===============================
-- 🔍 Section 6: Normal インスタンスのテスト
-- ===============================

-- ✅ H ⊓ K の K における正規性
instance intersection_normal_test (H K : Subgroup G) [H.Normal] : 
    (H ⊓ K).subgroupOf K |>.Normal := by
  constructor
  intro n hn k _
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hn ⊢
  exact ⟨Subgroup.Normal.conj_mem H hn.1 k.val, 
         Subgroup.mul_mem K (Subgroup.mul_mem K k.property hn.2) (Subgroup.inv_mem K k.property)⟩

-- ✅ H の H ⊔ K における正規性
instance H_normal_in_sup_test (H K : Subgroup G) [H.Normal] : 
    H.subgroupOf (H ⊔ K) |>.Normal := by
  constructor
  intro n hn x _
  simp only [Subgroup.mem_subgroupOf] at hn ⊢
  exact Subgroup.Normal.conj_mem H hn x.val

-- ===============================
-- 🔍 Section 7: 第一同型定理による解決テスト
-- ===============================

-- ✅ 第二同型定理の証明（簡略版）
theorem second_isomorphism_debug (H K : Subgroup G) [H.Normal] :
    K ⧸ (H ⊓ K).subgroupOf K ≃* (composition_test H K).range := by
  exact QuotientGroup.quotientKerEquivRange (composition_test H K)

-- ===============================
-- 🔍 Section 8: 動作確認
-- ===============================

#check second_isomorphism_debug
#check composition_test
#check inclusion_map_test

end DebugAPICheck