-- 第二・第三同型定理の段階的構築
-- Mode: explore
-- Goal: 第二・第三同型定理の必要補題を段階的に実装

import Mathlib.GroupTheory.QuotientGroup
import Mathlib.GroupTheory.Subgroup.Basic

namespace SecondThirdIsomorphism

variable {G : Type*} [Group G]

-- 補題1: H ⊔ K から K への自然な準同型写像
lemma subgroup_sup_quotient_map (H K : Subgroup G) [H.Normal] :
    ∃ φ : H ⊔ K →* K, ∀ h : H, ∀ k : K, φ ⟨h.val * k.val, Subgroup.mul_mem _ h.property k.property⟩ = k := by
  -- 自然な射影 φ : H ⊔ K → K を構成
  use {
    toFun := fun hk => ⟨hk.val, by
      -- hk ∈ H ⊔ K なので、∃ h ∈ H, k ∈ K s.t. hk = h * k
      -- この k 部分を抽出する必要があるが、表現の一意性が問題
      sorry -- TODO: reason="H ⊔ K の元の標準形表現が必要", missing_lemma="sup_canonical_form", priority=high
    ⟩,
    map_one' := by sorry -- TODO: reason="単位元の像", missing_lemma="identity_mapping", priority=medium
    map_mul' := fun x y => by sorry -- TODO: reason="準同型性", missing_lemma="homomorphism_property", priority=medium
  }
  intro h k
  sorry -- TODO: reason="具体的写像値の確認", missing_lemma="explicit_mapping_verification", priority=high

-- 補題2: 上記写像の良定義性（表現の一意性問題の解決）
lemma sup_quotient_map_well_defined (H K : Subgroup G) [H.Normal] :
    ∀ h₁ h₂ : H, ∀ k₁ k₂ : K, 
    h₁.val * k₁.val = h₂.val * k₂.val → k₁ = k₂ := by
  intro h₁ h₂ k₁ k₂ heq
  -- h₁ * k₁ = h₂ * k₂ ⟹ k₁ * k₂⁻¹ = h₁⁻¹ * h₂ ∈ H ⊓ K
  have h_eq : k₁.val * k₂.val⁻¹ = h₁.val⁻¹ * h₂.val := by
    -- rfl理由: 群の演算法則により代数的変形で一致
    rw [← heq]
    group
  -- k₁ * k₂⁻¹ ∈ K かつ h₁⁻¹ * h₂ ∈ H より、k₁ * k₂⁻¹ ∈ H ⊓ K
  have mem_inter : k₁.val * k₂.val⁻¹ ∈ H ⊓ K := by
    constructor
    · -- k₁ * k₂⁻¹ ∈ H の証明
      rw [h_eq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h₁.property) h₂.property
    · -- k₁ * k₂⁻¹ ∈ K の証明
      exact Subgroup.mul_mem _ k₁.property (Subgroup.inv_mem _ k₂.property)
  -- H ⊓ K ⊆ H, K なので、正規性により...
  sorry -- TODO: reason="交集合の性質を使った等号導出", missing_lemma="intersection_uniqueness", priority=high

-- 補題3: 写像の核の特定
lemma sup_quotient_map_kernel (H K : Subgroup G) [H.Normal] 
    (φ : H ⊔ K →* K) (h_def : ∀ h : H, ∀ k : K, φ ⟨h.val * k.val, Subgroup.mul_mem _ h.property k.property⟩ = k) :
    φ.ker = H.subgroupOf (H ⊔ K) := by
  ext x
  constructor
  · -- ker φ ⊆ H の方向
    intro hker
    -- φ(x) = 1 means x ∈ H when properly expressed
    sorry -- TODO: reason="核の元がHに属することの証明", missing_lemma="kernel_characterization", priority=high
  · -- H ⊆ ker φ の方向  
    intro hH
    -- h ∈ H なら φ(h) = 1 を示す
    sorry -- TODO: reason="Hの元の像が単位元であることの証明", missing_lemma="H_maps_to_identity", priority=medium

-- 補題4: 写像の全射性
lemma sup_quotient_map_surjective (H K : Subgroup G) [H.Normal]
    (φ : H ⊔ K →* K) (h_def : ∀ h : H, ∀ k : K, φ ⟨h.val * k.val, Subgroup.mul_mem _ h.property k.property⟩ = k) :
    Function.Surjective φ := by
  intro k
  -- 任意の k ∈ K に対して、1 * k = k の形で原像構成
  use ⟨k.val, Subgroup.mem_sup_right k.property⟩
  -- rfl理由: 定義により 1 ∈ H, k ∈ K での φ の値は k
  sorry -- TODO: reason="原像の具体的構成", missing_lemma="surjectivity_construction", priority=medium

-- 補題5: H ⊓ K の K における正規性
lemma intersection_normal_in_K (H K : Subgroup G) [H.Normal] :
    (H ⊓ K).subgroupOf K |>.Normal := by
  -- H が G で正規 ⟹ H ⊓ K が K で正規
  constructor
  intro n hn k hk
  -- k * n * k⁻¹ ∈ H ⊓ K を示す
  constructor
  · -- k * n * k⁻¹ ∈ H の証明（H の正規性使用）
    have : k.val * n.val * k.val⁻¹ ∈ H := by
      apply Subgroup.Normal.conj_mem
      exact hn.1
    exact this
  · -- k * n * k⁻¹ ∈ K の証明（K の部分群性）
    -- rfl理由: K の部分群性により k, k⁻¹ ∈ K, n ∈ K から閉包性で成立
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ k.property hn.2) (Subgroup.inv_mem _ k.property)

end SecondThirdIsomorphism