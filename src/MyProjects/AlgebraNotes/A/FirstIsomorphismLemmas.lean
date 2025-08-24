/-
  🎓 群の第一同型定理：補題による段階的構築
  Mode: explore
  Goal: 群の第一同型定理の各補題を証明
-/

import Mathlib.GroupTheory.QuotientGroup.Basic

namespace FirstIsomorphismLemmas

open QuotientGroup

/-- 補題1：準同型写像の核は正規部分群である
    
    概念的意義：準同型写像の核は常に正規部分群となる
    ブルバキ的視点：群準同型の構造が自動的に生成する対称性
    証明の核心：g⁻¹ * ker * g ⊆ ker の普遍的成立
    
    数学的背景：
    - 任意の g ∈ G, k ∈ ker(f) に対して
    - f(g⁻¹kg) = f(g)⁻¹f(k)f(g) = f(g)⁻¹ * 1 * f(g) = 1
    - よって g⁻¹kg ∈ ker(f)
-/
lemma kernel_normal {G H : Type*} [Group G] [Group H] (f : G →* H) :
    (MonoidHom.ker f).Normal := by
  -- Mathlibの既存定理を使用
  -- library_search候補: MonoidHom.normal_ker
  exact MonoidHom.normal_ker f

/-- 補題2：商群の良定義性
    
    概念的意義：同値類上での写像の一意性
    ブルバキ的視点：商構造における代表元独立性  
    証明戦略：g₁⁻¹ * g₂ ∈ ker ↔ f(g₁⁻¹ * g₂) = 1
    
    数学的背景：
    - Setoid.r による同値関係：g₁ ~ g₂ ⟺ g₁⁻¹ * g₂ ∈ ker
    - 同値な元は同じ像を持つ：g₁ ~ g₂ ⟹ f(g₁) = f(g₂)  
    - これにより商群上の写像が well-defined
-/
lemma quotient_group_well_defined {G H : Type*} [Group G] [Group H] 
    (f : G →* H) :
    ∀ (g₁ g₂ : G), (QuotientGroup.mk g₁ : G ⧸ MonoidHom.ker f) = QuotientGroup.mk g₂ → f g₁ = f g₂ := by
  intro g₁ g₂ h_eq
  -- 商群での等価条件: [g₁] = [g₂] ⟺ g₁⁻¹ * g₂ ∈ ker  
  -- library_search候補: QuotientGroup.eq
  rw [QuotientGroup.eq] at h_eq
  -- g₁⁻¹ * g₂ ∈ ker f ⟺ f(g₁⁻¹ * g₂) = 1
  rw [MonoidHom.mem_ker] at h_eq
  -- f(g₁⁻¹ * g₂) = f(g₁)⁻¹ * f(g₂) = 1
  rw [map_mul, map_inv] at h_eq
  -- f(g₁)⁻¹ * f(g₂) = 1 ⟺ f(g₁) = f(g₂)
  exact inv_mul_eq_one.mp h_eq

/-- 補題3：誘導写像の存在
    
    概念的意義：商群から像への自然な写像の構成  
    ブルバキ的視点：普遍的性質による写像の一意的決定  
    構造的美：交換図式 G → H と G → G/ker → im(f) の一致
    
    数学的背景：
    - 商群 G/ker から像 im(f) への写像 φ が存在
    - φ([g]) = f(g) として定義される
    - この写像は well-defined (補題2により)
-/
lemma induced_map_exists {G H : Type*} [Group G] [Group H] (f : G →* H) :
    ∃ (φ : G ⧸ MonoidHom.ker f → f.range), 
    ∀ g : G, φ (QuotientGroup.mk g) = ⟨f g, by 
      rw [MonoidHom.mem_range]
      exact ⟨g, rfl⟩⟩ := by
  -- library_search候補: QuotientGroup.lift, rangeKerLift
  -- 商群からの lift を構成
  use fun q => q.lift (fun g => ⟨f g, by 
    rw [MonoidHom.mem_range]
    exact ⟨g, rfl⟩⟩) (by
    -- well-definedness の証明
    intro a b hab
    rw [leftRel_eq] at hab
    -- a⁻¹ * b ∈ ker f ⟹ f(a) = f(b)
    rw [MonoidHom.mem_ker] at hab
    rw [map_mul, map_inv] at hab
    -- f(a)⁻¹ * f(b) = 1 ⟹ f(a) = f(b)
    have : f a = f b := inv_mul_eq_one.mp hab
    congr 1
    exact this)
  intro g
  rfl

/-- 補助定義：標準的な誘導写像
    
    QuotientGroup.rangeKerLift を使用した具体的な写像の構成
-/
def classical_induced_map {G H : Type*} [Group G] [Group H] (f : G →* H) :
    G ⧸ MonoidHom.ker f →* f.range :=
  QuotientGroup.rangeKerLift f

/-- 補題4：誘導写像の準同型性
    
    概念的意義：商群の演算と像の演算の構造保存  
    ブルバキ的視点：群構造の射影による保存  
    技術的要点：商群での演算の代表元独立性
    
    数学的背景：
    - φ([g] * [h]) = φ([g*h]) = f(g*h) = f(g)*f(h) = φ([g]) * φ([h])
    - 商群の演算が像の演算に正しく対応
-/
lemma induced_map_is_hom {G H : Type*} [Group G] [Group H] (f : G →* H) :
    let φ := classical_induced_map f
    ∀ (x y : G ⧸ MonoidHom.ker f), φ (x * y) = φ x * φ y := by
  -- library_search候補: MonoidHom.map_mul
  intro x y
  -- rangeKerLift は準同型写像なので自動的に成立
  rfl

/-- 補題5：誘導写像の単射性
    
    概念的意義：異なる同値類は異なる像を持つ  
    ブルバキ的視点：商構造の最小性（余分な同一視なし）  
    証明の核心：φ(gker) = φ(hker) → f(g) = f(h) → g⁻¹h ∈ ker
    
    数学的背景：
    - φ([g]) = φ([h]) ⟹ f(g) = f(h) 
    - ⟹ f(g⁻¹h) = 1 
    - ⟹ g⁻¹h ∈ ker 
    - ⟹ [g] = [h]
-/
lemma induced_map_injective {G H : Type*} [Group G] [Group H] (f : G →* H) :
    let φ := classical_induced_map f
    Function.Injective φ := by
  -- library_search候補: rangeKerLift_injective
  exact QuotientGroup.rangeKerLift_injective f

/-- 補題6：誘導写像の全射性
    
    概念的意義：像の各元素が商群の元素と対応  
    ブルバキ的視点：構造射の範囲の完全一致  
    自明性の美：構成により自動的に成立
    
    数学的背景：
    - 任意の y ∈ im(f) に対して、∃g ∈ G, f(g) = y
    - よって φ([g]) = y となる [g] ∈ G/ker が存在
    - 構成的に全射性が保証される
-/
lemma induced_map_surjective {G H : Type*} [Group G] [Group H] (f : G →* H) :
    let φ := classical_induced_map f
    Function.Surjective φ := by
  -- library_search候補: rangeKerLift_surjective
  exact QuotientGroup.rangeKerLift_surjective f

/-- 補題7：群同型の構成
    
    概念的意義：前6補題の統合による同型写像の完成  
    ブルバキ的視点：普遍的構成による必然的同型  
    美的調和：準同型 → 核 → 商 → 像 の完璧な循環
    
    数学的背景：
    - 誘導写像 φ: G/ker → im(f) が存在（補題3）
    - φ は準同型（補題4）
    - φ は単射（補題5）かつ全射（補題6）
    - よって φ は群同型写像
-/
lemma construct_group_iso {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Nonempty (G ⧸ MonoidHom.ker f ≃* f.range) := by
  -- library_search候補: quotientKerEquivRange
  exact ⟨QuotientGroup.quotientKerEquivRange f⟩

/-- 第一同型定理：最終統合版
    
    ブルバキ流証明の完成形
    前述の7つの補題を統合して第一同型定理を導出
-/
theorem first_isomorphism_theorem {G H : Type*} [Group G] [Group H]
    (f : G →* H) :
    Nonempty (G ⧸ MonoidHom.ker f ≃* f.range) := by
  -- 補題7により直接証明
  exact construct_group_iso f

end FirstIsomorphismLemmas