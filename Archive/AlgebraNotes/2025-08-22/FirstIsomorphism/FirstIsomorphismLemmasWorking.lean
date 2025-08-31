/-
  🎓 群の第一同型定理：補題による段階的構築
  Mode: explore - Working version  
  Goal: 群の第一同型定理の各補題を証明

  学習アプローチ：
  - 各補題はMathlib4の既存定理を活用
  - 教育的価値を重視した詳細な説明
  - ブルバキ流の構造的理解を促進
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
    
    library_search使用定理：MonoidHom.normal_ker
-/
lemma kernel_normal {G H : Type*} [Group G] [Group H] (f : G →* H) :
    (MonoidHom.ker f).Normal := by
  -- Mathlibの既存定理を使用
  exact MonoidHom.normal_ker f

/-- 補題2：商群の良定義性（簡化版）
    
    概念的意義：同値類上での写像の一意性
    ブルバキ的視点：商構造における代表元独立性  
    
    数学的背景：
    - QuotientGroup.lift により自動的に well-defined
    - 内部的に leftRel による同値関係を処理
-/
lemma quotient_group_lift_works {G H : Type*} [Group G] [Group H] (f : G →* H) :
    ∃ (φ : G ⧸ MonoidHom.ker f →* H), 
    ∀ g : G, φ (QuotientGroup.mk g) = f g := by
  -- QuotientGroup.lift を使用
  use QuotientGroup.lift f (MonoidHom.normal_ker f)
  intro g
  exact QuotientGroup.lift_mk f (MonoidHom.normal_ker f) g

/-- 補題3：誘導写像の存在（Mathlib版）
    
    概念的意義：商群から像への自然な写像の構成  
    ブルバキ的視点：普遍的性質による写像の一意的決定  
    構造的美：交換図式 G → H と G → G/ker → im(f) の一致
    
    library_search使用定理：QuotientGroup.rangeKerLift
-/
lemma induced_map_exists {G H : Type*} [Group G] [Group H] (f : G →* H) :
    ∃ (φ : G ⧸ MonoidHom.ker f →* f.range), 
    ∀ g : G, φ (QuotientGroup.mk g) = ⟨f g, by simp [MonoidHom.mem_range, exists_apply_eq_apply]⟩ := by
  -- rangeKerLift を使用
  use QuotientGroup.rangeKerLift f
  intro g
  simp [QuotientGroup.rangeKerLift_mk]

/-- 補助定義：標準的な誘導写像
    
    QuotientGroup.rangeKerLift を使用した具体的な写像の構成
-/
def classical_induced_map {G H : Type*} [Group G] [Group H] (f : G →* H) :
    G ⧸ MonoidHom.ker f →* f.range :=
  QuotientGroup.rangeKerLift f

/-- 補題4：誘導写像の準同型性
    
    概念的意義：商群の演算と像の演算の構造保存  
    ブルバキ的視点：群構造の射影による保存  
    
    自明性の美：rangeKerLift は構成により MonoidHom
-/
lemma induced_map_is_hom {G H : Type*} [Group G] [Group H] (f : G →* H) :
    MonoidHom (classical_induced_map f) := by
  -- rangeKerLift は定義により MonoidHom
  exact classical_induced_map f

/-- 補題5：誘導写像の単射性
    
    概念的意義：異なる同値類は異なる像を持つ  
    ブルバキ的視点：商構造の最小性（余分な同一視なし）  
    
    library_search使用定理：rangeKerLift_injective
-/
lemma induced_map_injective {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Function.Injective (classical_induced_map f) := by
  exact QuotientGroup.rangeKerLift_injective f

/-- 補題6：誘導写像の全射性
    
    概念的意義：像の各元素が商群の元素と対応  
    ブルバキ的視点：構造射の範囲の完全一致  
    
    library_search使用定理：rangeKerLift_surjective
-/
lemma induced_map_surjective {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Function.Surjective (classical_induced_map f) := by
  exact QuotientGroup.rangeKerLift_surjective f

/-- 補題7：群同型の構成
    
    概念的意義：前補題の統合による同型写像の完成  
    ブルバキ的視点：普遍的構成による必然的同型  
    美的調和：準同型 → 核 → 商 → 像 の完璧な循環
    
    library_search使用定理：quotientKerEquivRange
-/
lemma construct_group_iso {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Nonempty (G ⧸ MonoidHom.ker f ≃* f.range) := by
  exact ⟨QuotientGroup.quotientKerEquivRange f⟩

/-- 第一同型定理：最終統合版
    
    ブルバキ流証明の完成形
    前述の7つの補題を統合して第一同型定理を導出
    
    教育的価値：各補題の役割を明確化
    - 補題1: 核の正規性 → 商群の構成可能性
    - 補題2-3: 誘導写像の存在 → 構造の射影
    - 補題4: 準同型性 → 群構造の保存  
    - 補題5-6: 双射性 → 構造の完全対応
    - 補題7: 同型の統合 → 第一同型定理の完成
-/
theorem first_isomorphism_theorem {G H : Type*} [Group G] [Group H]
    (f : G →* H) :
    Nonempty (G ⧸ MonoidHom.ker f ≃* f.range) := by
  -- 補題7により直接証明
  exact construct_group_iso f

/-- 実例での確認：整数群の例
    
    教育的価値：抽象理論の具体的応用
    - G = ℤ, H = ℤ/4ℤ, f: n ↦ n mod 4
    - ker f = 4ℤ (4の倍数)
    - im f = ℤ/4ℤ 
    - 第一同型定理: ℤ/4ℤ ≃ ℤ/4ℤ
-/
example : Nonempty (ℤ ⧸ (4 : ℤ).zmultiples ≃* AddSubgroup.zmultiples (1 : ZMod 4)) := by
  -- AddMonoidHom.emod_nat の適用
  let f : ℤ →+ ZMod 4 := AddMonoidHom.mk ZMod.int_cast
  -- 第一同型定理の直接適用
  sorry -- TODO: reason="need concrete example setup", missing_lemma="AddMonoidHom.emod_kernel", priority=medium

end FirstIsomorphismLemmas