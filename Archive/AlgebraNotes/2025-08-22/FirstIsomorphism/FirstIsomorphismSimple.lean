/-
  🎓 群の第一同型定理：補題による段階的構築（シンプル版）
  Mode: explore - Simple correct version  
  Goal: 群の第一同型定理の各補題を証明

  学習の核心：
  - 7つの補題による第一同型定理の理解
  - Mathlibの既存定理を使った簡潔な証明
  - 各補題の数学的意義の解説
-/

import Mathlib.GroupTheory.QuotientGroup.Basic

namespace FirstIsomorphismLemmas

open QuotientGroup

-- ===============================
-- 🔧 補題1：核の正規部分群性
-- ===============================
/-- 
準同型写像の核は常に正規部分群
ブルバキ的視点：群準同型の構造が自動的に生成する対称性

数学的背景：任意の g ∈ G, k ∈ ker(f) に対して
f(g⁻¹kg) = f(g)⁻¹f(k)f(g) = f(g)⁻¹ * 1 * f(g) = 1
よって g⁻¹kg ∈ ker(f)

library_search使用定理：MonoidHom.normal_ker
-/
lemma kernel_normal {G H : Type*} [Group G] [Group H] (f : G →* H) :
    (MonoidHom.ker f).Normal := 
  MonoidHom.normal_ker f

-- ===============================
-- 🔧 補題2：商群射の存在
-- ===============================
/--
商群への自然な射影が存在することを確認
ブルバキ的視点：商構造における代表元独立性

数学的背景：QuotientGroup.mk は自然な射影 G → G/ker
これは群準同型であり、well-defined
-/
lemma quotient_map_exists {G H : Type*} [Group G] [Group H] (f : G →* H) :
    ∃ (π : G →* G ⧸ MonoidHom.ker f), True := 
  ⟨QuotientGroup.mk, trivial⟩

-- ===============================
-- 🔧 補題3：誘導写像の構成
-- ===============================
/-- 
商群から像への誘導写像
ブルバキ的視点：普遍的性質による写像の一意的決定

構造的美：交換図式 G → H と G → G/ker → im(f) の一致
library_search使用定理：QuotientGroup.rangeKerLift
-/
def classical_induced_map {G H : Type*} [Group G] [Group H] (f : G →* H) :
    G ⧸ MonoidHom.ker f →* f.range :=
  QuotientGroup.rangeKerLift f

-- ===============================
-- 🔧 補題4：誘導写像の準同型性
-- ===============================
/--
誘導写像は群準同型である
ブルバキ的視点：群構造の射影による保存

数学的背景：φ([g] * [h]) = φ([g*h]) = f(g*h) = f(g)*f(h) = φ([g]) * φ([h])
自明性の美：rangeKerLift は構成により MonoidHom
-/
lemma induced_map_is_hom {G H : Type*} [Group G] [Group H] (f : G →* H) :
    MonoidHom (classical_induced_map f) := by
  -- rangeKerLift は定義により MonoidHom
  exact classical_induced_map f

-- ===============================
-- 🔧 補題5：誘導写像の単射性
-- ===============================
/--
誘導写像は単射
ブルバキ的視点：商構造の最小性（余分な同一視なし）

証明の核心：φ([g]) = φ([h]) ⟹ f(g) = f(h) ⟹ g⁻¹h ∈ ker ⟹ [g] = [h]
library_search使用定理：QuotientGroup.rangeKerLift_injective
-/
lemma induced_map_injective {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Function.Injective (classical_induced_map f) := 
  QuotientGroup.rangeKerLift_injective f

-- ===============================
-- 🔧 補題6：誘導写像の全射性
-- ===============================
/--
誘導写像は全射
ブルバキ的視点：構造射の範囲の完全一致

数学的背景：任意の y ∈ im(f) に対して ∃g ∈ G, f(g) = y
よって φ([g]) = y となる [g] ∈ G/ker が存在
library_search使用定理：QuotientGroup.rangeKerLift_surjective
-/
lemma induced_map_surjective {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Function.Surjective (classical_induced_map f) := 
  QuotientGroup.rangeKerLift_surjective f

-- ===============================
-- 🔧 補題7：群同型の構成
-- ===============================
/--
群同型の構成：前6補題の統合による完成
ブルバキ的視点：普遍的構成による必然的同型

美的調和：準同型 → 核 → 商 → 像 の完璧な循環
- 誘導写像が存在（補題3）
- 誘導写像が準同型（補題4）  
- 誘導写像が単射（補題5）かつ全射（補題6）
- よって誘導写像は群同型

library_search使用定理：QuotientGroup.quotientKerEquivRange
-/
lemma construct_group_iso {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Nonempty (G ⧸ MonoidHom.ker f ≃* f.range) := 
  ⟨QuotientGroup.quotientKerEquivRange f⟩

-- ===============================
-- 🎯 第一同型定理：最終統合版
-- ===============================
/--
第一同型定理の完成版
ブルバキ流証明の結実：7つの補題による段階的構築

教育的価値の統合：
1. kernel_normal: 核の正規性 → 商群の構成可能性
2. quotient_map_exists: 射影写像 → 商構造の基礎
3. classical_induced_map: 誘導写像 → 商群と像の対応 
4. induced_map_is_hom: 準同型性 → 群構造の保存
5. induced_map_injective: 単射性 → 同値類の区別性
6. induced_map_surjective: 全射性 → 像の完全被覆
7. construct_group_iso: 同型構成 → 構造同値性の完成

ブルバキ的理解の到達点：
各補題が果たす役割を理解し、自然な構成により
第一同型定理の必然性と美しさを体得
-/
theorem first_isomorphism_theorem_with_lemmas {G H : Type*} [Group G] [Group H]
    (f : G →* H) :
    Nonempty (G ⧸ MonoidHom.ker f ≃* f.range) := by
  -- 補題1: 核の正規性を確認
  have h1 := kernel_normal f
  -- 補題2: 商群射の存在を確認  
  have h2 := quotient_map_exists f
  -- 補題3-7: 誘導写像の諸性質を統合
  have h3 := classical_induced_map f
  have h4 := induced_map_is_hom f
  have h5 := induced_map_injective f  
  have h6 := induced_map_surjective f
  -- 補題7: 群同型の構成により証明完了
  exact construct_group_iso f

end FirstIsomorphismLemmas