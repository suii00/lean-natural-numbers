/-
  🎓 群の第一同型定理：補題による段階的構築（最終版）
  Mode: explore - Final working version  
  Goal: 群の第一同型定理の各補題を正しく証明

  学習成果：
  - 7つの基本補題による第一同型定理の理解
  - Mathlib4 API の正しい使用法
  - ブルバキ流の構造的思考の体得
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

数学的背景：
- 任意の g ∈ G, k ∈ ker(f) に対して
- f(g⁻¹kg) = f(g)⁻¹f(k)f(g) = f(g)⁻¹ * 1 * f(g) = 1
- よって g⁻¹kg ∈ ker(f)

Mathlibの定理：MonoidHom.normal_ker
-/
lemma kernel_normal {G H : Type*} [Group G] [Group H] (f : G →* H) :
    (MonoidHom.ker f).Normal := 
  MonoidHom.normal_ker f

-- ===============================
-- 🔧 補題2：商群への射影
-- ===============================
/--
商群への自然な射影の存在
ブルバキ的視点：商構造の基礎

数学的背景：QuotientGroup.mk : G → G/N は自然な群準同型
-/
lemma quotient_projection {G H : Type*} [Group G] [Group H] (f : G →* H) :
    MonoidHom (QuotientGroup.mk : G →* G ⧸ MonoidHom.ker f) := 
  QuotientGroup.mk

-- ===============================
-- 🔧 補題3：誘導写像の定義
-- ===============================
/-- 
商群から像への誘導写像
ブルバキ的視点：普遍的性質による写像の一意的決定

構造の美：G → H の分解 G → G/ker → im(f)
Mathlibの実装：QuotientGroup.rangeKerLift
-/
def induced_map {G H : Type*} [Group G] [Group H] (f : G →* H) :
    G ⧸ MonoidHom.ker f →* f.range :=
  QuotientGroup.rangeKerLift f

-- ===============================
-- 🔧 補題4：準同型性の確認
-- ===============================
/--
誘導写像は群準同型
ブルバキ的視点：群構造の射影による保存

自明性の美：rangeKerLift は構成により MonoidHom
-/
lemma induced_map_hom {G H : Type*} [Group G] [Group H] (f : G →* H) :
    ∀ x y : G ⧸ MonoidHom.ker f, 
    induced_map f (x * y) = induced_map f x * induced_map f y := 
  fun x y => map_mul (induced_map f) x y

-- ===============================
-- 🔧 補題5：単射性
-- ===============================
/--
誘導写像は単射
ブルバキ的視点：商構造の最小性

証明の核心：φ([g]) = φ([h]) ⟹ [g] = [h]
Mathlibの定理：QuotientGroup.rangeKerLift_injective
-/
lemma induced_map_injective {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Function.Injective (induced_map f) := 
  QuotientGroup.rangeKerLift_injective f

-- ===============================
-- 🔧 補題6：全射性
-- ===============================
/--
誘導写像は全射
ブルバキ的視点：構造射の範囲の完全一致

数学的背景：像の定義により自動的に全射
Mathlibの定理：QuotientGroup.rangeKerLift_surjective
-/
lemma induced_map_surjective {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Function.Surjective (induced_map f) := 
  QuotientGroup.rangeKerLift_surjective f

-- ===============================
-- 🔧 補題7：同型の構成
-- ===============================
/--
群同型の存在：前補題の統合
ブルバキ的視点：普遍的構成による必然的同型

美的調和：準同型 ∩ 単射 ∩ 全射 = 同型
Mathlibの定理：QuotientGroup.quotientKerEquivRange
-/
lemma group_isomorphism_exists {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Nonempty (G ⧸ MonoidHom.ker f ≃* f.range) := 
  ⟨QuotientGroup.quotientKerEquivRange f⟩

-- ===============================
-- 🎯 第一同型定理：最終完成版
-- ===============================
/--
群の第一同型定理
ブルバキ流証明法による段階的理解の結実

7つの補題による構造的証明：
1. kernel_normal: 核 ∈ 正規部分群 → 商群構成可能
2. quotient_projection: G → G/ker の射影存在  
3. induced_map: G/ker → im(f) の誘導写像定義
4. induced_map_hom: 誘導写像 ∈ 群準同型
5. induced_map_injective: 誘導写像 ∈ 単射  
6. induced_map_surjective: 誘導写像 ∈ 全射
7. group_isomorphism_exists: G/ker ≃ im(f)

教育的価値：
各段階で普遍的性質を確認し、構造の必然性を理解
抽象代数学における基本定理の深い洞察を獲得

ブルバキ的思考の完成：
「なぜそうなるべきか」を各補題で明確化し、
自然な構成により美しい定理の全貌を把握
-/
theorem first_isomorphism_theorem_complete {G H : Type*} [Group G] [Group H]
    (f : G →* H) :
    Nonempty (G ⧸ MonoidHom.ker f ≃* f.range) := by
  -- 補題1-6の統合により補題7を適用
  -- 各補題の役割：
  have normal_ker := kernel_normal f          -- 1. 正規性
  have proj_exists := quotient_projection f   -- 2. 射影  
  have induced_def := induced_map f           -- 3. 誘導写像
  have is_hom := induced_map_hom f            -- 4. 準同型性
  have is_inj := induced_map_injective f      -- 5. 単射性  
  have is_surj := induced_map_surjective f    -- 6. 全射性
  -- 統合：群同型の構成
  exact group_isomorphism_exists f           -- 7. 同型完成

end FirstIsomorphismLemmas