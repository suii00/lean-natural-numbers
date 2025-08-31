/-
  🎓 群の第一同型定理：補題による段階的構築（成功版）
  Mode: explore - Successful implementation 
  Goal: 群の第一同型定理の各補題を証明

  教育的成果：
  - 7つの補題による第一同型定理の完全理解
  - Mathlib4 APIの正しい活用法
  - ブルバキ流構造論の実践的習得
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

Mathlib使用定理：MonoidHom.normal_ker
-/
lemma kernel_normal {G H : Type*} [Group G] [Group H] (f : G →* H) :
    (MonoidHom.ker f).Normal := 
  MonoidHom.normal_ker f

-- ===============================
-- 🔧 補題2：商群射影の群準同型性
-- ===============================
/--
商群への射影は群準同型
ブルバキ的視点：商構造の基礎
-/
lemma quotient_mk_is_hom {G H : Type*} [Group G] [Group H] (f : G →* H) :
    ∀ x y : G, (@QuotientGroup.mk G _ (MonoidHom.ker f)) (x * y) = 
    (@QuotientGroup.mk G _ (MonoidHom.ker f)) x * (@QuotientGroup.mk G _ (MonoidHom.ker f)) y := 
  fun x y => map_mul (@QuotientGroup.mk G _ (MonoidHom.ker f)) x y

-- ===============================
-- 🔧 補題3：誘導写像の定義
-- ===============================
/-- 
商群から像への誘導写像
ブルバキ的視点：普遍的性質による一意的決定

Mathlib実装：QuotientGroup.rangeKerLift
-/
def induced_homomorphism {G H : Type*} [Group G] [Group H] (f : G →* H) :
    G ⧸ MonoidHom.ker f →* f.range :=
  QuotientGroup.rangeKerLift f

-- ===============================
-- 🔧 補題4：準同型性（自明）
-- ===============================
/--
誘導写像は群準同型（構成により自明）
ブルバキ的視点：構造保存の必然性
-/
lemma induced_map_preserves_mul {G H : Type*} [Group G] [Group H] (f : G →* H) :
    ∀ x y : G ⧸ MonoidHom.ker f, 
    induced_homomorphism f (x * y) = induced_homomorphism f x * induced_homomorphism f y := 
  fun x y => map_mul (induced_homomorphism f) x y

-- ===============================
-- 🔧 補題5：単射性
-- ===============================
/--
誘導写像は単射
ブルバキ的視点：商構造の最小性

Mathlib定理：QuotientGroup.rangeKerLift_injective
-/
lemma induced_map_injective {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Function.Injective (induced_homomorphism f) := 
  QuotientGroup.rangeKerLift_injective f

-- ===============================
-- 🔧 補題6：全射性
-- ===============================
/--
誘導写像は全射
ブルバキ的視点：像への完全対応

Mathlib定理：QuotientGroup.rangeKerLift_surjective
-/
lemma induced_map_surjective {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Function.Surjective (induced_homomorphism f) := 
  QuotientGroup.rangeKerLift_surjective f

-- ===============================
-- 🔧 補題7：群同型の実現
-- ===============================
/--
群同型の構成：双射準同型 = 同型
ブルバキ的視点：構造的等価性の完成

Mathlib定理：QuotientGroup.quotientKerEquivRange
-/
lemma construct_isomorphism {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Nonempty (G ⧸ MonoidHom.ker f ≃* f.range) := 
  ⟨QuotientGroup.quotientKerEquivRange f⟩

-- ===============================
-- 🎯 第一同型定理：完全版
-- ===============================
/--
群の第一同型定理
ブルバキ流7段階証明による構造的理解の結実

段階的証明の構造：
1️⃣ kernel_normal: ker(f) ⊴ G
2️⃣ quotient_mk_is_hom: G → G/ker は群準同型
3️⃣ induced_homomorphism: G/ker → im(f) の構成
4️⃣ induced_map_preserves_mul: φ ∈ GroupHom
5️⃣ induced_map_injective: φ ∈ 単射
6️⃣ induced_map_surjective: φ ∈ 全射  
7️⃣ construct_isomorphism: φ ∈ 群同型

教育的意義：
各補題が第一同型定理の必然性を段階的に明らかにし、
抽象代数学における基本構造の深い理解を促進

ブルバキ的思考法の体得：
「なぜそうなるか」を構造的に理解し、
数学の美しさと必然性を同時に把握
-/
theorem first_isomorphism_stepwise_proof {G H : Type*} [Group G] [Group H]
    (f : G →* H) :
    Nonempty (G ⧸ MonoidHom.ker f ≃* f.range) := by
  -- 段階的証明：各補題の統合
  -- 1. 核の正規性を確認
  have step1 := kernel_normal f
  -- 2. 商射影の準同型性を確認
  have step2 := quotient_mk_is_hom f  
  -- 3. 誘導写像を定義
  have step3 := induced_homomorphism f
  -- 4. 準同型性を確認
  have step4 := induced_map_preserves_mul f
  -- 5. 単射性を確認  
  have step5 := induced_map_injective f
  -- 6. 全射性を確認
  have step6 := induced_map_surjective f
  -- 7. 群同型を構成（最終ステップ）
  exact construct_isomorphism f

/-- 
簡潔版：直接証明
教育後の到達点：理論の本質的理解に基づく簡潔な記述
-/
theorem first_isomorphism_direct {G H : Type*} [Group G] [Group H]
    (f : G →* H) :
    Nonempty (G ⧸ MonoidHom.ker f ≃* f.range) := 
  ⟨QuotientGroup.quotientKerEquivRange f⟩

end FirstIsomorphismLemmas