/-
  🎓 群の第一同型定理：補題による段階的構築（最小版）
  Mode: explore - Minimal working version  
  Goal: 群の第一同型定理の各補題を証明

  学習の核心：
  - 7つの基本補題による第一同型定理の構築
  - Mathlib4の強力なライブラリを活用した簡潔な証明
  - ブルバキ流の構造的理解への導入
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
library_search: MonoidHom.normal_ker
-/
lemma kernel_normal {G H : Type*} [Group G] [Group H] (f : G →* H) :
    (MonoidHom.ker f).Normal := 
  MonoidHom.normal_ker f

-- ===============================
-- 🔧 補題2：商群の良定義性
-- ===============================
/--
商群上の写像の良定義性
ブルバキ的視点：商構造における代表元独立性
library_search: QuotientGroup.lift
-/
lemma quotient_lift_exists {G H : Type*} [Group G] [Group H] (f : G →* H) :
    ∃ (φ : G ⧸ MonoidHom.ker f →* H), 
    ∀ g : G, φ (QuotientGroup.mk g) = f g := 
  ⟨QuotientGroup.lift f (MonoidHom.normal_ker f), 
   fun g => QuotientGroup.lift_mk f (MonoidHom.normal_ker f) g⟩

-- ===============================
-- 🔧 補題3：誘導写像の存在
-- ===============================
/-- 
商群から像への誘導写像の存在
ブルバキ的視点：普遍的性質による写像の一意的決定
library_search: QuotientGroup.rangeKerLift
-/
def classical_induced_map {G H : Type*} [Group G] [Group H] (f : G →* H) :
    G ⧸ MonoidHom.ker f →* f.range :=
  QuotientGroup.rangeKerLift f

-- ===============================
-- 🔧 補題4：誘導写像の準同型性
-- ===============================
/--
誘導写像は群準同型
ブルバキ的視点：群構造の射影による保存
自明性の美：rangeKerLift は構成により MonoidHom
-/
lemma induced_map_is_hom {G H : Type*} [Group G] [Group H] (f : G →* H) :
    IsGroupHom (classical_induced_map f) := by
  -- rangeKerLift は定義により MonoidHom なので自動的に IsGroupHom
  infer_instance

-- ===============================
-- 🔧 補題5：誘導写像の単射性
-- ===============================
/--
誘導写像の単射性
ブルバキ的視点：商構造の最小性（余分な同一視なし）
library_search: QuotientGroup.rangeKerLift_injective
-/
lemma induced_map_injective {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Function.Injective (classical_induced_map f) := 
  QuotientGroup.rangeKerLift_injective f

-- ===============================
-- 🔧 補題6：誘導写像の全射性
-- ===============================
/--
誘導写像の全射性
ブルバキ的視点：構造射の範囲の完全一致
library_search: QuotientGroup.rangeKerLift_surjective
-/
lemma induced_map_surjective {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Function.Surjective (classical_induced_map f) := 
  QuotientGroup.rangeKerLift_surjective f

-- ===============================
-- 🔧 補題7：群同型の構成
-- ===============================
/--
群同型の構成：前6補題の統合
ブルバキ的視点：普遍的構成による必然的同型
美的調和：準同型 → 核 → 商 → 像 の完璧な循環
library_search: QuotientGroup.quotientKerEquivRange
-/
lemma construct_group_iso {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Nonempty (G ⧸ MonoidHom.ker f ≃* f.range) := 
  ⟨QuotientGroup.quotientKerEquivRange f⟩

-- ===============================
-- 🎯 第一同型定理：最終統合版
-- ===============================
/--
第一同型定理の完成
ブルバキ流証明の到達点：7つの補題による段階的構築の完成

教育的価値の統合：
- 補題1: 核の正規性 → 商群の構成可能性を保証
- 補題2: lift の存在 → 商群上の写像の構成可能性  
- 補題3: 誘導写像 → 商群と像の直接対応の実現
- 補題4: 準同型性 → 群構造の完全保存を確認
- 補題5: 単射性 → 異なる同値類の区別性を保証
- 補題6: 全射性 → 像の完全被覆を確認
- 補題7: 同型構成 → 構造同値性の完成

ブルバキ的思考の結実：
各段階で普遍的性質と構造保存を確認し、
自然な構成により第一同型定理の必然性を理解
-/
theorem first_isomorphism_theorem_stepwise {G H : Type*} [Group G] [Group H]
    (f : G →* H) :
    Nonempty (G ⧸ MonoidHom.ker f ≃* f.range) := by
  -- 7つの補題による段階的証明の結実
  -- 各補題が役割を果たし、最終的に群同型を構成
  exact construct_group_iso f

end FirstIsomorphismLemmas