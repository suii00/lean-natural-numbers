/-
  🎯 Mathlib QuotientGroup 使用法まとめ
  Mode: explore
  Goal: QuotientGroupモジュールの正しい使用法の要点整理

  学習結果: Mathlib4における商群操作の実用ガイド
-/

import Mathlib.GroupTheory.QuotientGroup.Basic

namespace QuotientGroupSummary

open QuotientGroup

-- ===============================
-- 🔧 Section 1: 基本API確認
-- ===============================

variable {G H : Type*} [Group G] [Group H]

-- API 1: mk (射影写像)
example (N : Subgroup G) [N.Normal] : G →* G ⧸ N :=
  QuotientGroup.mk

-- API 2: eq (等価条件)  
example (N : Subgroup G) [N.Normal] (g₁ g₂ : G) : 
    (QuotientGroup.mk g₁ : G ⧸ N) = QuotientGroup.mk g₂ ↔ g₁⁻¹ * g₂ ∈ N :=
  QuotientGroup.eq

-- API 3: lift (普遍的性質)
example (f : G →* H) (N : Subgroup G) [N.Normal] (h : N ≤ f.ker) :
    G ⧸ N →* H :=
  QuotientGroup.lift f h

-- API 4: rangeKerLift (第一同型定理)
example (f : G →* H) : G ⧸ f.ker →* f.range :=
  QuotientGroup.rangeKerLift f

-- API 5: quotientKerEquivRange (完全同型)
example (f : G →* H) : G ⧸ f.ker ≃* f.range :=
  QuotientGroup.quotientKerEquivRange f

-- ===============================
-- 🎯 Section 2: 第一同型定理実装
-- ===============================

-- 単射性
example (f : G →* H) : Function.Injective (QuotientGroup.rangeKerLift f) :=
  QuotientGroup.rangeKerLift_injective f

-- 全射性  
example (f : G →* H) : Function.Surjective (QuotientGroup.rangeKerLift f) :=
  QuotientGroup.rangeKerLift_surjective f

-- 第一同型定理
theorem first_isomorphism_theorem (f : G →* H) :
    Nonempty (G ⧸ f.ker ≃* f.range) :=
  ⟨QuotientGroup.quotientKerEquivRange f⟩

-- ===============================
-- 🛠 Section 3: 実用パターン
-- ===============================

-- パターン1: 商群での等式証明
example (N : Subgroup G) [N.Normal] (g h : G) (H : g⁻¹ * h ∈ N) :
    (QuotientGroup.mk g : G ⧸ N) = QuotientGroup.mk h := by
  rw [QuotientGroup.eq]
  exact H

-- パターン2: 全射写像からの同型
example (f : G →* H) (hf : Function.Surjective f) :
    G ⧸ f.ker ≃* H := by
  -- f.range = ⊤ なので quotientKerEquivRange で十分
  rw [← MonoidHom.range_top_iff_surjective.mpr hf]
  exact QuotientGroup.quotientKerEquivRange f

-- パターン3: 核の正規性確認
example (f : G →* H) : (f.ker).Normal :=
  MonoidHom.normal_ker f

-- ===============================
-- ⚠️ Section 4: よくある注意点
-- ===============================

-- 注意1: Normal instance が必要
-- ❌ 間違い: instance なしで商群構成
-- example (N : Subgroup G) (g : G) : G ⧸ N := QuotientGroup.mk g  -- エラー

-- ✅ 正解: Normal instance を明示
example (N : Subgroup G) [N.Normal] (g : G) : G ⧸ N := 
  QuotientGroup.mk g

-- 注意2: lift の条件確認
-- ❌ 間違い: 条件なしで lift
-- example (f : G →* H) (N : Subgroup G) [N.Normal] : G ⧸ N →* H := 
--   QuotientGroup.lift f -- エラー: 条件 N ≤ f.ker が必要

-- ✅ 正解: 条件を満たす場合のみ
example (f : G →* H) (N : Subgroup G) [N.Normal] (h : N ≤ f.ker) : 
    G ⧸ N →* H := 
  QuotientGroup.lift f h

-- 注意3: 型注釈による曖昧性回避
example (N : Subgroup G) [N.Normal] (g : G) :
    (QuotientGroup.mk g : G ⧸ N) ∈ (⊤ : Set (G ⧸ N)) := by
  simp

end QuotientGroupSummary

-- ===============================
-- 📚 最終学習成果まとめ
-- ===============================

/-! 
## QuotientGroup モジュール使用法マスター完了

### 🔧 必須API:
- `QuotientGroup.mk` : G →* G⧸N (射影写像)
- `QuotientGroup.eq` : [g₁]=[g₂] ↔ g₁⁻¹g₂∈N  
- `QuotientGroup.lift` : 普遍的性質による写像構成
- `QuotientGroup.rangeKerLift` : G⧸ker(f) →* range(f)
- `QuotientGroup.quotientKerEquivRange` : G⧸ker(f) ≃* range(f)

### 🎯 使用パターン:
1. **商群構成**: [N.Normal] instance確認 → mk使用
2. **等式証明**: QuotientGroup.eq で代表元に帰着  
3. **写像構成**: N ≤ f.ker 確認 → lift適用
4. **同型証明**: quotientKerEquivRange 直接使用

### ⚠️ 注意事項:
- Normal instance は必須: [N.Normal]
- lift には条件が必要: N ≤ f.ker
- 型注釈で曖昧性を解消: (... : G ⧸ N)
- 既存定理を最大活用（車輪の再発明回避）

### 🎓 到達レベル:
**Mathlib4 QuotientGroup 実用レベル完全達成**

Goalクリア: QuotientGroupモジュールの正しい使用法を習得
-/