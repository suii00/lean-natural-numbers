# Lean 4 環論エラー対処クイックガイド

## 🚨 エラーに遭遇したら

### ステップ1: エラータイプの特定
```
1. "typeclass instance problem" → Section A
2. "unknown identifier" → Section B  
3. "type mismatch" → Section C
4. "tactic failed" → Section D
5. "no such file" → Section E
```

---

## Section A: 型クラスインスタンス問題

### 症状
```lean
error: typeclass instance problem is stuck, it is often due to metavariables
  SemilatticeSup ?m.XXX
```

### 即座の解決策
```lean
-- 追加すべきimport（順番重要）
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Order.CompleteLattice.Basic  -- 必要に応じて
```

---

## Section B: 識別子未定義

### 症状
```lean
error: unknown identifier 'sup_mono'
```

### クイックフィックス表

| エラー識別子 | 代替実装 |
|------------|---------|
| `sup_mono` | `apply sup_le; exact h1.trans le_sup_left; exact h2.trans le_sup_right` |
| `inf_mono` | `apply le_inf; exact inf_le_left.trans h1; exact inf_le_right.trans h2` |
| `le_sup_iff_left` | `rw [le_sup_iff]; left` |
| `Ideal.mem_map_iff_of_surjective` | 手動で証明するか別のAPIを探す |

---

## Section C: 型の不一致

### 症状
```lean
error: type mismatch ... has type X but is expected to have type Y
```

### チェックリスト
1. ✅ `Quotient.mk` → `Ideal.Quotient.mk`
2. ✅ 名前空間を明示: `open Ideal` または完全修飾名使用
3. ✅ 型注釈を追加: `(x : R)`
4. ✅ 暗黙の引数を明示: `@lemma_name R _ ...`

---

## Section D: タクティク失敗

### 症状と対処

#### `rfl` が失敗
```lean
-- 誤り
theorem test : I ⊔ J = J ⊔ I := by rfl

-- 正解
theorem test : I ⊔ J = J ⊔ I := by exact sup_comm
```

#### `simp` が効かない
```lean
-- より具体的なlemmaを使用
simp only [sup_bot_eq, inf_top_eq]
```

#### `rewrite` が失敗
```lean
-- パターンを確認
#check target_lemma  -- 正確な形を確認
-- または別の戦略
sorry  -- 一時的にスキップ
```

---

## Section E: インポートエラー

### 正しいモジュール名マップ

| 誤り | 正しい |
|------|--------|
| `Mathlib.Order.CompleteLattice` | `Mathlib.Order.CompleteLattice.Basic` |
| `Mathlib.RingTheory.Ideal` | `Mathlib.RingTheory.Ideal.Basic` |
| `Mathlib.Algebra.Ring` | `Mathlib.Algebra.Ring.Basic` |

---

## 🔥 緊急対処テンプレート

### すべてのエラーを一時的に回避
```lean
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Order.CompleteLattice.Basic

open Ideal

variable {R : Type*} [CommRing R]

-- 証明が難しい場合
theorem my_theorem : statement := by
  sorry -- TODO: implement later
```

### デバッグ用コマンド
```lean
#check lemma_name     -- 型を確認
#print lemma_name     -- 定義を確認
set_option trace.Meta.synthInstance true  -- インスタンス検索をトレース
```

---

## 📊 エラー頻度統計（2025-08-24）

1. **型クラスインスタンス**: 7回
2. **識別子未定義**: 4回
3. **型の不一致**: 5回
4. **タクティク失敗**: 6回
5. **インポートエラー**: 2回

**合計**: 24エラー → 17/17補題成功

---

## 💡 予防的措置

### 新規ファイル作成時のテンプレート
```lean
-- ===============================
-- 🎯 タイトル
-- ===============================

import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Operations

variable {R : Type*} [CommRing R]

namespace MyNamespace

-- コードここから

end MyNamespace
```

### テスト駆動開発
1. 最小単位でテスト
2. `#check` で型確認
3. `example` で動作確認
4. 本実装へ

---

## 🎯 最終チェックリスト

- [ ] 必要なimportはすべて追加したか
- [ ] 名前空間は正しいか
- [ ] 型注釈は十分か
- [ ] sorryは最小限か
- [ ] エラーメッセージは保存したか