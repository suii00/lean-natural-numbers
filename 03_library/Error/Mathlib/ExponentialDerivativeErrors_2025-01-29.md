# 指数関数微分エラー集 (2025-01-29)

## 概要
Lean 4 + Mathlib での指数関数微分実装時に遭遇したエラーパターンと解決策の体系的記録。

## 1. Import エラー

### エラー1: Real.deriv_exp が見つからない
```lean
error: unknown constant 'Real.deriv_exp'
```

**原因**: `ExpDeriv` モジュールのインポート漏れ

**解決策**:
```lean
import Mathlib.Analysis.SpecialFunctions.ExpDeriv  -- 追加必須
```

### エラー2: Real.differentiableAt_exp が見つからない
```lean
error: unknown constant 'Real.differentiableAt_exp'
```

**原因**: 同上（ExpDeriv モジュール不足）

## 2. API 使用エラー

### エラー3: Real.deriv_exp の誤用
```lean
error: Function expected at Real.deriv_exp
but this term has type: deriv Real.exp = Real.exp
```

**原因**: `Real.deriv_exp` は関数全体の等式であり、点での値ではない

**誤った使用**:
```lean
exact (Real.deriv_exp x)  -- ❌ xを適用できない
```

**正しい使用**:
```lean
rw [Real.deriv_exp]  -- ✅ 書き換えとして使用
```

## 3. 積の微分法則エラー

### エラー4: deriv_mul のパターンマッチング失敗
```lean
error: tactic 'rewrite' failed, did not find instance of the pattern
  deriv (id * Real.exp) ?m.4900
```

**原因**: `deriv_mul` が期待する関数の形と実際の関数の形が不一致

**試行した解決策（失敗）**:
```lean
-- 1. 直接適用 ❌
rw [deriv_mul differentiableAt_id Real.differentiableAt_exp]

-- 2. simp only での適用 ❌
simp only [deriv_mul differentiableAt_id Real.differentiableAt_exp]

-- 3. 関数の形を調整 ❌
have : (fun x => x * Real.exp x) = (fun x => id x * Real.exp x) := by ext y; simp [id]
rw [this]
```

**推奨解決策**: HasDerivAt レベルでの手動計算
```lean
theorem x_exp_product_deriv :
  ∀ x : ℝ, deriv (fun x => x * Real.exp x) x = (x + 1) * Real.exp x := by
  intro x
  have h1 : HasDerivAt (fun x => x) 1 x := hasDerivAt_id'
  have h2 : HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp x
  have h3 : HasDerivAt (fun x => x * Real.exp x) (1 * Real.exp x + x * Real.exp x) x := by
    exact HasDerivAt.mul h1 h2
  have : 1 * Real.exp x + x * Real.exp x = (x + 1) * Real.exp x := by ring
  rw [this] at h3
  exact HasDerivAt.deriv h3
```

## 4. 定数倍微分エラー

### エラー5: deriv_const_mul のパターンマッチング
```lean
error: tactic 'rewrite' failed, did not find instance of the pattern
  deriv (fun y => ?m.1225 * ?m.1212 y) ?m.1208
```

**原因**: 定数の型推論の問題

**解決策**:
```lean
-- 明示的な型指定が必要
rw [← deriv_const_mul (3 : ℝ) Real.differentiableAt_exp]
```

## 5. HasDerivAt 使用エラー

### エラー6: hasDerivAt_id' の引数エラー
```lean
error: type mismatch
  hasDerivAt_id'
has type
  ∀ (x : ?m.1994), HasDerivAt (fun x => x) 1 x : Prop
but is expected to have type
  HasDerivAt (fun x => x) 1 x : Prop
```

**原因**: `hasDerivAt_id'` は全称量化された命題

**解決策**:
```lean
have h1 : HasDerivAt (fun x => x) 1 x := hasDerivAt_id'  -- 暗黙的に x が適用される
```

### エラー7: convert での型不一致
```lean
error: unsolved goals after convert
```

**原因**: `convert` が完全に型を一致させられない

**解決策**: `exact` を使用するか、手動で等式を証明

## 6. 連鎖律エラー

### エラー8: hasDerivAt_const_mul が存在しない
```lean
error: unknown identifier 'hasDerivAt_const_mul'
```

**原因**: API 名の変更または存在しない

**代替案**:
```lean
-- 手動で定数倍を処理
have h1 : HasDerivAt (fun x => 2 * x) 2 x := by
  have : (fun x => 2 * x) = (fun x => 2 * id x) := by ext; simp [id]
  rw [this]
  exact HasDerivAt.const_mul 2 hasDerivAt_id'
```

## 7. パターン別解決戦略

### 基本微分
✅ **成功パターン**:
```lean
theorem exp_deriv : ∀ x : ℝ, deriv Real.exp x = Real.exp x := by
  intro x
  rw [Real.deriv_exp]
```

### 積の微分
⚠️ **要注意**: `deriv_mul` の直接使用は困難
**推奨**: `HasDerivAt.mul` を使用

### 合成関数の微分
⚠️ **要注意**: `deriv.comp` より `HasDerivAt.comp` が確実

### 定数倍の微分
✅ **成功パターン**: 型を明示的に指定

## 8. 教訓とベストプラクティス

1. **Import の完全性**: `ExpDeriv` モジュールは必須
2. **API の階層**: `deriv` レベルより `HasDerivAt` レベルが確実
3. **型の明示**: 定数には型注釈を付ける
4. **関数の形**: `id` vs `(fun x => x)` の違いに注意
5. **デバッグ手法**: 
   - まず `HasDerivAt` で動作確認
   - その後 `deriv` レベルに変換

## 9. 未解決の課題

1. `deriv_mul` の直接適用方法
2. `deriv.comp` の使用パターン
3. より複雑な合成関数での連鎖律

## 10. 参考リンク

- [Real.deriv_exp](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/ExpDeriv.html#Real.deriv_exp)
- [Real.differentiableAt_exp](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/ExpDeriv.html#Real.differentiableAt_exp)
- [deriv_mul](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/Deriv/Mul.html#deriv_mul)