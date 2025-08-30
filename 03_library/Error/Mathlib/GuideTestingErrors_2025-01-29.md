# ガイドテストエラー総合分析 (2025-01-29)

## 概要
claude2.txt と mathlib_deriv_corrected_guide.txt の実装テスト中に遭遇したエラーパターンの体系的記録。

## 1. パターンマッチングエラー群

### エラー1-1: deriv_mul のパターンマッチング失敗
```lean
error: tactic 'rewrite' failed, did not find instance of the pattern in the target expression
  deriv ((fun t => t) * Real.exp) x
```

**発生箇所**: ExponentialClaude2Test.lean, ExponentialMathLibCorrectedTest.lean
**原因**: Lean が `(fun t => t * Real.exp t)` を `f * g` の形として認識できない
**解決策**: 明示的な関数分解と ext による等価性証明

```lean
-- ✅ 動作する修正版
let f : ℝ → ℝ := fun t => t
let g : ℝ → ℝ := Real.exp
have h_eq : (fun t => t * Real.exp t) = f * g := by ext t; rfl
```

### エラー1-2: deriv_add のパターンマッチング失敗  
```lean
error: tactic 'rewrite' failed, did not find instance of the pattern in the target expression
  deriv (?m.23436 + ?m.23437) ?m.23438
```

**原因**: 加法関数の認識問題（乗法と同様）
**解決策**: 関数分解アプローチの適用

## 2. 型推論エラー群

### エラー2-1: hasDerivAt_id' の型不一致
```lean
error: type mismatch
  hasDerivAt_id'
has type
  ∀ (x : ?m.6073), HasDerivAt (fun x => x) 1 x : Prop
but is expected to have type
  HasDerivAt (fun t => t) 1 x : Prop
```

**発生箇所**: ExponentialClaude2Test.lean
**原因**: 変数名の不一致（`x` vs `t`）
**解決策**: 明示的な引数適用

```lean
-- ✅ 修正版
have h1 : HasDerivAt (fun t => t) 1 x := hasDerivAt_id' x
```

### エラー2-2: differentiableAt_pow の引数不足
```lean
error: type mismatch
  differentiableAt_pow
has type
  ∀ (n : ℕ) {x : ?m.4692}, DifferentiableAt ?m.4691 (fun x => x ^ n) x : Prop
but is expected to have type
  DifferentiableAt ℝ (fun t => t ^ 2) x : Prop
```

**原因**: `differentiableAt_pow` には冪数の引数が必要
**解決策**: 明示的な引数指定

```lean
-- ✅ 修正版
have h : DifferentiableAt ℝ (fun t => t^2) x := differentiableAt_pow
-- または
have h : DifferentiableAt ℝ (fun t => t^2) x := by simp [differentiableAt_pow]
```

### エラー2-3: hasDerivAt_pow の型調整
```lean
error: type mismatch
  hasDerivAt_pow 2 x
has type
  HasDerivAt (fun x => x ^ 2) (↑2 * x ^ (2 - 1)) x : Prop
but is expected to have type
  HasDerivAt (fun t => t ^ 2) (2 * x) x : Prop
```

**原因**: 自動生成された型 `(↑2 * x ^ (2 - 1))` が期待型 `(2 * x)` と一致しない
**解決策**: simp による型正規化

```lean
-- ✅ 修正版
example (x : ℝ) : HasDerivAt (fun t ↦ t^2) (2*x) x := by
  have h : HasDerivAt (fun t : ℝ ↦ t^2) (2 * x^(2-1)) x := hasDerivAt_pow 2 x
  simp at h
  exact h
```

## 3. simp タクティックエラー群

### エラー3-1: simp made no progress
```lean
error: simp made no progress
```

**発生箇所**: ExponentialClaude2Test.lean（複数箇所）
**原因**: simp 引数が現在のゴールに適用できない
**解決策**: より具体的な simp only や個別の rw 使用

```lean
-- ❌ 失敗例
simp [deriv_add, deriv_const_mul, deriv_pow]

-- ✅ 修正版
simp only [deriv_add, deriv_const_mul, deriv_pow]
-- または
rw [deriv_add]; simp [deriv_pow]
```

### エラー3-2: 未使用 simp 引数警告
```lean
warning: This simp argument is unused: deriv_add
```

**原因**: 指定した simp 引数が実際には使用されない
**対策**: 必要最小限の引数のみ指定

## 4. ゴール解決エラー群

### エラー4-1: no goals to be solved
```lean
error: no goals to be solved
```

**発生箇所**: ExponentialMathLibCorrectedTestFixed.lean（複数箇所）
**原因**: simp による過度な自動化でゴールが予期せず解決される
**解決策**: より制御された証明ステップ

### エラー4-2: unsolved goals
```lean
error: unsolved goals
x : ℝ
f : ℝ → ℝ := fun t => t ^ 2 + 1
⊢ f x = x ^ 2 + 1
```

**原因**: 関数定義の展開不足
**解決策**: 明示的な simp [f] または rfl

## 5. 合成関数エラー群

### エラー5-1: deriv.comp の使用法エラー
```lean
error: tactic 'rewrite' failed, equality or iff proof expected
```

**原因**: deriv.comp の引数順序や型の問題
**解決策**: 正確な引数順序の確認

```lean
-- ✅ 正しい使用法
rw [deriv.comp h_outer h_inner]
-- h_outer: 外側関数の微分可能性
-- h_inner: 内側関数の微分可能性
```

## 6. 関数等価性エラー群

### エラー6-1: show tactic の型不一致
```lean
error: 'show' tactic failed, pattern is not definitionally equal to target
```

**原因**: show で指定したパターンとゴールの型が一致しない
**解決策**: より正確な型指定または show の削除

## 7. エラーパターン分類

### レベル1: 致命的エラー（コンパイル不可）
- パターンマッチング失敗
- 型不一致
- 引数不足

### レベル2: 警告（コンパイル可能だが非効率）
- 未使用 simp 引数
- 冗長な証明

### レベル3: ゴール管理エラー
- no goals to be solved
- unsolved goals

## 8. エラー回避戦略

### 戦略A: 最小化アプローチ
```lean
-- ExponentialExploreFinal.lean パターン
rw [Real.deriv_exp]  -- 直接API使用
```

### 戦略B: 段階的構築アプローチ
```lean
-- 関数分解 + 明示的証明
let f := fun t => t
let g := Real.exp
have h_eq : (fun t => t * Real.exp t) = f * g := by ext t; rfl
```

### 戦略C: 型の明示化アプローチ
```lean
-- 曖昧さ回避
have h : DifferentiableAt ℝ (fun t => t^2) x := by simp [differentiableAt_pow]
```

## 9. 実用的な教訓

### 成功要因
1. **API の直接使用**: 複雑な変換を避ける
2. **明示的な型指定**: 推論に頼らない
3. **段階的な証明**: 一度に多くを解決しようとしない

### 失敗要因
1. **過度な一般化**: ガイドパターンの直接適用
2. **型推論への依存**: 予測困難な動作
3. **複雑な simp 使用**: デバッグ困難

## 10. 推奨開発フロー

```
1. 最小成功例から開始 (ExponentialExploreFinal.lean)
2. 必要に応じて段階的拡張
3. 各ステップでコンパイル確認
4. エラー発生時は簡単な形に戻る
5. 複雑なガイドパターンは避ける
```

## 結論

**ガイド由来のエラーの多くは、Lean の型システムとパターンマッチングの複雑さに起因する。実用的な開発では、理論的な美しさより確実性を重視し、最小限・段階的なアプローチを採用すべき。**

このエラー分析により、指数関数微分実装の実践的な方針が明確になった。