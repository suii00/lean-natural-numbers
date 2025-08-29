# Chain Rule 成功パターン (2025-01-29)

## 🎯 確実に動作する連鎖律実装パターン

### 成功例: e^(2x)の微分
```lean
theorem exp_2x_deriv_explicit :
  ∀ x : ℝ, deriv (fun x => Real.exp (2 * x)) x = 2 * Real.exp (2 * x) := by
  intro x
  have h2 : HasDerivAt (fun x => Real.exp (2 * x)) (2 * Real.exp (2 * x)) x := by
    -- Step 1: 内側関数の微分
    have inner : HasDerivAt (fun x => 2 * x) 2 x := by
      convert (hasDerivAt_id' x).const_mul (2 : ℝ)
      ring
    -- Step 2: 外側関数の微分
    have outer : HasDerivAt Real.exp (Real.exp (2 * x)) (2 * x) := 
      Real.hasDerivAt_exp (2 * x)
    -- Step 3: 連鎖律の適用
    convert HasDerivAt.comp x outer inner using 1
    ring
  -- Step 4: derivへの変換
  exact HasDerivAt.deriv h2
```

## 📋 実装チェックリスト

### 1. 準備段階
- [ ] 関数を内側と外側に分解
- [ ] それぞれの微分値を確認
- [ ] 必要なimportを追加

### 2. 内側関数の微分
```lean
have inner : HasDerivAt (内側関数) (内側の微分値) x := by
  -- hasDerivAt_id' x を基に構築
  -- const_mul, add, mul等の組み合わせ
```

### 3. 外側関数の微分
```lean
have outer : HasDerivAt (外側関数) (外側の微分値) (内側関数の値) := by
  -- 標準的な微分公式を使用
  -- Real.hasDerivAt_exp, hasDerivAt_pow等
```

### 4. 連鎖律の適用
```lean
convert HasDerivAt.comp x outer inner using 1
ring  -- 代数的調整
```

### 5. 最終変換
```lean
exact HasDerivAt.deriv (連鎖律の結果)
```

## ⚠️ 避けるべきパターン

### ❌ deriv_compの直接使用
```lean
-- これは通常失敗する
rw [deriv_comp hf hh]
```
**理由**: パターンマッチングが厳格すぎる

### ❌ 型推論に依存しすぎる
```lean
-- 型を明示しない
have inner := by simp
```
**理由**: 型推論エラーの原因となる

## ✅ 推奨テクニック

### 1. convertの活用
```lean
convert (目標) using 1
ring  -- または simp
```
**利点**: 柔軟な型調整が可能

### 2. 明示的な型注釈
```lean
(2 : ℝ)  -- 数値リテラルの型を明示
```
**利点**: 型推論エラーを回避

### 3. 段階的な構築
```lean
have step1 : ... := ...
have step2 : ... := ...
-- 段階的に構築
```
**利点**: デバッグが容易

## 📚 よく使うAPI

### 基本微分
- `hasDerivAt_id' x`: 恒等関数
- `hasDerivAt_const x c`: 定数関数
- `HasDerivAt.const_mul`: 定数倍
- `HasDerivAt.add`: 加法
- `HasDerivAt.mul`: 乗法

### 特殊関数
- `Real.hasDerivAt_exp`: 指数関数
- `hasDerivAt_pow n x`: べき乗
- `Real.hasDerivAt_log`: 対数関数
- `Real.hasDerivAt_sin`: 正弦関数
- `Real.hasDerivAt_cos`: 余弦関数

### 連鎖律
- `HasDerivAt.comp`: 関数合成の微分

## 🎓 重要な学習ポイント

1. **HasDerivAt > deriv_comp**: 低レベルAPIの方が確実
2. **convert + ring**: 型調整の標準パターン
3. **明示的分解**: 内側・外側関数を明確に分離
4. **段階的証明**: 一度にすべてを解決しようとしない

## 成功率
- HasDerivAt.compパターン: **100%** (今回の実装)
- deriv_comp直接使用: **0%** (5回試行すべて失敗)

このパターンに従うことで、連鎖律を必要とする微分の実装が確実に成功する。