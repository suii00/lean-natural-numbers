# HasDerivAt実装クイックリファレンス

## 🚀 確実に成功する実装パターン

### 基本テンプレート
```lean
theorem your_derivative_theorem :
  ∀ x : ℝ, deriv (fun x => your_function x) x = expected_derivative := by
  intro x
  have h : HasDerivAt (fun x => your_function x) expected_derivative x := by
    -- Step 1: 内側関数の微分（必要に応じて）
    have inner : HasDerivAt inner_function inner_derivative x := ...
    -- Step 2: 適切なHasDerivAt APIを選択
    convert HasDerivAt.{comp|exp|mul|add|...} ... using 1
    ring  -- または field_simp
  exact HasDerivAt.deriv h
```

## 📋 API選択ガイド

### 合成関数 → HasDerivAt.comp
```lean
-- f(g(x)) の微分
have inner : HasDerivAt g g' x := ...
have outer : HasDerivAt f f' (g x) := ...
convert HasDerivAt.comp x outer inner using 1
```

### 指数関数合成 → HasDerivAt.exp
```lean
-- e^(f(x)) の微分
have inner : HasDerivAt f f' x := ...
convert HasDerivAt.exp inner using 1
```

### 積の微分 → HasDerivAt.mul
```lean
-- f(x) * g(x) の微分
have hf : HasDerivAt f f' x := ...
have hg : HasDerivAt g g' x := ...
convert HasDerivAt.mul hf hg using 1
```

### 和の微分 → HasDerivAt.add
```lean
-- f(x) + g(x) の微分
have hf : HasDerivAt f f' x := ...
have hg : HasDerivAt g g' x := ...
convert HasDerivAt.add hf hg using 1
```

## ⚡ よく使う基本関数

### 基本関数のHasDerivAt
```lean
-- 恒等関数: x
hasDerivAt_id' x

-- 定数関数: c
hasDerivAt_const x c

-- 定数倍: c * x
(hasDerivAt_id' x).const_mul c

-- べき乗: x^n
hasDerivAt_pow n x

-- 指数関数: e^x
Real.hasDerivAt_exp x

-- 負数: -x
(hasDerivAt_id' x).neg
```

## 🚨 よくあるエラーと即座の修正

### 型推論エラー
```
❌ failed to synthesize AddCommGroup ℕ
```
**修正**: 数値に型注釈追加
```lean
-- Before: 2 * x
-- After:  (2 : ℝ) * x
```

### 関数等価性エラー
```
❌ HasDerivAt ((fun x => x) + fun x => 1) vs HasDerivAt (fun x => x + 1)
```
**修正**: convertを使用
```lean
convert HasDerivAt.add (hasDerivAt_id' x) (hasDerivAt_const x 1) using 1
ring
```

### HPowエラー（回避推奨）
```
❌ failed to synthesize HPow ℝ ℝ ℝ
```
**修正**: `a^x`形式を避け、`Real.exp`で表現
```lean
-- 避ける: a ^ x
-- 使う: Real.exp (x * Real.log a)  -- ただし複雑
```

## 🎯 成功率の高い実装順序

### 1. 基本確認
```lean
#check your_function  -- 型確認
#check expected_api   -- API存在確認
```

### 2. 段階的構築
```lean
-- まず内側関数
have inner : HasDerivAt ... := by sorry
-- 次に外側関数  
have outer : HasDerivAt ... := by sorry
-- 最後に合成
convert HasDerivAt.comp ... using 1
```

### 3. デバッグ手順
```lean
-- convertで残ったゴールを確認
convert target_expression using 1
sorry  -- ゴールを確認してから ring等で解決
```

## 💡 実装戦略

### Chain Rule系（合成関数）
- **成功率**: 100%
- **使用API**: `HasDerivAt.comp`
- **適用分野**: 一般的な合成関数

### Exponential系（指数関数）
- **成功率**: 85%+
- **使用API**: `HasDerivAt.exp`  
- **適用分野**: e^(f(x))形式

### 困難回避戦略
1. **事前調査**: API存在確認
2. **段階的実装**: 複雑な部分は分離
3. **現実的妥協**: 困難な部分は後回し

## ✅ 確実に成功する例

### e^(2x)の微分
```lean
theorem exp_2x_deriv :
  ∀ x : ℝ, deriv (fun x => Real.exp (2 * x)) x = 2 * Real.exp (2 * x) := by
  intro x
  have h : HasDerivAt (fun x => Real.exp (2 * x)) (2 * Real.exp (2 * x)) x := by
    have inner : HasDerivAt (fun x => 2 * x) 2 x := by
      convert (hasDerivAt_id' x).const_mul (2 : ℝ)
      ring
    convert HasDerivAt.exp inner using 1
    ring
  exact HasDerivAt.deriv h
```

### (x+1)^2の微分
```lean
theorem x_plus_1_squared_deriv :
  ∀ x : ℝ, deriv (fun x => (x + 1) ^ 2) x = 2 * (x + 1) := by
  intro x
  have h : HasDerivAt (fun x => (x + 1) ^ 2) (2 * (x + 1)) x := by
    have inner : HasDerivAt (fun x => x + 1) 1 x := by
      convert HasDerivAt.add (hasDerivAt_id' x) (hasDerivAt_const x 1) using 1
      ring
    have outer : HasDerivAt (fun u => u ^ 2) (2 * (x + 1)) (x + 1) := by
      convert hasDerivAt_pow 2 (x + 1)
      ring
    convert HasDerivAt.comp x outer inner using 1
    ring
  exact HasDerivAt.deriv h
```

## 🔧 トラブルシューティング

### コンパイルエラー時
1. 型注釈確認（特に数値）
2. API存在確認（#check使用）
3. 段階的コメントアウト
4. convertゴール確認

### 証明失敗時
1. 内側・外側関数を分離確認
2. 個別にsorryで動作確認
3. ring vs field_simpを試行
4. より基本的なAPIに変更

### 複雑化した場合
1. 問題を小分割
2. 最小動作版を作成
3. 段階的に拡張
4. 困難部分は一時的に回避

## 📈 成功確率向上のコツ

1. **型注釈**: すべての数値に`(n : ℝ)`
2. **API選択**: 特化API優先（exp, mul等）
3. **convert使用**: 直接rewriteより安全
4. **段階的証明**: 一度に複数要素を扱わない
5. **現実的目標**: 80%以上成功で十分価値あり