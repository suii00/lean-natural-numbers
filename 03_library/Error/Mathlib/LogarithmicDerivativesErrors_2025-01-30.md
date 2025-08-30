# Logarithmic Derivatives Implementation Errors (2025-01-30)

## 概要
対数関数の微分と逆関数の微分を実装する際に遭遇したエラーとその解決方法をまとめます。

## 1. API不一致エラー

### エラー1: `deriv_log` の引数エラー
```lean
-- エラーコード
rw [Real.deriv_log hx.ne']

-- エラーメッセージ
Application type mismatch: In the application
  deriv_log (LT.lt.ne' hx)
the argument has type
  x ≠ 0 : Prop
but is expected to have type
  ℝ : Type
```

**原因**: `Real.deriv_log` は引数として実数 `x` を受け取るが、証明 `hx.ne'` を渡していた

**解決方法**:
```lean
rw [Real.deriv_log x]  -- 正しい: xを渡す
```

### エラー2: `HasDerivAt.log` の型不一致
```lean
-- エラーコード
Real.hasDerivAt_log h2.ne'

-- エラーメッセージ
type mismatch
  hasDerivAt_log (LT.lt.ne' h2)
has type
  HasDerivAt log (a * x)⁻¹ (a * x) : Prop
but is expected to have type
  HasDerivAt log (1 / (a * x)) (a * x) : Prop
```

**原因**: Mathlibは `x⁻¹` を使用するが、コードでは `1 / x` を期待していた

**解決方法**: `inv_eq_one_div` を使用して変換、または `field_simp` で処理

## 2. 未知の識別子エラー

### エラー3: `deriv_eq_fderiv` が存在しない
```lean
-- エラーコード
rw [deriv_eq_fderiv h3]

-- エラーメッセージ
unknown identifier 'deriv_eq_fderiv'
```

**原因**: この関数は存在しない

**解決方法**:
```lean
rw [HasDerivAt.deriv h3]  -- 正しいAPI
```

### エラー4: `deriv_id'` の使用法エラー
```lean
-- エラーコード
exact deriv_id' x

-- エラーメッセージ
Function expected at deriv_id'
but this term has type
  deriv id = fun x => 1
```

**原因**: `deriv_id'` は定理であり、関数ではない

**解決方法**:
```lean
exact deriv_id'' x  -- deriv_id'' を使用
-- または
rw [deriv_id]      -- 書き換えとして使用
```

## 3. Import エラー

### エラー5: 存在しないモジュール
```lean
-- エラーコード
import Mathlib.Analysis.Calculus.Deriv.Div

-- エラーメッセージ
bad import 'Mathlib.Analysis.Calculus.Deriv.Div'
```

**原因**: このモジュールは存在しない

**解決方法**: 
- `deriv_div_const` は `Mathlib.Analysis.Calculus.Deriv.Mul` に含まれている
- 不要なimportを削除

## 4. 型変換エラー

### エラー6: `exp_log` の型エラー
```lean
-- エラーコード
have heq : ∀ z, 0 < z → Real.exp (Real.log z) = z := exp_log

-- エラーメッセージ
type mismatch
  exp_log
has type
  0 < ?m.2891 → rexp (log ?m.2891) = ?m.2891 : Prop
but is expected to have type
  ∀ (z : ℝ), 0 < z → rexp (log z) = z : Prop
```

**原因**: `exp_log` は単一の値に対する定理

**解決方法**: 直接使用するか、ラムダ式で包む

## 5. 連鎖律の適用エラー

### エラー7: `HasDerivAt.comp` の型不一致
```lean
-- エラーコード
HasDerivAt.comp x h2 h1

-- エラーメッセージ
type mismatch
  HasDerivAt.comp x ?m.9605 h1
has type
  HasDerivAt (?m.9350 ∘ fun x => x ^ 2 + 1) (?m.9352 * (2 * x)) x : Prop
but is expected to have type
  HasDerivAt (fun x => log (x ^ 2 + 1)) ((x ^ 2 + 1)⁻¹ * (2 * x)) x : Prop
```

**原因**: 合成関数の形が期待される形と一致しない

**解決方法**:
```lean
convert HasDerivAt.comp x h2 h1 using 1
```

## 6. Tactic エラー

### エラー8: `simp` が進捗しない
```lean
-- エラーコード
simp only [inv_eq_one_div]

-- エラーメッセージ
simp made no progress
```

**原因**: 
- 無限ループの可能性
- 適用可能な簡約規則がない

**解決方法**:
- `rw [inv_eq_one_div]` を使用
- `field_simp` で代数的処理

### エラー9: `linarith` の失敗
```lean
-- エラーコード
by linarith

-- エラーメッセージ
linarith failed to find a contradiction
case h
x : ℝ
hx : 0 < x
y : ℝ
a✝ : y ≤ 0
⊢ False
```

**原因**: コンテキストが不十分

**解決方法**:
```lean
by linarith [hx]  -- 必要な仮定を明示的に渡す
```

## 7. フィルター関連エラー

### エラー10: `𝓝` が未定義
```lean
-- エラーコード
∀ᶠ z in 𝓝 x

-- エラーメッセージ
unknown identifier '𝓝'
```

**原因**: 必要なnamespaceが開かれていない

**解決方法**:
```lean
open Filter Topology  -- 必要なnamespaceを開く
```

## 主な学習ポイント

1. **Mathlib APIの正確な理解が重要**
   - 関数シグネチャを確認
   - `x⁻¹` vs `1/x` の違いに注意

2. **型変換は明示的に**
   - `convert` を使用して型を調整
   - `field_simp` で代数的簡約

3. **Import の最小化**
   - 必要なモジュールのみimport
   - 存在しないモジュールに注意

4. **デバッグ戦略**
   - エラーメッセージを詳細に読む
   - 小さな部分から構築
   - `#check` でAPI確認

## 最終的な成功パターン

```lean
-- 対数微分の基本パターン
theorem log_deriv (x : ℝ) (_ : 0 < x) :
  deriv Real.log x = 1 / x := by
  rw [Real.deriv_log x]
  rw [inv_eq_one_div]

-- 連鎖律の適用パターン
have h1 : HasDerivAt f f' x := ...
have h2 : HasDerivAt g g' (f x) := ...
have h3 : HasDerivAt (g ∘ f) (g' * f') x :=
  HasDerivAt.comp x h2 h1
rw [HasDerivAt.deriv h3]
field_simp
```

このエラー集は、今後の対数関数や逆関数の実装において参考となる重要な知見です。