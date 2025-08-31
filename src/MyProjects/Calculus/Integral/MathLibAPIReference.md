# MathLib Integral API Reference

## 確認済み API (2025-01-30)

### 基本積分公式 - `Mathlib.Analysis.SpecialFunctions.Integrals.Basic`

#### 1. `integral_pow` - べき関数の積分
```lean
theorem integral_pow {a b : ℝ} (n : ℕ) :
  ∫ (x : ℝ) in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1)
```
**使用例**:
```lean
example : ∫ x in (0:ℝ)..(1:ℝ), x^2 = 1/3 := 
calc ∫ x in (0:ℝ)..(1:ℝ), x^2 
  = ((1:ℝ)^(2+1) - (0:ℝ)^(2+1)) / (2 + 1) := integral_pow 2
  _ = 1/3 := by norm_num
```

#### 2. `integral_sin` - 正弦関数の積分  
```lean
theorem integral_sin {a b : ℝ} :
  ∫ (x : ℝ) in a..b, Real.sin x = Real.cos a - Real.cos b
```
**使用例**:
```lean
example : ∫ x in (0:ℝ)..π, sin x = 2 := 
calc ∫ x in (0:ℝ)..π, sin x 
  = cos (0:ℝ) - cos π := integral_sin
  _ = 1 - (-1) := by simp [cos_zero, cos_pi]
  _ = 2 := by norm_num
```

#### 3. `integral_cos` - 余弦関数の積分
```lean
theorem integral_cos {a b : ℝ} :
  ∫ (x : ℝ) in a..b, Real.cos x = Real.sin b - Real.sin a
```
**使用例**:
```lean
example : ∫ x in (0:ℝ)..(π/2), cos x = 1 := 
calc ∫ x in (0:ℝ)..(π/2), cos x 
  = sin (π/2) - sin (0:ℝ) := integral_cos
  _ = 1 - 0 := by simp [sin_pi_div_two, sin_zero]
  _ = 1 := by norm_num
```

#### 4. `integral_one` - 定数1の積分
```lean
theorem integral_one {a b : ℝ} :
  ∫ (x : ℝ) in a..b, 1 = b - a
```

#### 5. `integral_const` - 一般定数の積分
```lean
-- intervalIntegral内で定義
theorem integral_const (c : ℝ) :
  ∫ (x : ℝ) in a..b, c = (b - a) • c
```
**注意**: スカラー倍 `•` を返すため、`smul_eq_mul` で通常の乗算に変換が必要

---

## 次回調査対象 API

### 微分積分学基本定理関連（予想）

#### `MeasureTheory.deriv_integral_right`
- 積分の上限を変数とする関数の微分
- fundamental_theorem_part1 の実装に必要

#### `integral_eq_sub_of_hasDerivAt`  
- 原始関数を使った定積分の計算
- fundamental_theorem_part2 の実装に必要

#### `integral_by_parts` または `integral_parts`
- 部分積分の公式
- integration_by_parts の実装に必要

### 線形性関連

#### `integral_add`
- 積分の加法性

#### `integral_const_mul` または `integral_smul`
- 定数倍の積分

#### `integral_linear_combination`
- 線形結合の積分（存在する場合）

---

## 実装時の注意点

### 型推論サポート
- 明示的型注釈: `(0:ℝ)`, `(1:ℝ)`, `(c:ℝ)`
- `norm_num`, `norm_cast` の活用

### スカラー倍問題
```lean
-- ❌ エラー: (b - a) • c ≠ c * (b - a)
rw [intervalIntegral.integral_const]
ring

-- ✅ 解決法
rw [intervalIntegral.integral_const]
simp only [smul_eq_mul, mul_comm]
```

### IntervalIntegrable条件
高度な定理では以下の条件が必要:
```lean
(hf : IntervalIntegrable f volume a b)
(hg : IntervalIntegrable g volume a b)
```

---

## 参照リンク

- [Mathlib4 Docs - Integrals.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Integrals/Basic.html)
- [Mathlib4 Docs - IntervalIntegral](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.html)
- [Mathlib4 Docs - FundThmCalculus](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.html)

---

## 更新履歴
- 2025-01-30: 初版作成、基本積分公式API確認済み