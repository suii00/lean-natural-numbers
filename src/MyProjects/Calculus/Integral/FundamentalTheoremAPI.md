# Fundamental Theorem of Calculus & Integration by Parts - MathLib API

## 確認済み API (2025-01-30)

### 1. 微分積分学第一基本定理 - `FundThmCalculus.lean`

#### `intervalIntegral.deriv_integral_right`
**概要**: 積分の上限を変数とする関数の微分

```lean
-- 基本形（推定される型シグネチャ）
theorem intervalIntegral.deriv_integral_right {f : ℝ → ℝ} {a : ℝ}
  (hf_integrable : IntervalIntegrable f volume a x)
  (hf_continuous : ContinuousAt f x) :
  deriv (fun y => ∫ t in a..y, f t) x = f x
```

**必要条件**:
- `f` が区間で可積分
- `f` が点 `x` で連続

**使用例（TODO実装）**:
```lean
theorem fundamental_theorem_part1 {f : ℝ → ℝ} {a : ℝ}
  (hf : Continuous f) :
  ∀ x, deriv (fun y => ∫ t in a..y, f t) x = f x := by
  intro x
  apply intervalIntegral.deriv_integral_right
  · exact hf.intervalIntegrable _ _
  · exact hf.continuousAt
```

---

### 2. 微分積分学第二基本定理 - `FundThmCalculus.lean`

#### `intervalIntegral.integral_eq_sub_of_hasDerivAt`
**概要**: 原始関数を使った定積分の計算（FTC-2）

```lean
-- 基本形（推定される型シグネチャ）
theorem intervalIntegral.integral_eq_sub_of_hasDerivAt {f F : ℝ → ℝ} {a b : ℝ}
  (hF : ∀ x ∈ Set.Ioo a b, HasDerivAt F (f x) x)
  (hf_integrable : IntervalIntegrable f volume a b)
  (hF_continuous : ContinuousOn F (Set.Icc a b)) :
  ∫ x in a..b, f x = F b - F a
```

**必要条件**:
- `F` が開区間 `(a, b)` で `f` を導関数として持つ
- `f` が区間で可積分  
- `F` が閉区間 `[a, b]` で連続

**使用例（TODO実装）**:
```lean
theorem fundamental_theorem_part2 {f F : ℝ → ℝ} {a b : ℝ}
  (hF : ∀ x ∈ Set.Icc a b, deriv F x = f x)
  (hf : ContinuousOn f (Set.Icc a b)) :
  ∫ x in a..b, f x = F b - F a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  -- HasDerivAt条件への変換が必要
  sorry
```

---

### 3. 部分積分 - `IntegrationByParts.lean`

#### `intervalIntegral.integral_mul_deriv_eq_deriv_mul`
**概要**: 部分積分の公式

```lean
-- 基本形（推定される型シグネチャ）
theorem intervalIntegral.integral_mul_deriv_eq_deriv_mul
  {u v : ℝ → ℝ} {a b : ℝ}
  (hu : ContinuousOn u (Set.Icc a b))
  (hv : ContinuousOn v (Set.Icc a b))
  (hu' : ∀ x ∈ Set.Ioo a b, HasDerivWithinAt u (u' x) (Set.Ioo a b) x)
  (hv' : ∀ x ∈ Set.Ioo a b, HasDerivWithinAt v (v' x) (Set.Ioo a b) x)
  (hu'_integrable : IntervalIntegrable u' volume a b)
  (hv'_integrable : IntervalIntegrable v' volume a b) :
  ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, u' x * v x
```

**必要条件**:
- `u`, `v` が閉区間で連続
- `u`, `v` が開区間で微分可能
- 導関数 `u'`, `v'` が可積分

**バリエーション**:
- `integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right`: 右微分版
- `integral_mul_deriv_eq_deriv_mul_of_hasDerivAt`: 両側微分版

**使用例（TODO実装）**:
```lean
theorem integration_by_parts {f g : ℝ → ℝ} {a b : ℝ}
  (hf : DifferentiableOn ℝ f (Set.Icc a b))
  (hg : DifferentiableOn ℝ g (Set.Icc a b)) :
  ∫ x in a..b, f x * deriv g x = 
  (f b * g b - f a * g a) - ∫ x in a..b, deriv f x * g x := by
  -- DifferentiableOnからHasDerivWithinAtへの変換
  -- ContinuousOnの導出
  -- IntervalIntegrableの証明
  sorry
```

---

## 実装戦略

### Phase 1: 第一基本定理
1. **API確認**: `#check intervalIntegral.deriv_integral_right`
2. **条件整理**: 
   - `Continuous f` → `IntervalIntegrable f`
   - `Continuous f` → `ContinuousAt f x`
3. **実装**: 条件の自動推論を含む証明

### Phase 2: 第二基本定理  
1. **API確認**: `#check intervalIntegral.integral_eq_sub_of_hasDerivAt`
2. **条件変換**:
   - `deriv F x = f x` → `HasDerivAt F (f x) x`
   - `ContinuousOn f` → `IntervalIntegrable f`
3. **実装**: HasDerivAt条件の構築

### Phase 3: 部分積分
1. **API選択**: 適切なバリエーションを選択
2. **条件導出**:
   - `DifferentiableOn` → `HasDerivWithinAt`
   - `DifferentiableOn` → `ContinuousOn`
   - 導関数の可積分性証明
3. **実装**: 完全な条件セットの構築

---

## 注意点

### FTCFilter
Mathlibは`FTCFilter`という型クラスを使用して、様々なフィルター（右微分、左微分、両側微分など）を統一的に扱っています。

### 条件の強さ
- **強い条件**: `Differentiable` → `HasDerivAt` → `HasDerivWithinAt`
- **弱い条件**: 片側微分、ほとんど至る所での微分

### IntervalIntegrable
多くの定理で`IntervalIntegrable`条件が必要。連続関数から自動的に導出可能：
```lean
hf.intervalIntegrable _ _
```

---

## 参照リンク

- [FundThmCalculus](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.html)
- [IntegrationByParts](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.html)

---

## 更新履歴
- 2025-01-30: 初版作成、FTC & 部分積分API調査完了