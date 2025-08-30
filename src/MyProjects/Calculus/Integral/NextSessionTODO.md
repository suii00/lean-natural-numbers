# Next Session TODO - Integral Advanced Implementation

## 🎯 次回セッション目標

### 主目標: 微分積分学基本定理の完全実装
- **Mode**: explore または stable（ユーザー指定）
- **Focus**: 高優先度TODO → 中優先度TODO → 低優先度TODO
- **Target File**: `IntegralExploreComplete.lean` 拡張または新ファイル作成

---

## 📋 優先度別実装計画

### 🔴 **Phase 1: 高優先度 (Must Do)**

#### 1. **fundamental_theorem_part1** - 第一基本定理
```lean
-- 目標: d/dx ∫[a,x] f(t)dt = f(x) の完全実装
theorem fundamental_theorem_part1 {f : ℝ → ℝ} {a : ℝ}
  (hf : Continuous f) :
  ∀ x, deriv (fun y => ∫ t in a..y, f t) x = f x
```

**実装戦略**:
1. **API調査**: 
   ```lean
   #check MeasureTheory.deriv_integral_right
   example : deriv (fun x => ∫ t in a..x, f t) = f := by library_search
   ```

2. **候補API**:
   - `MeasureTheory.deriv_integral_right`
   - `deriv_integral_of_continuous`
   - `deriv_integral_right`

3. **想定課題**:
   - IntervalIntegrable条件の自動推論
   - Continuous条件からIntervalIntegrableへの変換
   - 変数の適切なスコープ管理

**成功基準**: コンパイル通過 + 数学的正確性

---

#### 2. **fundamental_theorem_part2** - 第二基本定理  
```lean
-- 目標: ∫[a,b] f'(x)dx = f(b)-f(a) の完全実装
theorem fundamental_theorem_part2 {f F : ℝ → ℝ} {a b : ℝ}
  (hF : ∀ x ∈ Set.Icc a b, deriv F x = f x)
  (hf : ContinuousOn f (Set.Icc a b)) :
  ∫ x in a..b, f x = F b - F a
```

**実装戦略**:
1. **API調査**:
   ```lean
   #check integral_eq_sub_of_hasDerivAt
   #check integral_hasDerivAt  
   example {F : ℝ → ℝ} : ∫ x in a..b, deriv F x = F b - F a := by library_search
   ```

2. **候補API**:
   - `integral_eq_sub_of_hasDerivAt`
   - `integral_hasDerivAt`
   - `integral_eq_sub_of_deriv`

3. **想定課題**:
   - `deriv F x = f x` 条件の適切な表現
   - Set.Icc条件とHasDerivAt条件の関係
   - ContinuousOn条件の活用

**成功基準**: 数学的に正確な第二基本定理の証明

---

#### 3. **integration_by_parts** - 部分積分
```lean  
-- 目標: ∫ uv' = uv - ∫ u'v の完全実装
theorem integration_by_parts {f g : ℝ → ℝ} {a b : ℝ}
  (hf : DifferentiableOn ℝ f (Set.Icc a b))
  (hg : DifferentiableOn ℝ g (Set.Icc a b)) :
  ∫ x in a..b, f x * deriv g x = 
  (f b * g b - f a * g a) - ∫ x in a..b, deriv f x * g x
```

**実装戦略**:
1. **API調査**:
   ```lean
   #check integral_parts
   #check integral_by_parts
   #check integral_mul_deriv
   example : ∫ x in a..b, u x * (deriv v x) = sorry := by library_search
   ```

2. **候補API**:  
   - `integral_parts`
   - `integral_by_parts`
   - `integral_mul_deriv_eq_sub_integral_deriv_mul`

3. **想定課題**:
   - DifferentiableOn条件の複雑な管理
   - 連続性とHasDerivAt条件の組み合わせ
   - 境界項の正確な計算

**成功基準**: 部分積分公式の完全実装

---

### 🟡 **Phase 2: 中優先度 (Should Do)**

#### 4. **integral_linear** - 積分の線形性
```lean
theorem integral_linear {f g : ℝ → ℝ} (α β : ℝ) (a b : ℝ) 
  (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b) :
  ∫ x in a..b, (α * f x + β * g x) = 
  α * (∫ x in a..b, f x) + β * (∫ x in a..b, g x)
```

**実装戦略**:
- `integral_add` + `integral_const_mul` 組み合わせ
- IntervalIntegrable条件の適切な管理

#### 5. **antiderivative_relation** - 原始関数の関係
**実装戦略**: 第二基本定理の応用として実装

#### 6. **substitution_concept** - 置換積分
**実装戦略**: 高度なMathlib API調査が必要

### 🟢 **Phase 3: 低優先度 (Could Do)**

#### 7. **geometric_meaning** - 幾何学的解釈
**実装戦略**: `integral_nonneg`系API使用

---

## 🔍 実装前準備

### 事前API調査項目
```lean
-- 次回セッション開始時に実行
#check MeasureTheory.deriv_integral_right
#check integral_eq_sub_of_hasDerivAt  
#check integral_parts
#check integral_add
#check integral_const_mul
#check integral_nonneg_of_ae
```

### Library Search実行予定
```lean
-- 第一基本定理
example (f : ℝ → ℝ) (hf : Continuous f) : 
  deriv (fun x => ∫ t in a..x, f t) = f := by library_search

-- 第二基本定理  
example (F : ℝ → ℝ) (a b : ℝ) : 
  ∫ x in a..b, deriv F x = F b - F a := by library_search

-- 部分積分
example (u v : ℝ → ℝ) (a b : ℝ) :
  ∫ x in a..b, u x * deriv v x = sorry := by library_search
```

---

## 🚨 予想される困難と対処法

### 想定エラーパターン
1. **IntervalIntegrable自動推論失敗**
   - 対処: 明示的条件追加
   - 参考: 今回のintegral_linear実装

2. **HasDerivAt vs deriv条件混乱**
   - 対処: Mathlib条件の詳細調査
   - 参考: 今回のエラー解決記録

3. **境界条件とSet.Icc管理**
   - 対処: 段階的条件確認
   - 参考: 今回の成功パターン

### エラー対処リソース
- **エラー記録**: `03_library/Error/Mathlib/IntegralImplementationErrors_2025-01-30.md`
- **成功パターン**: `IntegralExploreComplete.lean`
- **API参考**: 今回作成の各バージョンファイル

---

## 📈 進捗測定

### Phase 1完了基準
- [ ] fundamental_theorem_part1: コンパイル成功
- [ ] fundamental_theorem_part2: コンパイル成功  
- [ ] integration_by_parts: コンパイル成功
- [ ] 3つの定理すべてsorryなしで証明完了

### 全体完了基準
- [ ] 高優先度TODO: 3/3 完成
- [ ] 中優先度TODO: 3/3 完成
- [ ] 低優先度TODO: 1/1 完成
- [ ] **claude.txt完全制覇** ✅

### 成功報酬
**全TODO完成時**: Mathlib積分マスター認定 🏆

---

## 💡 実装のコツ

### 成功への3原則
1. **段階的アプローチ**: 一度に1つのTODOに集中
2. **エラー記録活用**: 今回の解決パターンを再利用
3. **数学理解重視**: 定理の意味を理解してから実装

### 推奨セッション構成
1. **API調査** (10分): library_search + #check実行
2. **実装** (30分): 1つのTODOに集中実装
3. **テスト** (10分): コンパイル + 具体例確認
4. **記録** (10分): エラー・成功パターンの記録

---

**次回セッション宣言**: 
> **"微分積分学基本定理完全制覇への挑戦！"** 🎯

準備万端、実装戦略明確、成功への道筋確立 ✅