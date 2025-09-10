# 解析学1 第1回：関数とグラフ・面積
## 基本的な関数の性質と積分の導入

### 問題1：偶関数の基本性質

**問題文**：
実数上で定義された関数 f(x) = x² が偶関数であること（すなわち、すべての実数 x に対して f(-x) = f(x) が成り立つこと）を証明してください。

**Leanでの問題定義**：
```lean
import Mathlib
open Real

theorem square_is_even_function : ∀ x : ℝ, (-x)^2 = x^2 := by
  sorry
```

**証明のヒント**：
- `ring` タクティクで代数的計算を自動化できます
- または `simp [sq]` で二乗の定義を展開してから計算
- 負の数の二乗の性質 `neg_sq` が使えるかもしれません

**大学レベルへの発展**：
- 一般の偶関数の積分における対称性の利用
- フーリエ級数における偶関数成分（余弦項）への展開
- 測度論的観点からの対称関数の積分

---

### 問題2：定数関数の積分

**問題文**：
定数関数 f(x) = c（c は正の実数）の区間 [a, b]（a < b）における定積分が c(b - a) に等しいことを証明してください。

**Leanでの問題定義**：
```lean
import Mathlib
open Real MeasureTheory Interval
open scoped Interval

theorem constant_integral (c : ℝ) (a b : ℝ) (hc : 0 < c) (hab : a < b) :
    ∫ x in a..b, c = c * (b - a) := by
  sorry
```

**証明のヒント**：
- `intervalIntegral.integral_const` が直接使えます
- または `simp [integral_const]` で簡約
- 積分の線形性を使った方法もあります

**大学レベルへの発展**：
- リーマン和による積分の定義からの直接証明
- ルベーグ積分における定数関数の積分
- 多変数の場合の体積計算への一般化

---

### 問題3：一次関数の積分

**問題文**：
一次関数 f(x) = x の区間 [0, a]（a > 0）における定積分が a²/2 に等しいことを証明してください。これは直角三角形の面積に対応します。

**Leanでの問題定義**：
```lean
import Mathlib
open Real MeasureTheory Interval
open scoped Interval

theorem linear_integral (a : ℝ) (ha : 0 < a) :
    ∫ x in (0:ℝ)..a, x = a^2 / 2 := by
  sorry
```

**証明のヒント**：
- `integral_id` を使って ∫x dx を計算
- 原始関数は x²/2 であることを利用
- `simp [integral_id, sq]` で簡約できます

**大学レベルへの発展**：
- 一般の多項式の積分公式への拡張
- 部分積分を使った高次の積分計算
- 数値積分（台形則）の誤差評価

---

### 問題4：偶関数の対称積分

**問題文**：
偶関数 f(x) = x² の区間 [-a, a]（a > 0）における定積分が、区間 [0, a] における定積分の2倍に等しいことを証明してください。

**Leanでの問題定義**：
```lean
import Mathlib
open Real MeasureTheory Interval
open scoped Interval

theorem even_function_symmetric_integral (a : ℝ) (ha : 0 < a) :
    ∫ x in (-a)..a, x^2 = 2 * ∫ x in (0:ℝ)..a, x^2 := by
  sorry
```

**証明のヒント**：
- `integral_comp_neg` で積分区間の変換
- 偶関数の性質 `(-x)^2 = x^2` を利用
- `intervalIntegral.integral_add_adjacent_intervals` で区間を分割

**大学レベルへの発展**：
- 一般の偶関数・奇関数の対称積分の性質
- フーリエ変換における対称性の利用
- 物理学における対称性と保存則の関係

---

### 問題5：区分的に定義された関数の積分

**問題文**：
次の区分的に定義された関数の区間 [0, 2] における定積分を計算してください：
f(x) = { 1 (0 ≤ x ≤ 1), x (1 < x ≤ 2) }

**Leanでの問題定義**：
```lean
import Mathlib
open Real MeasureTheory Interval Set
open scoped Interval

noncomputable def piecewise_function (x : ℝ) : ℝ :=
  if x ≤ 1 then 1 else x

theorem piecewise_integral :
    ∫ x in (0:ℝ)..(2:ℝ), piecewise_function x = 5/2 := by
  sorry
```

**証明のヒント**：
- `intervalIntegral.integral_add_adjacent_intervals` で [0,1] と [1,2] に分割
- 各区間で関数の定義を展開
- `split_ifs` でif文を処理

**大学レベルへの発展**：
- より複雑な区分的連続関数の積分
- 不連続点を持つ関数のリーマン可積分性
- ルベーグ積分における階段関数の役割

---

### チャレンジ問題：奇関数と偶関数の積

**問題文**：
f(x) が奇関数（f(-x) = -f(x)）、g(x) が偶関数（g(-x) = g(x)）のとき、それらの積 h(x) = f(x)g(x) が奇関数であることを証明してください。さらに、h(x) の対称区間 [-a, a] での積分が0になることを示してください。

**Leanでの問題定義**：
```lean
import Mathlib
open Real MeasureTheory Interval
open scoped Interval

theorem odd_times_even_is_odd 
  (f g : ℝ → ℝ) 
  (hf_odd : ∀ x, f (-x) = -f x)
  (hg_even : ∀ x, g (-x) = g x) :
  ∀ x, (f * g) (-x) = -(f * g) x := by
  sorry

-- ボーナス：積分が0になることの証明
theorem odd_function_symmetric_integral_zero
  (h : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
  (h_odd : ∀ x, h (-x) = -h x)
  (h_int : IntegrableOn h (Icc (-a) a)) :
  ∫ x in (-a)..a, h x = 0 := by
  sorry
```

**証明のヒント**：
- 関数の積の定義 `Pi.mul_apply` を使用
- 奇関数・偶関数の性質を組み合わせる
- 積分については `integral_comp_neg` と奇関数の性質を組み合わせる

**大学レベルへの発展**：
- フーリエ級数における直交性
- 群論的観点からの対称性の分類
- 物理学における選択則とパリティ

---

## 完全な証明例（問題1）

```lean
import Mathlib
open Real

theorem square_is_even_function : ∀ x : ℝ, (-x)^2 = x^2 := by
  intro x
  ring
  -- または以下のような詳細な証明も可能：
  -- rw [sq, sq]
  -- rw [neg_mul_neg]
```

この証明では、`ring` タクティクが代数的な計算を自動的に処理します。`(-x)^2 = (-x) * (-x) = x * x = x^2` という変形を内部で行っています。