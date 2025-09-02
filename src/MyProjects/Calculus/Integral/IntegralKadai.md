# IntegralKadai 解説（課題1〜6＋チャレンジ）

このドキュメントは `src/MyProjects/Calculus/Integral/IntegralKadai.lean` の数学的背景と、利用している mathlib API の要点を解説します。目的は、積分の基本公式から微分積分学の基本定理、部分積分までを Lean で安全に再利用可能な形でまとめることです。

## 1. 依存と全体設計

- インポート
  - `Mathlib.Analysis.SpecialFunctions.Integrals.Basic`（基本的な積分公式: べき、sin、cos 等）
  - `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`（区間積分の基本 API）
  - `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`（微分積分学の基本定理）
  - `Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts`（部分積分）

- 設計方針
  - 既存の確立済み定理（API）を積極的に利用し、最小限の証明で安全に結論へ到達する。
  - 実用上よく現れる形（例えば `•` と `*` の変換、`uIcc` 条件）を明示的に整える。

## 2. 使用 API の要点

- `integral_pow`：べき関数の区間積分
- `integral_sin` / `integral_cos`：三角関数の区間積分
- `intervalIntegral.integral_const`：定数の区間積分（結果は `(b - a) • c` で返る）
- `intervalIntegral.integral_add`：加法性
- `intervalIntegral.integral_const_mul`：定数倍の引き上げ
- `intervalIntegral.deriv_integral_right`：第一基本定理（上限を変数とする積分の微分）
- `intervalIntegral.integral_eq_sub_of_hasDerivAt`：第二基本定理（原始関数による評価）
- `intervalIntegral.integral_mul_deriv_eq_deriv_mul`：部分積分

補助事実（よく使う）
- `hf.intervalIntegrable a b`：連続性から区間可積分性が従う。
- `hf.stronglyMeasurable.stronglyMeasurableAtFilter`：連続関数の強測度可能性。
- `IntervalIntegrable.const_mul`：被積分関数の定数倍で可積分性が保存される。

## 3. 各課題の数学的内容

### 課題1：定数関数の積分
定数関数 `c` の区間積分は区間長に比例し、`∫_{a}^{b} c dx = c (b-a)`。
mathlib の定理は `(b - a) • c`（スカラー倍）で返るため、`smul_eq_mul` と可換律で通常の積 `c * (b - a)` に整形します。

### 課題2：べき関数の積分
`∫_{a}^{b} x^n dx = (b^{n+1} - a^{n+1}) / (n+1)`（`n ≥ 0`）を `integral_pow` でそのまま利用します。

### 課題3：正弦（と余弦）の積分
`∫_{a}^{b} sin x dx = cos a - cos b`、`∫_{a}^{b} cos x dx = sin b - sin a` を既存 API で直接利用します。

### 課題4：微分積分学の基本定理（第一）
関数 `F(x) := ∫_{a}^{x} f(t) dt` は、`f` が連続なら `F' = f`。`intervalIntegral.deriv_integral_right` は点ごとの仮説（連続・強測度可能・区間可積分）を要求しますが、`Continuous f` から標準的に導けます。

直観：上限が `x` の面積関数は、`x` を微小に動かすと幅が微小、縦が `f(x)` の長方形の面積に等しいため、導関数が `f(x)` になるという幾何学的理解と整合します。

### 課題5：微分積分学の基本定理（第二）
原始関数 `F` が `(a,b)` で `HasDerivAt F (f x) x` を満たし、`f` が可積分なら、`∫_{a}^{b} f = F(b) - F(a)`。

本ファイルでは `intervalIntegral.integral_eq_sub_of_hasDerivAt` に合わせ、`Set.uIcc a b`（順序入替も許容する閉区間）上の `HasDerivAt` を仮定に採用しています。しばしば「`deriv F x = f x` 形式」を使いたくなりますが、その場合は `HasDerivAt` へ持ち上げる補題を併用してこの API を適用するのが実務的です。

### 課題6：積分の線形性
`∫ (α f + β g) = α ∫ f + β ∫ g`。`integral_add` と `integral_const_mul` の合成で示します。可積分性は `IntervalIntegrable.const_mul` で安定します。

### チャレンジ：部分積分
`∫ f · g' = f g − ∫ f' · g` の実装は `intervalIntegral.integral_mul_deriv_eq_deriv_mul` を利用します。仮定は `uIcc` 上の `HasDerivAt` と、導関数の可積分性です。`deriv` 形の系は、`f' x = deriv f x` などと置き換えて直ちに得られます。

## 4. 例と小技

- 例：`∫₀¹ x² dx = 1/3` は `integral_pow` の右辺と一致します。
- 例：`∫₀^π sin x dx = 2` は `integral_sin` と三角恒等式 `cos 0 = 1, cos π = -1` で即座に計算できます。

実務上の小技
- `•` と `*` の変換：`simp [smul_eq_mul, mul_comm]`。
- 区間条件：`Set.uIcc a b` は `a ≤ b` かどうかに依らず対称に扱える便利な集合。
- 補助タクティク：`simp`, `norm_num` は数値・基本恒等式の整理に有効。

## 5. 形式化の価値

本ファイルの構成により、
- 典型的な積分計算を mathlib の信頼できる定理として再利用可能にし、
- FTC（第一・第二）や部分積分といった理論的中核を、それぞれの API に沿って最小限の仮定で適用できるようになりました。

教育的にも、
- 「連続性 ⇒ 可積分性・強測度可能性」などの条件伝播、
- `HasDerivAt` と `deriv` の役割分担、
- `uIcc` による区間の対称化

といった Lean / mathlib 特有の観点が整理されます。

---

参考：対象ファイル
- `src/MyProjects/Calculus/Integral/IntegralKadai.lean`

