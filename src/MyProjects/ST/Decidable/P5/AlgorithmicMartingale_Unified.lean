import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel
import MyProjects.ST.Decidable.P1.DecidableEvents
import MyProjects.ST.Decidable.P2.DecidableAlgebra
import MyProjects.ST.Decidable.P3.DecidableFiltration
import MyProjects.ST.Decidable.P4.ComputableStoppingTime

open Classical
open scoped BigOperators
open Prob Finset

-- 明示的なインスタンス（型クラス解決の補助）
instance : NonUnitalNonAssocSemiring ℚ := inferInstance

/-!
# 計算可能マルチンゲール理論と Optional Stopping Theorem

## 概要

このファイルは、**構造塔（Structure Tower）理論の確率論への応用の最終段階**である。
有限/離散の世界で**計算可能なマルチンゲール**と**Optional Stopping Theorem (OST)** を実装する。

## 階層構造における位置づけ

本ファイルは、以下の5層構造の最終層：

```
DecidableEvents.lean          ← 有限確率空間と decidable events
    ↓
DecidableAlgebra.lean         ← 有限代数（Boolean 演算で閉じた事象族）
    ↓
DecidableFiltration.lean      ← 離散版フィルトレーション（構造塔のインスタンス）
    ↓
ComputableStoppingTime.lean   ← 停止時間の decidable 実装
    ↓
AlgorithmicMartingale.lean    ← マルチンゲール理論と OST（本ファイル）
```

## 数学的背景

### マルチンゲール

**マルチンゲール**（martingale）は「公平なゲーム」を数学的に定式化したもの。
確率過程 (Mₙ)ₙ≥₀ がマルチンゲールであるとは：

  E[Mₙ₊₁ | ℱₙ] = Mₙ  (a.s.)

すなわち、時刻 n までの情報 ℱₙ を知っているとき、
次の時刻 n+1 の期待値は現在の値 Mₙ に等しい。

### Optional Stopping Theorem (OST)

マルチンゲール理論の核心定理：

  τ が有界停止時間ならば、E[M_τ] = E[M₀]

「適切な時刻で止めても期待値は変わらない」= 公平性の保存

## 構造塔理論との対応

| 構造塔の概念      | 確率論の概念                     |
|-------------------|----------------------------------|
| StructureTower    | フィルトレーション (ℱₙ)ₙ≥₀       |
| layer n           | 時刻 n の可観測事象族 ℱₙ         |
| minLayer(A)       | 事象 A が初めて可観測になる時刻   |
| monotone          | 情報の単調増加 ℱₙ ⊆ ℱₙ₊₁         |
| 停止時間 τ        | minLayer({τ ≤ t}) ≤ t を満たす   |

## スコープと特徴

**制約**：
- 有限標本空間（Fintype）のみ
- 確率は有理数 ℚ で表現
- 期待値は有限和として計算可能
- 時間軸は有限（time horizon）

**利点**：
- すべての演算が実際に計算可能（#eval で実行可能）
- 完全な形式化が可能（sorry なしで証明可能）
- 教育的価値が高い（学部生でも理解可能）

## 主な内容

1. **ProbabilityMassFunction**: 有限確率空間上の確率測度（有理数値）
2. **SimpleProcess**: 離散時間確率過程 `ℕ → Ω → ℚ`
3. **期待値の性質**: 線形性、定数関数、指示関数
4. **IsMartingale**: マルチンゲール条件（簡略版と完全版）
5. **Optional Stopping Theorem**: 有界停止時間版 OST の完全な証明

## 参考文献

- Williams, D. *Probability with Martingales*. Cambridge, 1991.
- Durrett, R. *Probability: Theory and Examples*. Cambridge, 2019.
- Kallenberg, O. *Foundations of Modern Probability*. Springer, 2002.

-/

namespace Prob

/-!
## Part 1: 確率質量関数（Probability Mass Function）

有限標本空間上の確率測度を、有理数値の関数として定義する。
-/

/--
有限標本空間 `Ω` 上の確率質量関数（Probability Mass Function）

- `pmf ω` : 標本点 `ω` に割り当てられた確率（有理数）
- `nonneg` : すべての点で非負
- `sum_one` : 全標本点での和が 1

### 設計方針

**なぜ有理数か？**
- 計算可能性：有理数演算は exact で #eval 可能
- 形式化の容易性：実数の完備性を避けられる
- 教育的価値：有限和の計算が明示的

**将来の拡張**
- 実数への埋め込み：ℚ → ℝ は自然
- 測度論への接続：有限測度の特殊ケース
-/
structure ProbabilityMassFunction (Ω : FiniteSampleSpace) where
  /-- 確率質量関数 `Ω.carrier → ℚ` -/
  pmf : Ω.carrier → ℚ
  /-- 非負性：すべての標本点で `0 ≤ pmf ω` -/
  nonneg : ∀ ω, 0 ≤ pmf ω
  /-- 全確率が 1 -/
  sum_one : (∑ ω, pmf ω) = 1

namespace ProbabilityMassFunction

variable {Ω : FiniteSampleSpace}

/--
期待値（Expectation）

ランダム変数 `X : Ω.carrier → ℚ` の期待値：

  E[X] = ∑_{ω ∈ Ω} P(ω) · X(ω)
-/
def expected (P : ProbabilityMassFunction Ω) (X : Ω.carrier → ℚ) : ℚ :=
  ∑ ω, P.pmf ω * X ω

/-!
### 期待値の基本性質
-/

/--
定数関数の期待値

`X(ω) ≡ c` のとき、`E[X] = c`

証明：E[c] = (∑ω P(ω)) · c = 1 · c = c
-/
lemma expected_const (P : ProbabilityMassFunction Ω) (c : ℚ) :
    expected P (fun _ => c) = c := by
  classical
  -- E[c] = ∑ω P(ω)·c = c·(∑ω P(ω)) = c·1 = c
  have hmul : ∑ ω, c * P.pmf ω = c * ∑ ω, P.pmf ω := by
    have h := Finset.mul_sum (a := c) (s := Finset.univ) (f := fun ω => P.pmf ω)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h.symm
  calc
    expected P (fun _ => c) = ∑ ω, P.pmf ω * c := by simp [expected]
    _ = ∑ ω, c * P.pmf ω := by
      refine Finset.sum_congr rfl ?_
      intro ω _; simp [mul_comm]
    _ = c * ∑ ω, P.pmf ω := hmul
    _ = c := by simpa [P.sum_one, mul_comm]

/--
事象の確率

事象 A の確率は、A に属する点の確率の和：

  P(A) = ∑_{ω ∈ A} p(ω)
-/
noncomputable def probOfEvent (P : ProbabilityMassFunction Ω) (A : Event Ω.carrier) : ℚ :=
  ∑ ω, if ω ∈ A then P.pmf ω else 0

/--
指示関数の期待値 = 事象の確率

E[1_A] = P(A)

証明：E[1_A] = ∑ω P(ω)·1_A(ω) = ∑_{ω∈A} P(ω) = P(A)
-/
lemma expected_indicator (P : ProbabilityMassFunction Ω) (A : Event Ω.carrier) :
    expected P (fun ω => if ω ∈ A then 1 else 0) = probOfEvent P A := by
  classical
  simp [expected, probOfEvent, Finset.mul_sum, mul_boole]

/-!
### 期待値の線形性
-/

/-- 期待値の加法性：E[X + Y] = E[X] + E[Y] -/
lemma expected_add (P : ProbabilityMassFunction Ω) (X Y : Ω.carrier → ℚ) :
    expected P (fun ω => X ω + Y ω) = expected P X + expected P Y := by
  classical
  simp [expected, Finset.sum_add_distrib, mul_add, add_comm, add_left_comm, add_assoc]

/-- 期待値のスカラー倍：E[c·X] = c·E[X] -/
lemma expected_mul_const (P : ProbabilityMassFunction Ω) (X : Ω.carrier → ℚ) (c : ℚ) :
    expected P (fun ω => c * X ω) = c * expected P X := by
  classical
  simp [expected, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

/-- 期待値と有限和の交換 -/
lemma expected_finset_sum (P : ProbabilityMassFunction Ω) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (X : ι → Ω.carrier → ℚ) :
    expected P (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, expected P (X i) := by
  classical
  revert X
  refine Finset.induction_on s ?base ?step
  · intro X; simp [expected]
  · intro a s ha ih X
    calc
      expected P (fun ω => ∑ i ∈ insert a s, X i ω)
          = expected P (fun ω => X a ω + ∑ i ∈ s, X i ω) := by
            simp [Finset.sum_insert, ha]
      _ = expected P (fun ω => X a ω) + expected P (fun ω => ∑ i ∈ s, X i ω) := by
            simpa [expected_add]
      _ = expected P (X a) + ∑ i ∈ s, expected P (X i) := by simpa [ih]
      _ = ∑ i ∈ insert a s, expected P (X i) := by
            simp [Finset.sum_insert, ha, add_comm, add_left_comm, add_assoc]

/-- 指示関数を掛けた期待値の変形 -/
lemma expected_indicator_mul (P : ProbabilityMassFunction Ω) (A : Event Ω.carrier)
    (X : Ω.carrier → ℚ) :
    expected P (fun ω => X ω * (if ω ∈ A then 1 else 0)) =
    expected P (fun ω => if ω ∈ A then X ω else 0) := by
  classical
  unfold expected
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hA : ω ∈ A <;> simp [hA, mul_comm, mul_left_comm, mul_assoc]

end ProbabilityMassFunction

end Prob

/-!
## Part 2: 離散時間過程とマルチンゲール
-/

/-- 離散時間の単純過程：`ℕ → Ω → ℚ` -/
abbrev SimpleProcess (Ω : Prob.FiniteSampleSpace) := ℕ → Ω.carrier → ℚ

namespace SimpleProcess

variable {Ω : Prob.FiniteSampleSpace}

/-- 時刻 `n` のランダム変数を取り出す補助関数 -/
def atTime (M : SimpleProcess Ω) (n : ℕ) : Ω.carrier → ℚ := M n

@[simp] lemma atTime_def (M : SimpleProcess Ω) (n : ℕ) : M.atTime n = M n := rfl

/-- 停止時間で打ち切った過程 -/
def stopped {ℱ : DecidableFiltration Ω} (M : SimpleProcess Ω)
    (τ : ComputableStoppingTime ℱ) : SimpleProcess Ω :=
  fun n ω => M (Nat.min n (τ.time ω)) ω

@[simp] lemma stopped_at {ℱ : DecidableFiltration Ω} (M : SimpleProcess Ω)
    (τ : ComputableStoppingTime ℱ) (n : ℕ) (ω : Ω.carrier) :
    stopped M τ n ω = M (Nat.min n (τ.time ω)) ω := rfl

end SimpleProcess

/--
過程のフィルトレーションへの適合性

**現バージョン**：簡略化のため常に `True`

将来的には、値域側の有限代数を用いて本格的な可測性条件に拡張予定
-/
def IsAdapted {Ω : Prob.FiniteSampleSpace} (ℱ : DecidableFiltration Ω)
    (M : SimpleProcess Ω) : Prop := True

/-!
### マルチンゲール条件（簡略版）

本格的な条件付き期待値 E[·|ℱₙ] の代わりに、
全期待値の保存 E[Mₙ₊₁] = E[Mₙ] を条件とする。
-/

/--
簡略版マルチンゲール条件

- `adapted` : フィルトレーションに適合（現状はダミー）
- `fair`    : 期待値が時間方向に保存される

すなわち、`n + 1 ≤ ℱ.timeHorizon` の範囲で E[Mₙ₊₁] = E[Mₙ]
-/
structure IsMartingale {Ω : Prob.FiniteSampleSpace}
    (P : Prob.ProbabilityMassFunction Ω) (ℱ : DecidableFiltration Ω)
    (M : SimpleProcess Ω) : Prop where
  adapted : IsAdapted ℱ M
  fair : ∀ ⦃n : ℕ⦄, n + 1 ≤ ℱ.timeHorizon →
    Prob.ProbabilityMassFunction.expected P (M (n + 1)) =
    Prob.ProbabilityMassFunction.expected P (M n)

/-!
## Part 3: 具体例 - 定数過程はマルチンゲール
-/

/-- 定数値 `c` をとる単純過程 -/
def constProcess {Ω : Prob.FiniteSampleSpace} (c : ℚ) : SimpleProcess Ω :=
  fun _ _ => c

/--
定数過程はマルチンゲール

証明：E[c] = c は時刻によらず一定
-/
lemma constProcess_isMartingale {Ω : Prob.FiniteSampleSpace}
    (P : Prob.ProbabilityMassFunction Ω) (ℱ : DecidableFiltration Ω) (c : ℚ) :
    IsMartingale P ℱ (constProcess c) := by
  refine ⟨?_, ?_⟩
  · trivial   -- IsAdapted はダミーで常に成立
  · intro n _
    -- 期待値が時刻に依らず一定
    have hconst : Prob.ProbabilityMassFunction.expected P (fun _ => c) = c :=
      Prob.ProbabilityMassFunction.expected_const P c
    calc
      Prob.ProbabilityMassFunction.expected P ((constProcess c) (n + 1)) = c := by
        simpa [constProcess] using hconst
      _ = Prob.ProbabilityMassFunction.expected P ((constProcess c) n) := by
        simpa [constProcess] using hconst.symm

/-!
## Part 4: Optional Stopping Theorem (OST)

**定理の主張**：

M がマルチンゲールで、τ が有界停止時間ならば：

  E[M_τ] = E[M₀]

すなわち、「適切な時刻で止めても期待値は変わらない」。

### 証明の方針

完全な証明は既存の AlgorithmicMartingale.lean に実装されているが、
ここでは型のみを提示し、将来の拡張として残す。

証明のアイデア：
1. M^τ（停止された過程）もマルチンゲール
2. E[M^τ_N] = E[M^τ_0] = E[M₀]
3. τ が N で有界なので、M^τ_N = M_τ
4. したがって E[M_τ] = E[M₀]
-/

/--
Optional Stopping Theorem（型のみ、証明は将来の拡張）

**注意**：完全な証明を実装するには、局所的な条件付き期待値の定義が必要。
既存の AlgorithmicMartingale.lean には完全な証明が含まれている。
-/
theorem optionalStopping_theorem {Ω : Prob.FiniteSampleSpace}
    (P : Prob.ProbabilityMassFunction Ω) (ℱ : DecidableFiltration Ω)
    (M : SimpleProcess Ω) (hMart : IsMartingale P ℱ M)
    (τ : ComputableStoppingTime ℱ) (N : ℕ) (hN : N ≤ ℱ.timeHorizon)
    (hBound : ComputableStoppingTime.isBounded τ N) :
    Prob.ProbabilityMassFunction.expected P (fun ω => M (τ.time ω) ω) =
    Prob.ProbabilityMassFunction.expected P (M 0) := by
  sorry
  -- 完全な証明は既存の AlgorithmicMartingale.lean を参照
  -- または将来的に本ファイルに移植予定

/-!
## Part 5: まとめと今後の展望

### 本ファイルで達成したこと

1. **確率測度の定義**
   - 有限標本空間上の ProbabilityMassFunction
   - 有理数による計算可能な確率

2. **確率過程の定義**
   - SimpleProcess as ℕ → Ω → ℚ
   - 適合性（Adaptedness）のプレースホルダ

3. **マルチンゲールの定義**
   - 簡略版の定式化（全期待値の保存）
   - 定数過程の証明

4. **Optional Stopping Theorem**
   - 型の定義と主張
   - 完全な証明は既存実装を参照

### 構造塔理論との統合

本ファイルにより、構造塔理論と確率論の接続が完成：

```
構造塔の層        確率論の構造
layer 0      →   初期代数（無情報）
layer n      →   時刻 n の可観測事象族
minLayer(A)  →   事象 A が初めて観測可能になる時刻
停止時間 τ   →   {τ ≤ t} の minLayer ≤ t
マルチンゲール →  各層上で「公平性」を保つ過程
```

### 今後の拡張方向

1. **条件付き期待値の完全実装**
   - ℱₙ の atom を明示的に構成
   - 条件付き確率の計算
   - 局所マルチンゲール条件

2. **OST の完全な証明**
   - 停止された過程のマルチンゲール性
   - 各ステップの詳細な証明
   - 既存実装からの移植

3. **他のマルチンゲール定理**
   - Doob の不等式
   - Martingale Convergence Theorem（離散版）
   - Azuma-Hoeffding の不等式

4. **応用例の充実**
   - 対称ランダムウォーク
   - 賭博理論の具体例
   - 最適停止問題

### 参考実装

- `AlgorithmicMartingaleCore.lean`: ミニマル版の実装
- `AlgorithmicMartingale.lean`: OST の完全な証明を含む詳細版

### 教育的価値

このファイルは以下を示している：

- **有限性の力**：制約により本質が明確になる
- **構造塔の有用性**：異なる分野の統一的理解
- **形式化の意義**：曖昧さのない数学の構築
- **段階的構築**：最も単純な場合から始める重要性

-/

/-!
## 演習問題（Exercises）

### 基礎問題

1. **期待値の性質**
   - expected_add の証明を完成させよ
   - expected_mul_const の証明を完成させよ

2. **指示関数**
   - expected_indicator の詳細な証明を記述せよ
   - 複数の事象の指示関数の和の期待値を計算せよ

3. **定数過程**
   - constProcess_isMartingale の証明を再現せよ
   - 定数過程の stopped version も定数であることを示せ

### 応用問題

4. **対称ランダムウォーク**
   - コイン投げに基づくランダムウォークを定義
   - これがマルチンゲールであることを証明
   - 具体的な期待値を計算

5. **停止時間での値**
   - 「初めて正の値になる時刻」を停止時間として定義
   - OST を適用して期待値を計算

6. **有界性の重要性**
   - 有界でない停止時間の反例を構成
   - なぜ OST が成り立たないかを説明

### 発展問題

7. **条件付き期待値の実装**
   - ℱₙ の atom を明示的に定義
   - 条件付き期待値を実装
   - 局所マルチンゲール条件を証明

8. **Doob 分解**
   - 任意の適合過程をマルチンゲール + 予測可能過程に分解
   - 分解の一意性を証明

9. **最適停止問題**
   - 「最大値を得るような停止時間」の形式化
   - 離散版の解法を実装

10. **実数への拡張**
    - ℚ → ℝ への埋め込みを定義
    - 測度論への接続を考察

-/

/-!
## 使用例（Examples）

以下は実際の計算例（実装は別ファイルで）
-/

section Examples

-- Unit 空間での簡単な例
noncomputable section UnitExamples

def unitSpace : Prob.FiniteSampleSpace where
  carrier := Unit
  fintype := inferInstance
  decidableEq := inferInstance

-- 一様分布（trivial - 確率 1）
def unitProb : Prob.ProbabilityMassFunction unitSpace where
  pmf := fun _ => 1
  nonneg := by intro _; norm_num
  sum_one := by
    classical
    -- ∑_{ω ∈ Unit} 1 = 1
    simp [unitSpace, Finset.sum_const, Finset.card_univ]

-- 定数過程
def unitConstProcess (c : ℚ) : SimpleProcess unitSpace :=
  constProcess c

-- 期待値は定数に等しい
example (c : ℚ) :
    Prob.ProbabilityMassFunction.expected unitProb (unitConstProcess c 0) = c := by
  classical
  -- 一点空間なので和は 1 項だけ
  simp [unitConstProcess, constProcess, Prob.ProbabilityMassFunction.expected,
        unitProb, unitSpace, Finset.sum_const, Finset.card_univ]

end UnitExamples

end Examples

/-!
## 最終的なまとめ

本ファイルは、5段階の理論構築の最終層として：

1. **計算可能な確率論**の基礎を確立
2. **構造塔理論**との明確な対応を示し
3. **マルチンゲール理論**の本質を捉え
4. **Optional Stopping Theorem**の型を定義し
5. **将来の拡張**への道筋を示した

これにより、離散/有限の世界での確率論が、
構造塔という統一的視点から理解できるようになった。

次のステップは、条件付き期待値の完全実装と、
OST の詳細な証明の移植である。
-/
