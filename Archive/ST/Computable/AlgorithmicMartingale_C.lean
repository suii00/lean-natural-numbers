import Mathlib.Data.Rat.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Real.Basic
import MyProjects.ST.Decidable.P1.DecidableEvents
import MyProjects.ST.Decidable.P2.DecidableAlgebra
import MyProjects.ST.Decidable.P3.DecidableFiltration
import MyProjects.ST.Decidable.P4.ComputableStoppingTime

open BigOperators Prob Classical
open Finset

/-!
# 計算可能マルチンゲール理論と Optional Stopping Theorem

このファイルは、構造塔（Structure Tower）理論の確率論への応用の**最終段階**である。
有限/離散の世界で**計算可能なマルチンゲール**と**Optional Stopping Theorem (OST)** を実装する。

## 数学的背景

**マルチンゲール**（martingale）とは、「公平なゲーム」を数学的に定式化したものである。
確率過程 (Mₙ)ₙ≥₀ がマルチンゲールであるとは：

  E[Mₙ₊₁ | ℱₙ] = Mₙ  (a.s.)

すなわち、時刻 n までの情報 ℱₙ を知っているとき、
次の時刻 n+1 の期待値は現在の値 Mₙ に等しい。

**Optional Stopping Theorem (OST)** は、マルチンゲールの最も重要な定理の一つであり、
停止時間でゲームを止めても「公平性」が保たれることを主張する：

  τ が有界停止時間ならば、E[M_τ] = E[M₀]

## このファイルの位置づけ

本ファイルは、以下の階層構造の**第 5 層（最終層）**である：

```
1. DecidableEvents.lean      ← 有限確率空間と decidable events
   ↓
2. DecidableAlgebra.lean     ← 有限代数（Boolean 演算で閉じた事象族）
   ↓
3. DecidableFiltration.lean  ← 離散版フィルトレーション（構造塔のインスタンス）
   ↓
4. ComputableStoppingTime    ← 停止時間の decidable 実装
   ↓
5. AlgorithmicMartingale     ← マルチンゲール理論と OST（今回）
```

## スコープの制限（重要）

このファイルは、**離散/有限の世界**に限定する：
- 有限標本空間（Fintype）のみ
- 確率は有理数 ℚ≥0 で表現
- 期待値は有限和として計算可能
- 時間軸は有限（time horizon）

これにより：
- すべての演算が実際に計算可能（#eval で実行可能）
- 完全な形式化が可能（sorry なしで証明可能）
- 教育的価値が高い（学部生でも理解可能）

mathlib の一般的な測度論（σ-代数、ルベーグ積分）とは独立である。

## 構造塔理論との接続

構造塔の重要な対応関係：

| 構造塔の概念        | 確率論の概念                     |
|---------------------|----------------------------------|
| StructureTower      | フィルトレーション (ℱₙ)ₙ≥₀       |
| layer n             | 時刻 n の可観測事象族 ℱₙ         |
| minLayer(A)         | 事象 A が初めて可観測になる時刻   |
| monotone            | 情報の単調増加 ℱₙ ⊆ ℱₙ₊₁         |
| 停止時間 τ          | minLayer({τ ≤ t}) ≤ t を満たす   |

この対応により、停止時間は構造塔の minLayer 関数を用いて特徴づけられる。

## 主な内容

1. **ProbabilityMassFunction**: 有限確率空間上の確率測度
2. **StochasticProcess**: 確率過程の定義
3. **Adaptedness**: 過程の ℱₙ-可測性
4. **ConditionalExpectation**: 条件付き期待値（有限和）
5. **Martingale**: マルチンゲールの定義
6. **Optional Stopping Theorem**: 有界停止時間版 OST

## 対象読者

- DecidableEvents, DecidableAlgebra, DecidableFiltration, ComputableStoppingTime を理解
- 学部 3-4 年生レベルの確率論（測度論は不要）
- Lean 4 の基本的な構文と BigOperators

## 参考文献

- Williams, D. *Probability with Martingales*. Cambridge, 1991.
- Durrett, R. *Probability: Theory and Examples*. Cambridge, 2019.
- Kallenberg, O. *Foundations of Modern Probability*. Springer, 2002.

-/

/-!
## Part 1: 確率測度（Probability Mass Function）

有限標本空間上の確率測度を、有理数値の関数として定義する。
-/

/--
確率質量関数（Probability Mass Function）

有限標本空間 Ω 上の確率測度を、各点 ω に確率 p(ω) ∈ ℚ≥0 を割り当てる関数として定義。
公理：∑_ω p(ω) = 1

### 設計方針

**なぜ有理数か？**
- 計算可能性：有理数演算は exact で #eval 可能
- 形式化の容易性：実数の完備性を避けられる
- 教育的価値：有限和の計算が明示的

**将来の拡張**
- 実数への埋め込み：ℚ≥0 → ℝ≥0 は自然
- 測度論への接続：有限測度の特殊ケース
-/
structure ProbabilityMassFunction (Ω : FiniteSampleSpace) where
  /-- 各標本点の確率値 -/
  prob : Ω.carrier → ℚ
  /-- 非負性：すべての確率が非負 -/
  nonneg : ∀ ω, 0 ≤ prob ω
  /-- 正規化条件：確率の総和が 1 -/
  sum_eq_one : (∑ ω : Ω.carrier, prob ω) = 1

namespace ProbabilityMassFunction

variable {Ω : FiniteSampleSpace}

/--
事象の確率

事象 A の確率は、A に属する点の確率の和：
  P(A) = ∑_{ω ∈ A} p(ω)
-/
def probEvent (p : ProbabilityMassFunction Ω) (A : Event Ω.carrier) : ℚ :=
  ∑ ω in Finset.univ.filter (fun ω => ω ∈ A), p.prob ω

notation:max p "[" A "]" => probEvent p A

/-- 事象の確率は非負 -/
theorem probEvent_nonneg (p : ProbabilityMassFunction Ω) (A : Event Ω.carrier) :
    0 ≤ p[A] := by
  sorry  -- 証明方針：各項が非負なので和も非負

/-- 全事象の確率は 1 -/
theorem probEvent_univ (p : ProbabilityMassFunction Ω) :
    p[Event.univ] = 1 := by
  unfold probEvent Event.univ
  -- すべての ω が Set.univ に属するので、filter の結果は Finset.univ そのもの
  have hfilter : Finset.univ.filter (fun ω => ω ∈ (Set.univ : Set Ω.carrier)) = Finset.univ := by
    ext ω
    simp
  simp [hfilter]
  exact p.sum_eq_one

/-- 空事象の確率は 0 -/
theorem probEvent_empty (p : ProbabilityMassFunction Ω) :
    p[Event.empty] = 0 := by
  sorry  -- 証明方針：空集合のフィルタは空なので和は 0

/--
一様分布（Uniform Distribution）

すべての点に等しい確率 1/|Ω| を割り当てる。
-/
def uniform (Ω : FiniteSampleSpace) [Nonempty Ω.carrier] :
    ProbabilityMassFunction Ω where
  prob := fun _ => 1 / (Fintype.card Ω.carrier : ℚ)
  nonneg := by
    intro ω
    apply div_nonneg
    · norm_num
    · have h := Fintype.card_pos (α := Ω.carrier)
      omega
  sum_eq_one := by
    sorry  -- 証明方針：n × (1/n) = 1

end ProbabilityMassFunction

/-!
## Part 2: 確率過程（Stochastic Process）

時間とともに変化する確率変数の系列。
-/

/--
確率過程（Stochastic Process）

離散時間確率過程は、各時刻 n ∈ ℕ と各標本点 ω ∈ Ω に対して、
値 Mₙ(ω) ∈ ℚ を割り当てる関数。

### 表現

`Process Ω := ℕ → Ω → ℚ`

すなわち：
- 時刻 n を固定すると、Mₙ : Ω → ℚ は確率変数
- 標本点 ω を固定すると、n ↦ Mₙ(ω) は軌道（path）
-/
abbrev StochasticProcess (Ω : FiniteSampleSpace) := ℕ → Ω.carrier → ℚ

namespace StochasticProcess

variable {Ω : FiniteSampleSpace}

/--
期待値（Expectation）

時刻 n での確率変数 Mₙ の期待値：
  E[Mₙ] = ∑_ω p(ω) · Mₙ(ω)
-/
def expectation (M : StochasticProcess Ω) (p : ProbabilityMassFunction Ω) (n : ℕ) : ℚ :=
  ∑ ω : Ω.carrier, p.prob ω * M n ω

notation:max "𝔼[" M "]" n => expectation M p n

/--
過程の ℱₙ-可測性（Adaptedness）

確率過程 M が フィルトレーション ℱ に適合（adapted）であるとは、
各時刻 n で、Mₙ が ℱₙ-可測であること。

### 離散版の定義

有限標本空間では、「Mₙ が ℱₙ-可測」とは：
  ∀ r ∈ ℚ, {ω | Mₙ(ω) = r} ∈ ℱₙ

すなわち、「Mₙ の値が r である」という事象が時刻 n で可観測。

### 教育的注釈

一般的な測度論では、「可測」とは「逆像が代数に属する」ことだが、
有限標本空間では値域も有限なので、上の定義で十分。
-/
def isAdapted (M : StochasticProcess Ω) (ℱ : DecidableFiltration Ω) : Prop :=
  ∀ n (hn : n ≤ ℱ.timeHorizon) (r : ℚ),
    {ω : Ω.carrier | M n ω = r} ∈ (ℱ.observableAt n hn).events

end StochasticProcess

/-!
## Part 3: 条件付き期待値（Conditional Expectation）

有限標本空間における条件付き期待値の定義。
-/

namespace ConditionalExpectation

variable {Ω : FiniteSampleSpace}

/--
条件付き期待値（離散版）

E[Mₙ₊₁ | ℱₙ] を計算するため、ℱₙ の各 atom（原子）上での条件付き確率を使用。

### 簡略版の定義

有限標本空間では、各 ω に対して：
  E[Mₙ₊₁ | ℱₙ](ω) = ∑_{ω' : ℱₙ(ω) = ℱₙ(ω')} p(ω' | ℱₙ(ω)) · Mₙ₊₁(ω')

ここで、ℱₙ(ω) = ℱₙ(ω') は「ω と ω' が時刻 n で区別できない」ことを意味。

### 注意

完全な形式化は複雑なので、ここでは存在のみを仮定し、
マルチンゲール条件は公理的に与える。

将来的には：
1. ℱₙ の atom を明示的に定義
2. 各 atom 上の条件付き確率を計算
3. 条件付き期待値を構成
-/

-- 完全な実装は将来の拡張として残す
-- ここでは型のみを定義
axiom conditionalExpectation :
  (M : StochasticProcess Ω) →
  (p : ProbabilityMassFunction Ω) →
  (ℱ : DecidableFiltration Ω) →
  (n : ℕ) → (hn : n < ℱ.timeHorizon) →
  Ω.carrier → ℚ

notation:max "𝔼[" M "|" ℱ "]" n => conditionalExpectation M p ℱ n

end ConditionalExpectation

/-!
## Part 4: マルチンゲール（Martingale）

「公平なゲーム」の数学的定式化。
-/

/--
マルチンゲール（Martingale）

確率過程 M が フィルトレーション ℱ に関するマルチンゲールであるとは：

1. **適合性**（Adaptedness）：各 Mₙ が ℱₙ-可測
2. **可積分性**（Integrability）：各 E[|Mₙ|] < ∞（有限標本空間では自動）
3. **マルチンゲール条件**：E[Mₙ₊₁ | ℱₙ] = Mₙ (a.s.)

### 離散版の簡略化

有限標本空間では、条件付き期待値の完全な実装を避け、
マルチンゲール条件を直接 axiom として与える。

すなわち、各時刻 n と各標本点 ω に対して：
  ∑_{ω' : 同じ atom} p(ω') · Mₙ₊₁(ω') = Mₙ(ω)

ここでは、この条件を「E[Mₙ₊₁ | ℱₙ] = Mₙ」と略記。

### 教育的注釈

**直感的理解**：
- 「次の値の期待値 = 現在の値」
- 「ゲームの期待値が変わらない」
- 「公平なゲーム」

**具体例**：
- 対称ランダムウォーク
- 賭けの累積収支（公平な賭け）
-/
structure Martingale (Ω : FiniteSampleSpace)
    (p : ProbabilityMassFunction Ω) (ℱ : DecidableFiltration Ω) where
  /-- 確率過程 -/
  process : StochasticProcess Ω
  /-- 適合性：過程が ℱ に適合 -/
  adapted : StochasticProcess.isAdapted process ℱ
  /--
  マルチンゲール条件：E[Mₙ₊₁ | ℱₙ] = Mₙ (a.s.)
  
  簡略版：各時刻で、条件付き期待値が現在の値に等しい
  -/
  martingale_property :
    ∀ n (hn : n < ℱ.timeHorizon) (ω : Ω.carrier),
      ConditionalExpectation.conditionalExpectation process p ℱ n hn ω = process n ω

namespace Martingale

variable {Ω : FiniteSampleSpace} {p : ProbabilityMassFunction Ω}
variable {ℱ : DecidableFiltration Ω}

/--
マルチンゲールの期待値は時間によらず一定

定理：M がマルチンゲールならば、E[Mₙ] = E[M₀] for all n
-/
theorem expectation_constant (M : Martingale Ω p ℱ) (n : ℕ) :
    StochasticProcess.expectation M.process p n = StochasticProcess.expectation M.process p 0 := by
  sorry
  -- 証明方針：
  -- 1. 帰納法で n について証明
  -- 2. E[Mₙ₊₁] = E[E[Mₙ₊₁ | ℱₙ]] = E[Mₙ] （条件付き期待値の性質）
  -- 3. マルチンゲール条件より E[Mₙ₊₁ | ℱₙ] = Mₙ
  -- 4. したがって E[Mₙ₊₁] = E[Mₙ]

end Martingale

/-!
## Part 5: Optional Stopping Theorem (OST)

マルチンゲール理論の核心定理。
-/

/--
停止された過程（Stopped Process）

停止時間 τ に対して、停止された過程 M^τ を：
  M^τ_n(ω) := M_{min(n, τ(ω))}(ω)

すなわち、「時刻 τ(ω) で値を固定」。
-/
def stoppedProcess {Ω : FiniteSampleSpace} {ℱ : DecidableFiltration Ω}
    (M : StochasticProcess Ω)
    (τ : ComputableStoppingTime ℱ) :
    StochasticProcess Ω :=
  fun n ω => M (min n (τ.time ω)) ω

/--
停止時間での過程の値

M_τ(ω) := M_{τ(ω)}(ω)
-/
def processAtStoppingTime {Ω : FiniteSampleSpace} {ℱ : DecidableFiltration Ω}
    (M : StochasticProcess Ω)
    (τ : ComputableStoppingTime ℱ) :
    Ω.carrier → ℚ :=
  fun ω => M (τ.time ω) ω

notation:max M "[" τ "]" => processAtStoppingTime M τ

/-!
### Optional Stopping Theorem の準備

**定理の主張**：

M がマルチンゲールで、τ が有界停止時間ならば：
  E[M_τ] = E[M₀]

すなわち、「適切な時刻で止めても期待値は変わらない」。

**条件**：
1. M はマルチンゲール
2. τ は停止時間
3. τ は有界：∃ N, ∀ ω, τ(ω) ≤ N

### 教育的注釈

**直感的理解**：
- 「公平なゲームは、いつ止めても公平」
- 「カジノは事前に決めた戦略で止めるプレイヤーに勝てない」
- ただし「無限時間」や「予知能力」は禁止（有界性が重要）

**反例（有界でない場合）**：
- 「最初に勝つまで続ける」戦略
- 「元を取るまで続ける」戦略
- これらは有界でないので OST が使えない
-/

/--
Optional Stopping Theorem（有界停止時間版）

**主定理**：
M が (Ω, p, ℱ) 上のマルチンゲールで、
τ が N で有界な停止時間ならば：

  E[M_τ] = E[M₀]

### 証明のアイデア

1. M^τ（停止された過程）もマルチンゲール
2. E[M^τ_N] = E[M^τ_0] = E[M₀]
3. τ が N で有界なので、M^τ_N = M_τ
4. したがって E[M_τ] = E[M₀]

### 重要性

この定理は：
- 賭博理論の基礎
- 金融工学の根幹
- 確率微分方程式の基本ツール
- 最適停止問題の出発点
-/
theorem optional_stopping_theorem
    {Ω : FiniteSampleSpace} {p : ProbabilityMassFunction Ω}
    {ℱ : DecidableFiltration Ω}
    (M : Martingale Ω p ℱ)
    (τ : ComputableStoppingTime ℱ)
    (N : ℕ)
    (hN : N ≤ ℱ.timeHorizon)
    (hbounded : ComputableStoppingTime.isBounded τ N) :
    (∑ ω : Ω.carrier, p.prob ω * M.process (τ.time ω) ω) =
    StochasticProcess.expectation M.process p 0 := by
  sorry
  -- 証明方針：
  -- 
  -- Step 1: 停止された過程 M^τ を定義
  --   M^τ_n(ω) = M_{min(n, τ(ω))}(ω)
  -- 
  -- Step 2: M^τ もマルチンゲールであることを示す
  --   - 適合性：min(n, τ) は ℱ_n-可測
  --   - マルチンゲール条件：
  --     E[M^τ_{n+1} | ℱ_n] = E[M_{min(n+1, τ)} | ℱ_n]
  --                        = E[M_{min(n, τ)} | ℱ_n] + E[1_{τ > n} · (M_{n+1} - M_n) | ℱ_n]
  --                        = M^τ_n + 1_{τ > n} · 0  (マルチンゲール条件)
  --                        = M^τ_n
  -- 
  -- Step 3: マルチンゲールの期待値は時間によらず一定
  --   E[M^τ_N] = E[M^τ_0] = E[M_0]
  -- 
  -- Step 4: τ が N で有界なので
  --   M^τ_N(ω) = M_{min(N, τ(ω))}(ω) = M_{τ(ω)}(ω)  (∵ τ(ω) ≤ N)
  -- 
  -- Step 5: したがって
  --   E[M_τ] = E[M^τ_N] = E[M_0]

/-!
## Part 6: 具体例

実際に計算可能な例を示す。
-/

section Examples

/-!
### 例 1：対称ランダムウォーク

コイン投げの系列で、表なら +1、裏なら -1 移動する。
これはマルチンゲールの典型例。
-/

/-- 2回のコイン投げの標本空間 -/
def twoCoins : FiniteSampleSpace where
  carrier := Bool × Bool
  fintype := inferInstance
  decidableEq := inferInstance

/-- 一様分布（各結果の確率 = 1/4） -/
noncomputable def uniformTwoCoins : ProbabilityMassFunction twoCoins :=
  ProbabilityMassFunction.uniform twoCoins

/--
対称ランダムウォーク

- 時刻 0：初期値 0
- 時刻 1：第1回の結果に応じて +1 or -1
- 時刻 2：第2回の結果を加えて ±2, 0
-/
def symmetricRandomWalk : StochasticProcess twoCoins :=
  fun n ω =>
    match n with
    | 0 => 0  -- 初期値
    | 1 =>    -- 第1回の結果
        match ω.1 with
        | true => 1    -- 表なら +1
        | false => -1  -- 裏なら -1
    | _ =>    -- 第2回の結果を加算
        match ω.1, ω.2 with
        | true, true => 2     -- 表・表：+1+1
        | true, false => 0    -- 表・裏：+1-1
        | false, true => 0    -- 裏・表：-1+1
        | false, false => -2  -- 裏・裏：-1-1

/-- 初期値の期待値は 0 -/
example : StochasticProcess.expectation symmetricRandomWalk uniformTwoCoins 0 = 0 := by
  unfold StochasticProcess.expectation symmetricRandomWalk uniformTwoCoins
  sorry

/--
時刻 1 の期待値も 0（マルチンゲール性の検証）
-/
example : StochasticProcess.expectation symmetricRandomWalk uniformTwoCoins 1 = 0 := by
  sorry
  -- 証明方針：
  -- E[M₁] = (1/4)(1 + 1 + (-1) + (-1)) = 0

/--
時刻 2 の期待値も 0
-/
example : StochasticProcess.expectation symmetricRandomWalk uniformTwoCoins 2 = 0 := by
  sorry
  -- 証明方針：
  -- E[M₂] = (1/4)(2 + 0 + 0 + (-2)) = 0

/-!
### 例 2：停止時間での Optional Stopping

「初めて値が非負になる時刻」で止める戦略。

標本空間：(false, false) → 裏・裏 → 値は常に負 → 時刻 2 で強制終了
-/

-- これらの例の完全な実装は将来の拡張として残す
-- ここでは型と構造のみを示す

end Examples

/-!
## Part 7: まとめと今後の展望

### 本ファイルで達成したこと

1. **確率測度の定義**
   - 有限標本空間上の ProbabilityMassFunction
   - 有理数による計算可能な確率

2. **確率過程の定義**
   - StochasticProcess as ℕ → Ω → ℚ
   - 適合性（Adaptedness）

3. **マルチンゲールの定義**
   - 公理的な定式化
   - E[Mₙ₊₁ | ℱₙ] = Mₙ

4. **Optional Stopping Theorem**
   - 有界停止時間版の主張
   - 証明の方針

### 構造塔理論との統合

本ファイルにより、構造塔理論と確率論の接続が完成した：

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
   - 条件付き期待値の性質の証明

2. **OST の完全な証明**
   - 停止された過程のマルチンゲール性
   - 各ステップの詳細な証明
   - 有界性の必要性の反例

3. **他のマルチンゲール定理**
   - Doob の不等式
   - Martingale Convergence Theorem（離散版）
   - Azuma-Hoeffding の不等式

4. **応用**
   - 最適停止問題
   - 賭博理論
   - ランダムウォークの詳細解析

5. **実数への拡張**
   - ℚ → ℝ への埋め込み
   - 測度論への接続

6. **計算可能性の追求**
   - すべての定義を #eval 可能にする
   - 具体的な数値例の充実
   - 視覚化・シミュレーション

### 教育的価値

このファイルは以下を示している：

- **有限性の力**：制約により本質が明確になる
- **構造塔の有用性**：異なる分野の統一的理解
- **形式化の意義**：曖昧さのない数学の構築
- **計算可能性**：理論と実践の橋渡し

### 学習の指針

本ファイルを理解するための推奨順序：

1. DecidableEvents.lean から順に積み上げる
2. 各概念を具体例で確認
3. #eval で実際に計算してみる
4. sorry の証明を埋めてみる
5. 新しい例を自分で構成してみる

### 参考資料

- CAT2_complete.lean：構造塔の完全な形式化
- DecidableFiltration.lean：フィルトレーションの実装
- Williams の教科書：マルチンゲール理論の入門書

-/

/-!
## 演習問題（Exercises）

### 基礎問題

1. **一様分布の検証**
   - uniform の sum_eq_one を証明せよ
   - |Ω| = 6（サイコロ）の場合を具体的に計算

2. **事象の確率**
   - probEvent_empty の証明を完成させよ
   - probEvent_nonneg の証明を完成させよ

3. **期待値の計算**
   - 対称ランダムウォークの各時刻の期待値を計算
   - #eval で確認

### 応用問題

4. **マルチンゲールの検証**
   - 対称ランダムウォークがマルチンゲールであることを示せ
   - 各時刻で E[Mₙ₊₁ | ℱₙ] = Mₙ を確認

5. **停止時間の構成**
   - 「初めて正の値になる時刻」を停止時間として定義
   - 停止時間条件を満たすことを証明

6. **OST の適用**
   - 対称ランダムウォークに OST を適用
   - E[M_τ] = E[M₀] = 0 を確認

### 発展問題

7. **条件付き期待値の実装**
   - ℱₙ の atom を明示的に定義せよ
   - 条件付き期待値を実装せよ

8. **非対称ランダムウォーク**
   - p ≠ 1/2 のランダムウォークを定義
   - これはマルチンゲールか？

9. **Doob 分解**
   - 任意の適合過程をマルチンゲール + 予測可能過程に分解

10. **最適停止問題**
    - 「最大値を得るような停止時間」を求める問題を形式化
    - 離散版の解法を実装

-/
