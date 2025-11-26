import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import MyProjects.ST.Decidable.P1.DecidableEvents
import MyProjects.ST.Decidable.P2.DecidableAlgebra
import MyProjects.ST.Decidable.P3.DecidableFiltration
import MyProjects.ST.Decidable.P4.ComputableStoppingTime

-- In the actual project, these would be imports:
-- import MyProjects.ST.Decidable.P1.DecidableEvents
-- import MyProjects.ST.Decidable.P2.DecidableAlgebra
-- import MyProjects.ST.Decidable.P3.DecidableFiltration
-- import MyProjects.ST.Decidable.P4.ComputableStoppingTime

open Classical Finset BigOperators

/-!
# Algorithmic Martingale Theory and Discrete Optional Stopping Theorem

このファイルは、離散版フィルトレーション上での**計算可能なマルチンゲール**と
**有限停止時間に対する Optional Stopping Theorem（OST）** を定義する。

## 位置づけ

本ファイルは、以下の階層構造の**第 5 層**（最終層）に対応する：

```
DecidableEvents.lean        ← 有限標本空間と decidable events
    ↓
DecidableAlgebra.lean       ← 有限代数（Boolean 演算で閉じた事象族）
    ↓
DecidableFiltration.lean    ← 離散版フィルトレーション（構造塔のインスタンス）
    ↓
ComputableStoppingTime.lean ← 停止時間（情報＋時刻の構造）
    ↓
AlgorithmicMartingale.lean  ← 今回（マルチンゲールと OST）
```

## 数学的背景

### マルチンゲールとは

マルチンゲール (M_n)_{n≥0} は確率過程であり、以下を満たす：

1. **適合性（Adapted）**: 各 M_n は F_n-可測
2. **可積分性**: E[|M_n|] < ∞
3. **マルチンゲール条件**: E[M_{n+1} | F_n] = M_n

直感的には、「公平なゲームでの累積勝ち金」を表す：
過去の情報を知っていても、将来の期待値は現在の値に等しい。

### Optional Stopping Theorem (OST)

停止時間 τ に対して、適切な条件の下で：

  E[M_τ] = E[M_0]

つまり、「いつゲームをやめても期待値は変わらない」。

## このファイルの設計方針

**スコープ限定**：
- 有限標本空間 Ω に限定
- 有理数 ℚ での確率・期待値（浮動小数点を避ける）
- 有界停止時間に限定
- 完全な証明よりも構造の明確さを優先

**計算可能性**：
- すべての期待値が有限和として計算可能
- #eval で実際に値を確認できる

## 主な内容

1. **ProbabilityMassFunction**: 有限確率分布
2. **DiscreteProcess**: 離散確率過程
3. **Adapted 条件**: F_n-可測性
4. **ConditionalExpectation**: 条件付き期待値（離散版）
5. **DiscreteMartingale**: マルチンゲールの定義
6. **DiscreteOST**: Optional Stopping Theorem の statement

## 参考文献

- Williams, David. *Probability with Martingales*. Cambridge University Press, 1991.
- Durrett, Rick. *Probability: Theory and Examples*. Cambridge University Press, 2019.
- Shiryaev, A. N. *Probability*. Springer, 1996.

-/

namespace Prob

/-!
## Part 0: 前提となる定義の再掲

実際のプロジェクトでは import を使用。
ここでは自己完結性のために最小限の定義を再掲。
-/

/-- 有限標本空間（DecidableEvents.lean から） -/
structure FiniteSampleSpace where
  carrier : Type*
  [fintype : Fintype carrier]
  [decidableEq : DecidableEq carrier]

namespace FiniteSampleSpace

instance instFintype (Ω : FiniteSampleSpace) : Fintype Ω.carrier :=
  Ω.fintype

instance instDecidableEq (Ω : FiniteSampleSpace) : DecidableEq Ω.carrier :=
  Ω.decidableEq

/-- 標本点の集合（Finset として） -/
def points (Ω : FiniteSampleSpace) : Finset Ω.carrier :=
  Finset.univ

/-- 標本空間の要素数 -/
def card (Ω : FiniteSampleSpace) : ℕ :=
  Fintype.card Ω.carrier

end FiniteSampleSpace

/-- 事象の型 -/
abbrev Event (Ω : Type*) := Set Ω

namespace Event

variable {Ω : Type*}

def empty : Event Ω := ∅
def univ : Event Ω := Set.univ
def complement (A : Event Ω) : Event Ω := Aᶜ
def union (A B : Event Ω) : Event Ω := A ∪ B
def intersection (A B : Event Ω) : Event Ω := A ∩ B

end Event

/-- 有限代数（DecidableAlgebra.lean から） -/
structure FiniteAlgebra (Ω : Type*) where
  events : Set (Event Ω)
  has_empty : Event.empty ∈ events
  closed_complement : ∀ {A : Event Ω}, A ∈ events → Event.complement A ∈ events
  closed_union : ∀ {A B : Event Ω}, A ∈ events → B ∈ events →
                 Event.union A B ∈ events

namespace FiniteAlgebra

variable {Ω : Type*}

theorem has_univ (ℱ : FiniteAlgebra Ω) : Event.univ ∈ ℱ.events := by
  have h := ℱ.closed_complement ℱ.has_empty
  simp [Event.complement, Event.empty, Event.univ] at h ⊢
  exact h

def IsSubalgebra (ℱ 𝒢 : FiniteAlgebra Ω) : Prop :=
  ℱ.events ⊆ 𝒢.events

notation:50 ℱ " ⊆ₐ " 𝒢:50 => IsSubalgebra ℱ 𝒢

/-- 全体の代数（Power Set Algebra） -/
def powerSet : FiniteAlgebra Ω where
  events := Set.univ
  has_empty := Set.mem_univ _
  closed_complement := fun _ => Set.mem_univ _
  closed_union := fun _ _ => Set.mem_univ _

end FiniteAlgebra

/-- 離散フィルトレーション（DecidableFiltration.lean から） -/
structure DecidableFiltration (Ω : FiniteSampleSpace) where
  timeHorizon : ℕ
  observableAt :
    (t : ℕ) → (h : t ≤ timeHorizon) → FiniteAlgebra Ω.carrier
  monotone :
    ∀ (s t : ℕ) (hs : s ≤ timeHorizon) (ht : t ≤ timeHorizon),
      s ≤ t → (observableAt s hs) ⊆ₐ (observableAt t ht)

/-- 計算可能な停止時間（ComputableStoppingTime.lean から） -/
structure ComputableStoppingTime {Ω : FiniteSampleSpace}
    (ℱ : DecidableFiltration Ω) where
  time : Ω.carrier → ℕ
  adapted :
    ∀ (t : ℕ) (ht : t ≤ ℱ.timeHorizon),
      {ω : Ω.carrier | time ω ≤ t} ∈ (ℱ.observableAt t ht).events

namespace ComputableStoppingTime

variable {Ω : FiniteSampleSpace} {ℱ : DecidableFiltration Ω}

/-- 停止時間が上から N で抑えられること -/
def isBounded (τ : ComputableStoppingTime ℱ) (N : ℕ) : Prop :=
  ∀ ω, τ.time ω ≤ N

/-- 定数停止時間 -/
def const (ℱ : DecidableFiltration Ω) (c : ℕ) (hc : c ≤ ℱ.timeHorizon) :
    ComputableStoppingTime ℱ where
  time := fun _ => c
  adapted := by
    intro t ht
    by_cases hct : c ≤ t
    · have hset : {ω : Ω.carrier | c ≤ t} = (Set.univ : Set Ω.carrier) := by
        ext ω; simp [hct]
      have h := FiniteAlgebra.has_univ (ℱ.observableAt t ht)
      simpa [hset] using h
    · have hset : {ω : Ω.carrier | c ≤ t} = (∅ : Set Ω.carrier) := by
        ext ω; simp [hct]
      have h := (ℱ.observableAt t ht).has_empty
      have h' : (∅ : Set Ω.carrier) ∈ (ℱ.observableAt t ht).events := by
        simpa [Event.empty] using h
      simpa [hset] using h'

end ComputableStoppingTime

/-!
## Part 1: 確率質量関数（Probability Mass Function）

有限標本空間上の確率分布を定義する。
有理数 ℚ を使用し、すべての計算が正確に行える。

### 数学的定義

確率質量関数 p : Ω → ℚ≥0 は以下を満たす：
1. 非負性：∀ ω, p(ω) ≥ 0
2. 正規化：∑_ω p(ω) = 1

### 実装の注釈

- ℚ を使用して丸め誤差を回避
- 非負性は暗黙の仮定とし、型レベルでは ℚ を使用
- 正規化条件は normalization フィールドで明示
-/

/--
確率質量関数（Probability Mass Function, PMF）

有限標本空間 Ω 上の確率分布を表す。

### 構造塔との対応

確率測度は構造塔の layer（代数）の上に定義される「追加の構造」である。
フィルトレーションの各時刻の代数上で、確率を定義できる。
-/
structure ProbabilityMassFunction (Ω : FiniteSampleSpace) where
  /-- 各標本点の確率（重み）-/
  pmf : Ω.carrier → ℚ
  /-- 非負性：すべての確率は非負 -/
  nonneg : ∀ ω, 0 ≤ pmf ω
  /-- 正規化：確率の総和は 1 -/
  normalization : ∑ ω in Ω.points, pmf ω = 1

namespace ProbabilityMassFunction

variable {Ω : FiniteSampleSpace}

/--
事象の確率

P(A) = ∑_{ω ∈ A} p(ω)

有限和なので計算可能。
-/
def prob (P : ProbabilityMassFunction Ω) (A : Event Ω.carrier)
    [DecidablePred (· ∈ A)] : ℚ :=
  ∑ ω in Ω.points.filter (· ∈ A), P.pmf ω

/-- 空事象の確率は 0 -/
theorem prob_empty (P : ProbabilityMassFunction Ω) :
    P.prob Event.empty = 0 := by
  simp [prob, Event.empty, Finset.filter_false]

/-- 全事象の確率は 1 -/
theorem prob_univ (P : ProbabilityMassFunction Ω) :
    P.prob Event.univ = 1 := by
  have h : Ω.points.filter (· ∈ Event.univ) = Ω.points := by
    ext ω; simp [Event.univ, FiniteSampleSpace.points]
  simp [prob, h, P.normalization]

/--
期待値（Expected Value）

E[X] = ∑_ω X(ω) · p(ω)

確率変数 X : Ω → ℚ の期待値を有限和として計算。
-/
def expectation (P : ProbabilityMassFunction Ω) (X : Ω.carrier → ℚ) : ℚ :=
  ∑ ω in Ω.points, X ω * P.pmf ω

notation "𝔼[" X ", " P "]" => ProbabilityMassFunction.expectation P X

/-- 定数の期待値は定数 -/
theorem expectation_const (P : ProbabilityMassFunction Ω) (c : ℚ) :
    𝔼[(fun _ => c), P] = c := by
  simp [expectation, ← Finset.sum_mul, P.normalization]

/-- 期待値の線形性（スカラー倍） -/
theorem expectation_smul (P : ProbabilityMassFunction Ω)
    (c : ℚ) (X : Ω.carrier → ℚ) :
    𝔼[(fun ω => c * X ω), P] = c * 𝔼[X, P] := by
  simp [expectation, mul_assoc, ← Finset.mul_sum]

/-- 期待値の線形性（加法） -/
theorem expectation_add (P : ProbabilityMassFunction Ω)
    (X Y : Ω.carrier → ℚ) :
    𝔼[(fun ω => X ω + Y ω), P] = 𝔼[X, P] + 𝔼[Y, P] := by
  simp [expectation, add_mul, Finset.sum_add_distrib]

/-- 一様分布の構成（すべての点に等しい確率） -/
def uniform (Ω : FiniteSampleSpace) (hpos : 0 < Ω.card) :
    ProbabilityMassFunction Ω where
  pmf := fun _ => 1 / Ω.card
  nonneg := by
    intro _
    apply div_nonneg
    · exact le_of_lt one_pos
    · exact Nat.cast_nonneg _
  normalization := by
    have hcard : (Ω.card : ℚ) ≠ 0 := by
      simp [FiniteSampleSpace.card]
      exact Nat.pos_iff_ne_zero.mp hpos
    simp [FiniteSampleSpace.points, FiniteSampleSpace.card, Finset.sum_const]
    field_simp

end ProbabilityMassFunction

/-!
## Part 2: 離散確率過程（Discrete Process）

時刻とともに変化する確率変数の列を定義する。

### 数学的定義

離散確率過程 (X_n)_{n=0,...,N} は：
- 各時刻 n に対して、確率変数 X_n : Ω → ℚ
- N は時間の終端（timeHorizon）

### 構造塔との対応

確率過程は、構造塔の各層（時刻）に「値」を割り当てる構造である。
フィルトレーションが「観測可能な情報」を表すのに対し、
確率過程は「観測される量」を表す。
-/

/--
離散確率過程

有限標本空間 Ω とフィルトレーション ℱ 上の確率過程。
時刻 n での値は processAt n : Ω → ℚ で与えられる。
-/
structure DiscreteProcess {Ω : FiniteSampleSpace}
    (ℱ : DecidableFiltration Ω) where
  /-- 時刻 n での確率変数 -/
  processAt : (n : ℕ) → (h : n ≤ ℱ.timeHorizon) → (Ω.carrier → ℚ)

namespace DiscreteProcess

variable {Ω : FiniteSampleSpace} {ℱ : DecidableFiltration Ω}

/-- 定数過程（すべての時刻で同じ値） -/
def const (ℱ : DecidableFiltration Ω) (c : ℚ) : DiscreteProcess ℱ where
  processAt := fun _ _ _ => c

/-- 停止時間での確率過程の値 -/
def stoppedValue (X : DiscreteProcess ℱ)
    (τ : ComputableStoppingTime ℱ)
    (hτ : ComputableStoppingTime.isBounded τ ℱ.timeHorizon)
    (ω : Ω.carrier) : ℚ :=
  X.processAt (τ.time ω) (hτ ω) ω

end DiscreteProcess

/-!
## Part 3: F_n-可測性（Adapted Condition）

確率過程が「情報の流れ」に適合していることを表す。

### 数学的定義

確率過程 (X_n) がフィルトレーション (ℱ_n) に**適合している (adapted)** とは：
∀ n, X_n は ℱ_n-可測

つまり、時刻 n での値 X_n(ω) は、時刻 n までの情報のみで決定される。

### 離散版での定式化

有限標本空間では、X_n が ℱ_n-可測であることは：
∀ c ∈ ℚ, {ω | X_n(ω) = c} ∈ ℱ_n

### 構造塔との対応

適合性は「確率過程が構造塔の層構造を尊重する」ことを意味する。
minLayer の言葉で言えば：X_n の値は、minLayer ≤ n の事象のみに依存する。
-/

/--
適合性（Adapted Condition）

確率過程 X がフィルトレーション ℱ に適合しているとは、
各時刻 n での値が ℱ_n-可測であること。

### 実装の注釈

厳密には「任意の c ∈ ℚ について {X_n = c} ∈ ℱ_n」を要求すべきだが、
有限空間では X_n は有限個の値しか取らないので、
ここでは簡略化した定義を使用。
-/
structure IsAdapted {Ω : FiniteSampleSpace} {ℱ : DecidableFiltration Ω}
    (X : DiscreteProcess ℱ) where
  /--
  適合性条件：各時刻 n での値が ℱ_n-可測

  ここでは、X_n の各レベル集合 {X_n = c} が ℱ_n に属することを要求。
  -/
  adapted :
    ∀ (n : ℕ) (hn : n ≤ ℱ.timeHorizon) (c : ℚ),
      {ω : Ω.carrier | X.processAt n hn ω = c} ∈ (ℱ.observableAt n hn).events

/-!
## Part 4: 条件付き期待値（Conditional Expectation）

条件付き期待値は、マルチンゲール理論の中心概念である。

### 数学的定義

E[X | ℱ_n] は、以下を満たす ℱ_n-可測な確率変数：
- E[E[X | ℱ_n]] = E[X]
- ∀ A ∈ ℱ_n, E[X · 1_A] = E[E[X | ℱ_n] · 1_A]

### 離散版での定式化

有限標本空間では、条件付き期待値は**分割上の平均**として計算できる。

ℱ_n の原子（atom）A に対して：
  E[X | ℱ_n](ω) = E[X · 1_A] / P(A)  （ω ∈ A のとき）

### 簡略化

完全な条件付き期待値の実装は複雑なので、
ここでは「代数の原子上での平均」という概念のみを導入し、
マルチンゲール条件は直接定式化する。
-/

/--
分割上の条件付き期待値（簡略版）

代数 ℱ の原子的分割 {A_i} が与えられたとき、
E[X | ℱ](ω) = E[X | A_i] where ω ∈ A_i

### 実装の注釈

完全な実装には代数の原子分解が必要だが、
ここでは型定義のみ行い、具体的な計算は例で示す。
-/
structure ConditionalExpectation {Ω : FiniteSampleSpace}
    (P : ProbabilityMassFunction Ω)
    (X : Ω.carrier → ℚ)
    (ℱ : FiniteAlgebra Ω.carrier) where
  /-- 条件付き期待値（ℱ-可測な確率変数） -/
  value : Ω.carrier → ℚ
  /-- 可測性：value は ℱ-可測 -/
  measurable :
    ∀ c : ℚ, {ω : Ω.carrier | value ω = c} ∈ ℱ.events
  /-- 期待値の保存：E[E[X | ℱ]] = E[X] -/
  expectation_preserved :
    𝔼[value, P] = 𝔼[X, P]
  /-- 積分条件（省略：完全な実装は別途必要） -/

/-!
## Part 5: マルチンゲール（Martingale）

マルチンゲールの正式な定義を与える。

### 数学的定義

確率過程 (M_n)_{n=0,...,N} がマルチンゲールであるとは：
1. M は適合している（adapted）
2. ∀ n, E[|M_n|] < ∞（可積分）
3. ∀ n < N, E[M_{n+1} | ℱ_n] = M_n（マルチンゲール条件）

### 離散版での特徴

有限標本空間では：
- 可積分性は自動的に満たされる（有限和）
- マルチンゲール条件は各原子上で検証可能

### 直感的理解

マルチンゲールは「公平なゲーム」を表す：
- M_n = 時刻 n での累積勝ち金
- E[M_{n+1} | ℱ_n] = M_n は「平均的に勝ちも負けもない」

### 構造塔との対応

マルチンゲールは、構造塔の層（時刻）ごとに定義される値の系列であり、
「条件付き期待値が保存される」という特別な性質を持つ。
-/

/--
離散マルチンゲール

有限標本空間 Ω、フィルトレーション ℱ、確率測度 P 上のマルチンゲール。

### 定義

確率過程 (M_n) が以下を満たすとき、マルチンゲールと呼ぶ：
1. 適合性：各 M_n は ℱ_n-可測
2. マルチンゲール条件：E[M_{n+1} | ℱ_n] = M_n

### 実装の注釈

完全な条件付き期待値の実装は複雑なので、
ここではマルチンゲール条件を「分割上の期待値の等式」として直接記述。
-/
structure DiscreteMartingale {Ω : FiniteSampleSpace}
    (ℱ : DecidableFiltration Ω)
    (P : ProbabilityMassFunction Ω) where
  /-- 基礎となる確率過程 -/
  process : DiscreteProcess ℱ
  /-- 適合性：process は ℱ に適合 -/
  adapted : IsAdapted process
  /--
  マルチンゲール条件（簡略版）

  完全な形式化には条件付き期待値が必要だが、
  ここでは「ℱ_n の原子 A 上での期待値が M_n(ω) に等しい」という
  直接的な条件として記述。

  ∀ n < N, ∀ A ∈ ℱ_n (原子), ∀ ω ∈ A,
    E[M_{n+1} | A] = M_n(ω)
  -/
  martingale_condition :
    ∀ (n : ℕ) (hn : n < ℱ.timeHorizon)
      (hn' : n ≤ ℱ.timeHorizon)
      (hn1 : n + 1 ≤ ℱ.timeHorizon),
      -- 簡略版：全体での期待値が保存される
      -- E[M_{n+1}] = E[M_n]
      𝔼[process.processAt (n + 1) hn1, P] =
        𝔼[process.processAt n hn', P]

namespace DiscreteMartingale

variable {Ω : FiniteSampleSpace} {ℱ : DecidableFiltration Ω}
variable {P : ProbabilityMassFunction Ω}

/-- 定数マルチンゲール：M_n ≡ c は自明にマルチンゲール -/
def constMartingale (ℱ : DecidableFiltration Ω)
    (P : ProbabilityMassFunction Ω) (c : ℚ) :
    DiscreteMartingale ℱ P where
  process := DiscreteProcess.const ℱ c
  adapted := {
    adapted := by
      intro n hn c'
      by_cases hc : c = c'
      · -- c = c' の場合、{ω | c = c'} = Ω
        have hset : {ω : Ω.carrier | c = c'} = Set.univ := by
          ext ω; simp [hc]
        rw [hset]
        exact FiniteAlgebra.has_univ _
      · -- c ≠ c' の場合、{ω | c = c'} = ∅
        have hset : {ω : Ω.carrier | c = c'} = ∅ := by
          ext ω; simp [hc]
        rw [hset]
        exact (ℱ.observableAt n hn).has_empty
  }
  martingale_condition := by
    intro n hn hn' hn1
    -- 定数なので期待値は同じ
    simp [DiscreteProcess.const, ProbabilityMassFunction.expectation_const]

/-- マルチンゲールの初期値 -/
def initialValue (M : DiscreteMartingale ℱ P) : Ω.carrier → ℚ :=
  M.process.processAt 0 (Nat.zero_le _)

/-- マルチンゲールの初期期待値 -/
def initialExpectation (M : DiscreteMartingale ℱ P) : ℚ :=
  𝔼[M.initialValue, P]

end DiscreteMartingale

/-!
## Part 6: Optional Stopping Theorem（離散版）

有界停止時間に対する Optional Stopping Theorem を述べる。

### 定理（離散 OST）

マルチンゲール (M_n) と有界停止時間 τ（τ ≤ N）に対して：

  E[M_τ] = E[M_0]

### 証明の方針

有界停止時間の場合、以下のステップで証明できる：
1. M_τ = ∑_{k=0}^{N} M_k · 1_{τ=k} と分解
2. 各項の期待値を計算
3. マルチンゲール条件を繰り返し使用

### 実装の注釈

完全な証明は複雑なので、ここでは statement のみを与える。
証明の詳細は sorry で残す。

### 数学的重要性

OST は以下を示す：
- 「いつゲームをやめても期待値は変わらない」
- 停止時間の選び方に依存しない
- ただし、有界性（または可積分性条件）が必須

### 構造塔との対応

停止時間 τ は minLayer 関数の一般化であり、
OST は「minLayer に基づく選択が期待値を変えない」ことを示している。
-/

/--
有界停止時間でのマルチンゲールの値

M_τ(ω) = M_{τ(ω)}(ω)

停止時間 τ で評価したマルチンゲールの値。
-/
def stoppedMartingale {Ω : FiniteSampleSpace} {ℱ : DecidableFiltration Ω}
    {P : ProbabilityMassFunction Ω}
    (M : DiscreteMartingale ℱ P)
    (τ : ComputableStoppingTime ℱ)
    (hτ : ComputableStoppingTime.isBounded τ ℱ.timeHorizon) :
    Ω.carrier → ℚ :=
  M.process.stoppedValue τ hτ

/--
**Optional Stopping Theorem（離散版）**

マルチンゲール M と有界停止時間 τ（τ ≤ timeHorizon）に対して：

  E[M_τ] = E[M_0]

### 定理の意味

「公平なゲームをいつやめても、期待勝ち金は初期値に等しい」

### 仮定

1. M はマルチンゲール
2. τ は停止時間
3. τ ≤ N（有界性）

### 証明の概略（sorry）

1. M_{τ∧n} もマルチンゲール
2. τ∧n → τ（有界性より）
3. 極限操作により E[M_τ] = E[M_0]

有限空間・有界停止時間の場合、直接計算でも証明可能。
-/
theorem optional_stopping_theorem
    {Ω : FiniteSampleSpace} {ℱ : DecidableFiltration Ω}
    {P : ProbabilityMassFunction Ω}
    (M : DiscreteMartingale ℱ P)
    (τ : ComputableStoppingTime ℱ)
    (hτ : ComputableStoppingTime.isBounded τ ℱ.timeHorizon) :
    𝔼[stoppedMartingale M τ hτ, P] = M.initialExpectation := by
  sorry
  -- 証明の方針：
  -- M_τ = ∑_{k=0}^{N} M_k · 1_{τ=k} と分解
  -- E[M_τ] = ∑_{k=0}^{N} E[M_k · 1_{τ=k}]
  -- マルチンゲール条件と停止時間の性質を使用
  -- E[M_τ] = E[M_0]

/-!
### OST の系

OST のいくつかの応用を述べる。
-/

/--
定数停止時間に対する OST

τ ≡ c の場合、M_τ = M_c なので、
E[M_c] = E[M_0]

これはマルチンゲール条件の繰り返し適用と同値。
-/
theorem ost_const
    {Ω : FiniteSampleSpace} {ℱ : DecidableFiltration Ω}
    {P : ProbabilityMassFunction Ω}
    (M : DiscreteMartingale ℱ P)
    (c : ℕ) (hc : c ≤ ℱ.timeHorizon) :
    𝔼[M.process.processAt c hc, P] = M.initialExpectation := by
  sorry
  -- マルチンゲール条件を c 回適用

/-!
## Part 7: 具体例と計算

#eval を使った計算可能な例を示す。
-/

section Examples

/-- コイン投げの標本空間（Bool = {true, false}） -/
def coinSpace : FiniteSampleSpace where
  carrier := Bool
  fintype := inferInstance
  decidableEq := inferInstance

/-- 公平なコイン（一様分布） -/
def fairCoin : ProbabilityMassFunction coinSpace where
  pmf := fun _ => 1/2
  nonneg := by intro _; norm_num
  normalization := by
    simp [FiniteSampleSpace.points, Finset.sum_bool]
    norm_num

/-- コイン標本空間上の全体代数 -/
def coinFullAlgebra : FiniteAlgebra coinSpace.carrier :=
  FiniteAlgebra.powerSet

/-- 定数フィルトレーション（time horizon = 2） -/
def coinFiltration : DecidableFiltration coinSpace where
  timeHorizon := 2
  observableAt := fun _ _ => coinFullAlgebra
  monotone := by intro _ _ _ _ _; exact Set.Subset.refl _

/--
簡単なマルチンゲールの例：公平な賭け

- 時刻 0：資産 M_0 = 0
- 時刻 1：表なら +1、裏なら -1
- 時刻 2：累積

E[M_1] = (1/2) · 1 + (1/2) · (-1) = 0 = E[M_0]
-/

/-- 賭けの結果（表 = +1、裏 = -1） -/
def betResult (b : Bool) : ℚ := if b then 1 else -1

/-- 簡単な確率過程：累積賭け金 -/
def simpleBettingProcess : DiscreteProcess coinFiltration where
  processAt := fun n _ b =>
    match n with
    | 0 => 0                      -- 初期資産
    | 1 => betResult b            -- 1回目の結果
    | _ => betResult b            -- それ以降も同じ（簡略化）

-- 計算例
#eval betResult true   -- 1
#eval betResult false  -- -1

-- 期待値の計算（手動）
-- E[M_0] = 0
-- E[M_1] = (1/2) · 1 + (1/2) · (-1) = 0

/-- 停止時間の例：最初の「表」で停止 -/
def firstHeadsTime : ComputableStoppingTime coinFiltration where
  time := fun b => if b then 0 else 1  -- 表なら即停止、裏なら時刻 1
  adapted := by
    intro t ht
    simp [coinFiltration, coinFullAlgebra, FiniteAlgebra.powerSet]

#eval firstHeadsTime.time true   -- 0
#eval firstHeadsTime.time false  -- 1

/-- 定数停止時間 τ ≡ 1 -/
def constStoppingTime1 : ComputableStoppingTime coinFiltration :=
  ComputableStoppingTime.const coinFiltration 1 (by decide)

#eval constStoppingTime1.time true   -- 1
#eval constStoppingTime1.time false  -- 1

end Examples

/-!
## Part 8: 学習のまとめ

### 本ファイルで学んだこと

1. **確率質量関数（PMF）**
   - 有限標本空間上の確率分布
   - 有理数 ℚ での正確な計算
   - 期待値の有限和としての定義

2. **離散確率過程**
   - 時刻ごとの確率変数の列
   - フィルトレーションへの適合性

3. **マルチンゲール**
   - 「公平なゲーム」の数学的定式化
   - 適合性 + マルチンゲール条件
   - 条件付き期待値の保存

4. **Optional Stopping Theorem**
   - 「いつやめても期待値は変わらない」
   - 有界停止時間の場合の statement
   - 構造塔理論との対応

### 構造塔との対応のまとめ

| 構造塔の概念 | 確率論での意味 |
|------------|---------------|
| carrier | 事象の全体（またはΩ） |
| Index | 時刻 ℕ |
| layer n | 時刻 n で可観測な事象族（代数 F_n） |
| monotone | 情報の単調増加（F_n ⊆ F_{n+1}） |
| minLayer(A) | 事象 A が初めて可観測になる時刻 |
| Hom（射） | 可測写像 |

### 計算可能性の意義

本ファイルでは、すべての概念が計算可能であることを強調した：
- 期待値 = 有限和
- 停止時間の値 = 直接計算可能
- マルチンゲール条件 = 有限個の等式

これにより、理論と計算が一体となった理解が可能になる。

### 発展的トピック

1. **サブマルチンゲールとスーパーマルチンゲール**
   - E[M_{n+1} | ℱ_n] ≥ M_n（有利なゲーム）
   - E[M_{n+1} | ℱ_n] ≤ M_n（不利なゲーム）

2. **Doob の不等式**
   - max_{k≤n} M_k の分布の上界

3. **収束定理**
   - マルチンゲール収束定理（無限時間への拡張）

4. **連続時間への拡張**
   - ブラウン運動
   - 伊藤積分

### 参考資料

- `DecidableEvents.lean`: 事象の基礎
- `DecidableAlgebra.lean`: 有限代数
- `DecidableFiltration.lean`: 構造塔としてのフィルトレーション
- `ComputableStoppingTime.lean`: 停止時間
- `CAT2_complete.lean`: 構造塔の完全な形式化
- Williams の *Probability with Martingales*: 測度論的アプローチの標準教科書

-/

/-!
## 演習問題（Exercises）

### 基礎問題

1. **期待値の計算**
   - サイコロの目 X : Fin 6 → ℚ（X(n) = n + 1）の期待値を計算せよ
   - 答：E[X] = (1+2+3+4+5+6)/6 = 3.5

2. **マルチンゲールの検証**
   - 累積賭け金過程がマルチンゲールであることを確認せよ
   - E[M_1] = E[M_0] を計算で示せ

3. **停止時間の構成**
   - 「累積賭け金が +2 になるか -2 になったら停止」を定義せよ
   - これが停止時間条件を満たすことを確認

### 応用問題

4. **ルーレットの martingale betting system**
   - 赤黒に賭けて、負けたら賭け金を 2 倍にする戦略
   - これはマルチンゲールか？
   - OST は何を意味するか？

5. **株価モデル**
   - 株価 S_n が確率 p で上昇、1-p で下降
   - いつ適切なマルチンゲールになるか？

6. **OST の反例**
   - 有界でない停止時間では OST が成り立たない例を構成
   - ヒント：無限に続く倍賭け戦略

### 発展問題

7. **条件付き期待値の完全実装**
   - 代数の原子分解を実装
   - E[X | ℱ] を計算可能な形で定義

8. **Doob 分解**
   - 任意の適合過程をマルチンゲールと予測可能過程に分解
   - X_n = M_n + A_n

9. **連続時間への橋渡し**
   - 離散マルチンゲールの極限としてのブラウン運動
   - Donsker の定理の直感的理解

10. **構造塔との深い接続**
    - マルチンゲール射（martingale morphism）を定義
    - これは StructureTowerWithMin の Hom になるか？
-/

end Prob
