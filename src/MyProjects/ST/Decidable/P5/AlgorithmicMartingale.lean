import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.Rat   -- brings the `Semiring` / `Field` instances for ℚ
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Ring.Finset
import MyProjects.ST.Decidable.P1.DecidableEvents
import MyProjects.ST.Decidable.P2.DecidableAlgebra
import MyProjects.ST.Decidable.P3.DecidableFiltration
import MyProjects.ST.Decidable.P4.ComputableStoppingTime

open Classical
open scoped BigOperators

open Prob
open Finset

-- 明示的に与えておくと、後続の `Finset.mul_sum` などが型クラス解決に失敗しなくなる。
instance : NonUnitalNonAssocSemiring ℚ := inferInstance

/-!
# Algorithmic Martingale on Discrete Finite Sample Spaces

このファイルは、離散有限標本空間上の

* 確率質量関数 `ProbabilityMassFunction`
* 離散時間過程 `SimpleProcess`
* 有限和として定義された期待値
* （簡略版の）マルチンゲール条件
* 有界停止時間に対する Optional Stopping Theorem (OST) の「型」

を与える。

## 階層構造における位置づけ

本ファイルは、以下の階層構造の第 5 層に対応する：

DecidableEvents.lean ← 有限標本空間と decidable events
↓
DecidableAlgebra.lean ← 有限代数（Boolean 演算で閉じた事象族）
↓
DecidableFiltration.lean ← 離散版フィルトレーション（StructureTower 的な層構造）
↓
ComputableStoppingTime.lean ← 計算可能な停止時間
↓
AlgorithmicMartingale.lean ← マルチンゲールと Optional Stopping Theorem


ここでは、測度論的な一般論ではなく、**有限標本空間 + 離散フィルトレーション** に限定する。
そのため、期待値や（簡略化された）マルチンゲール条件はすべて**有限和として計算可能**であり、
`#eval` による具体的な計算が可能になる。

## 構造塔との対応

`DecidableFiltration` は、StructureTowerWithMin の具体例とみなせる：

* carrier        : 事象の全体 / 有限代数
* Index          : 時刻 `ℕ`
* layer n        : 時刻 `n` で可観測な有限代数 `ℱₙ`
* monotone       : `ℱ₀ ⊆ ℱ₁ ⊆ …` （情報の単調増加）
* minLayer(A)    : 事象 `A` が初めて可観測になる時刻
* StoppingTime   : `{τ ≤ t}` の minLayer が `t` 以下であるような時刻

本ファイルのマルチンゲールは、この離散フィルトレーション上の
**構造塔に沿った過程**として理解できる。

## スコープ

* Ω は常に有限標本空間 `Prob.FiniteSampleSpace`
* 確率は有理数値 `ℚ` の確率質量関数で表現
* 期待値は有限和として定義
* マルチンゲール条件は「全期待値が時間に沿って保存される」という
  簡略版（本格的な条件付き期待値は将来拡張）

-/

namespace Prob

/-!
## 1. 確率質量関数（Probability Mass Function）

有限標本空間 `Ω` 上の確率を、表形式の「確率質量関数」として表現する。
-/

/--
有限標本空間 `Ω` 上の確率質量関数（Probability Mass Function）。

* `pmf ω` : 標本点 `ω` に割り当てられた有理数の確率
* `nonneg` : すべての点で非負
* `sum_one` : 全標本点での和が 1
-/
structure ProbabilityMassFunction (Ω : FiniteSampleSpace) where
  /-- 確率質量関数 `Ω.carrier → ℚ`。 -/
  pmf : Ω.carrier → ℚ
  /-- 非負性：すべての標本点で `0 ≤ pmf ω`。 -/
  nonneg : ∀ ω, 0 ≤ pmf ω
  /-- 全確率が 1。 -/
  sum_one : (∑ ω, pmf ω) = 1

namespace ProbabilityMassFunction

variable {Ω : FiniteSampleSpace}

open FiniteSampleSpace

/--
有限標本空間 `Ω` 上の期待値。

`X : Ω.carrier → ℚ` に対し、

`E_P[X] = ∑_{ω ∈ Ω} P(ω) * X(ω)`

として定義する。
-/
def expected (P : ProbabilityMassFunction Ω) (X : Ω.carrier → ℚ) : ℚ :=
  ∑ ω, P.pmf ω * X ω

/--
期待値の定義から直接従う：定数関数の期待値。

`X(ω) ≡ c` のとき、`E[X] = c`。
-/
lemma expected_const (P : ProbabilityMassFunction Ω) (c : ℚ) :
    expected P (fun _ => c) = c := by
  classical
  -- E[c] = (∑ω P(ω)) * c = 1 * c = c
  have hmul :
      ∑ ω, c * P.pmf ω = c * ∑ ω, P.pmf ω := by
    -- `Finset.mul_sum` gives the reverse direction; use `symm` to flip.
    have := (Finset.mul_sum (a := c) (s := Finset.univ) (f := fun ω => P.pmf ω))
    -- this : c * ∑ ω, P.pmf ω = ∑ ω, c * P.pmf ω
    simpa [mul_comm, mul_left_comm, mul_assoc] using this.symm
  calc
    expected P (fun _ => c) = ∑ ω, P.pmf ω * c := by
      simp [expected]
    _ = ∑ ω, c * P.pmf ω := by
      refine Finset.sum_congr rfl ?_
      intro ω _; simp [mul_comm]
    _ = c * ∑ ω, P.pmf ω := hmul
    _ = c := by simpa [P.sum_one, mul_comm]

/--
指示関数 `1_A` の期待値は `P(A)` と一致する。
ここでは「`P(A)`」を有限和として書き下ろした形で表現する。
-/
noncomputable def probOfEvent (P : ProbabilityMassFunction Ω) (A : Event Ω.carrier) : ℚ :=
  ∑ ω, if ω ∈ A then P.pmf ω else 0

lemma expected_indicator (P : ProbabilityMassFunction Ω) (A : Event Ω.carrier) :
    expected P (fun ω => if ω ∈ A then 1 else 0) = probOfEvent P A := by
  classical
  simp [expected, probOfEvent, Finset.mul_sum, mul_boole]

/-! ### 期待値の線形性（基本形だけ追加） -/

lemma expected_add (P : ProbabilityMassFunction Ω)
    (X Y : Ω.carrier → ℚ) :
    expected P (fun ω => X ω + Y ω) =
      expected P X + expected P Y := by
  classical
  simp [expected, Finset.sum_add_distrib, mul_add, add_comm, add_left_comm, add_assoc]

lemma expected_mul_const (P : ProbabilityMassFunction Ω)
    (X : Ω.carrier → ℚ) (c : ℚ) :
    expected P (fun ω => c * X ω) = c * expected P X := by
  classical
  simp [expected, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

/-- 期待値と有限和の交換（有限指標 `s` 上の総和）。 -/
lemma expected_finset_sum (P : ProbabilityMassFunction Ω)
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (X : ι → Ω.carrier → ℚ) :
    expected P (fun ω => ∑ i ∈ s, X i ω) =
      ∑ i ∈ s, expected P (X i) := by
  classical
  revert X
  refine Finset.induction_on s ?base ?step
  · intro X; simp [expected]
  · intro a s ha ih X
    calc
      expected P (fun ω => ∑ i ∈ insert a s, X i ω)
          = expected P (fun ω => X a ω + ∑ i ∈ s, X i ω) := by
              simp [Finset.sum_insert, ha]
      _ = expected P (fun ω => X a ω) +
            expected P (fun ω => ∑ i ∈ s, X i ω) := by
              simpa [expected_add]
      _ = expected P (X a) + ∑ i ∈ s, expected P (X i) := by
              simpa [ih]
      _ = ∑ i ∈ insert a s, expected P (X i) := by
              simp [Finset.sum_insert, ha, add_comm, add_left_comm, add_assoc]

/-- 指示関数を掛けた期待値を if でゼロ埋めした形に書き換える。 -/
lemma expected_indicator_mul (P : ProbabilityMassFunction Ω)
    (A : Event Ω.carrier) (X : Ω.carrier → ℚ) :
    expected P (fun ω => X ω * (if ω ∈ A then 1 else 0)) =
      expected P (fun ω => if ω ∈ A then X ω else 0) := by
  classical
  -- 各項で場合分けして一致
  unfold expected
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hA : ω ∈ A
  · simp [hA, mul_comm, mul_left_comm, mul_assoc]
  · simp [hA, mul_comm, mul_left_comm, mul_assoc]

end ProbabilityMassFunction

end Prob

/-!
## 2. 離散時間過程とマルチンゲール条件（簡略版）

ここでは、構造塔（DecidableFiltration）に沿った離散時間過程を

* `SimpleProcess Ω = ℕ → Ω → ℚ`

として定義し、期待値が時間方向に保存されることを
「（簡略版の）マルチンゲール条件」とする。

**注意**: 本バージョンでは、条件付き期待値 `E[· | ℱₙ]` はまだ導入しない。
その代わり、以下の弱い条件を採用する：

`E[M_{n+1}] = E[M_n]  (0 ≤ n < timeHorizon)`

将来的には、`FiniteAlgebra` / `DecidableFiltration` を用いた
本格的な条件付き期待値に置き換える予定である。
-/

/-- 離散時間の単純過程：時刻 `n` と標本点 `ω` から有理数値を返す。 -/
abbrev SimpleProcess (Ω : Prob.FiniteSampleSpace) :=
  ℕ → Ω.carrier → ℚ

namespace SimpleProcess

variable {Ω : Prob.FiniteSampleSpace}

/-- 時刻 `n` のランダム変数を取り出す補助関数（予約語 `at` 回避のため `atTime`）。 -/
def atTime (M : SimpleProcess Ω) (n : ℕ) : Ω.carrier → ℚ := M n

@[simp] lemma atTime_def (M : SimpleProcess Ω) (n : ℕ) : M.atTime n = M n := rfl

end SimpleProcess

/-!
### フィルトレーションに対する「適合性」（プレースホルダ）

本格的には「`M n` が `ℱ.observableAt n` に可測」という性質を定義したいが、
そのためには値域側の有限代数など、追加のインフラが必要になる。

ここでは、将来の拡張を見越して `IsAdapted` を **型レベルのフラグ** としておき、
実装の最初の版では単に `True` を返すようにしておく：

* 定義は complete（sorry なし）
* しかし内容は「常に適合している」とみなす

将来のバージョンで、ここを書き換えるだけで本格的な可測性条件に差し替えられる。
-/

/--
`SimpleProcess` がフィルトレーション `ℱ` に「適合している」ことを表す型。

現バージョンでは、条件付き期待値をまだ導入していないため、
実装はダミーの `True` とする。
-/
def IsAdapted
    {Ω : Prob.FiniteSampleSpace}
    (ℱ : DecidableFiltration Ω) (M : SimpleProcess Ω) : Prop :=
  True

/-!
### 簡略版マルチンゲール条件

`ProbabilityMassFunction` による期待値を用いて

* `E[M_{n+1}] = E[M_n]` （全期待値が一定）

をマルチンゲール条件とする。ここでは

* 適合性 `IsAdapted ℱ M`（現状 `True`）
* 期待値保存条件

の 2 つをまとめて `IsMartingale` として定義する。
-/

/--
（簡略版）マルチンゲール条件：

* `adapted` : フィルトレーションに「適合している」（現状はダミー）
* `fair`    : 期待値が時間方向に保存される

`n + 1 ≤ ℱ.timeHorizon` の範囲で

`E[M_{n+1}] = E[M_n]`

が成り立つことを要求する。
-/
structure IsMartingale
    {Ω : Prob.FiniteSampleSpace}
    (P : Prob.ProbabilityMassFunction Ω)
    (ℱ : DecidableFiltration Ω)
    (M : SimpleProcess Ω) : Prop where
  /-- フィルトレーションへの適合性（現状はダミーの条件）。 -/
  adapted : IsAdapted ℱ M
  /-- 各時刻で期待値が保存されること。 -/
  fair :
    ∀ ⦃n : ℕ⦄, n + 1 ≤ ℱ.timeHorizon →
      Prob.ProbabilityMassFunction.expected P (M (n + 1)) =
      Prob.ProbabilityMassFunction.expected P (M n)

/--
より強い（OST 向けの）マルチンゲール条件：
すべての可観測事象 `A ∈ ℱ_n` に対し
`E[M_{n+1}·1_A] = E[M_n·1_A]` が成り立つ。
-/
structure IsMartingaleStrong
    {Ω : Prob.FiniteSampleSpace}
    (P : Prob.ProbabilityMassFunction Ω)
    (ℱ : DecidableFiltration Ω)
    (M : SimpleProcess Ω) : Prop where
  adapted : IsAdapted ℱ M
  fair_local :
    ∀ {n : ℕ} (hn : n ≤ ℱ.timeHorizon) (hn1 : n + 1 ≤ ℱ.timeHorizon)
      {A : Prob.Event Ω.carrier},
      A ∈ (ℱ.observableAt n hn).events →
      Prob.ProbabilityMassFunction.expected P
        (fun ω => M (n + 1) ω * (if ω ∈ A then 1 else 0)) =
      Prob.ProbabilityMassFunction.expected P
        (fun ω => M n ω * (if ω ∈ A then 1 else 0))

/-- 強い条件から「全期待値一定」版の IsMartingale を得る。 -/
lemma IsMartingaleStrong.to_IsMartingale
    {Ω : Prob.FiniteSampleSpace}
    {P : Prob.ProbabilityMassFunction Ω}
    {ℱ : DecidableFiltration Ω}
    {M : SimpleProcess Ω}
    (h : IsMartingaleStrong P ℱ M) :
    IsMartingale P ℱ M := by
  refine ⟨h.adapted, ?_⟩
  intro n hn1
  have hn : n ≤ ℱ.timeHorizon := Nat.le_trans (Nat.le_succ n) hn1
  -- 事象 A = univ をとる
  have hA : (Set.univ : Prob.Event Ω.carrier) ∈ (ℱ.observableAt n hn).events :=
    (ℱ.observableAt n hn).has_univ
  have hloc := h.fair_local hn hn1 (A := Set.univ) hA
  -- if … then 1 else 0 が常に 1 になるので簡約
  simpa using hloc

/-! ### 定数過程はマルチンゲール -/

/-- 定数値 `c` をとる単純過程。 -/
def constProcess {Ω : Prob.FiniteSampleSpace} (c : ℚ) : SimpleProcess Ω :=
  fun _ _ => c

/-- 定数過程は（期待値保存の意味で）マルチンゲール。 -/
lemma constProcess_isMartingale
    {Ω : Prob.FiniteSampleSpace}
    (P : Prob.ProbabilityMassFunction Ω)
    (ℱ : DecidableFiltration Ω) (c : ℚ) :
    IsMartingale P ℱ (constProcess c) := by
  refine ⟨?_, ?_⟩
  · trivial   -- IsAdapted はダミーで常に成立
  · intro n hn
    have hconst :
        Prob.ProbabilityMassFunction.expected P (fun _ => c) = c :=
      Prob.ProbabilityMassFunction.expected_const (P := P) (c := c)
    calc
      Prob.ProbabilityMassFunction.expected P ((constProcess c) (n + 1)) = c := by
        simpa [constProcess] using hconst
      _ = Prob.ProbabilityMassFunction.expected P ((constProcess c) n) := by
        simpa [constProcess] using hconst.symm

-- 簡単なセルフチェック：定数過程では時刻 0 と 1 の期待値が一致する。
example
    {Ω : Prob.FiniteSampleSpace}
    (P : Prob.ProbabilityMassFunction Ω) (c : ℚ) :
    Prob.ProbabilityMassFunction.expected P ((constProcess c) 0) =
    Prob.ProbabilityMassFunction.expected P ((constProcess c) 1) := by
  have h0 : Prob.ProbabilityMassFunction.expected P ((constProcess c) 0) = c := by
    simpa [constProcess] using Prob.ProbabilityMassFunction.expected_const (P := P) (c := c)
  have h1 : Prob.ProbabilityMassFunction.expected P ((constProcess c) 1) = c := by
    simpa [constProcess] using Prob.ProbabilityMassFunction.expected_const (P := P) (c := c)
  calc
    Prob.ProbabilityMassFunction.expected P ((constProcess c) 0) = c := h0
    _ = Prob.ProbabilityMassFunction.expected P ((constProcess c) 1) := h1.symm

/-! ### マルチンゲールなら期待値は時刻に依らない（ステートメント） -/
lemma martingale_expectation_const
    {Ω : Prob.FiniteSampleSpace}
    (P : Prob.ProbabilityMassFunction Ω)
    (ℱ : DecidableFiltration Ω)
    (M : SimpleProcess Ω)
    (hMart : IsMartingale P ℱ M)
    {n m : ℕ}
    (hn : n ≤ ℱ.timeHorizon) (hm : m ≤ ℱ.timeHorizon) :
    Prob.ProbabilityMassFunction.expected P (M n) =
    Prob.ProbabilityMassFunction.expected P (M m) := by
  classical
  -- 記号短縮
  set E : ℕ → ℚ := fun k => Prob.ProbabilityMassFunction.expected P (M k)
  -- 隣接時刻の期待値一致（`fair` の向きを揃える）。
  have hstep : ∀ {k}, k + 1 ≤ ℱ.timeHorizon → E k = E (k + 1) := by
    intro k hk
    simpa [E, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (hMart.fair (n := k) hk).symm
  -- 任意の基点 `a` から `a+k` まで期待値が一定。
  have hchain : ∀ a k, a + k ≤ ℱ.timeHorizon → E a = E (a + k) := by
    intro a k
    induction k with
    | zero =>
        intro _; simp [E]
    | succ k ih =>
        intro hk
        have hk_prev : a + k ≤ ℱ.timeHorizon :=
          Nat.le_trans (Nat.le_succ (a + k)) hk
        have hfair : E (a + k) = E (a + k + 1) := by
          have hk' : (a + k) + 1 ≤ ℱ.timeHorizon := by
            -- `a + k + 1 = a + (Nat.succ k)` なので `hk` がそのまま使える
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hk
          exact hstep hk'
        calc
          E a = E (a + k) := ih hk_prev
          _ = E (a + k + 1) := hfair
  -- `n` と `m` の大小で場合分けして鎖をたどる。
  cases Nat.le_total n m with
  | inl hnm =>
      have hsum : n + (m - n) = m := by
        have := Nat.sub_add_cancel hnm
        simpa [Nat.add_comm] using this
      have hleH : n + (m - n) ≤ ℱ.timeHorizon := by
        simpa [hsum] using hm
      calc
        E n = E (n + (m - n)) := hchain n (m - n) hleH
        _ = E m := by simpa [E, hsum]
  | inr hmn =>
      have hsum : m + (n - m) = n := by
        have := Nat.sub_add_cancel hmn
        simpa [Nat.add_comm] using this
      have hleH : m + (n - m) ≤ ℱ.timeHorizon := by
        simpa [hsum] using hn
      calc
        E n = E m := by
          -- `m ≤ n` のとき、`m` から先にたどる。
          have hmn' : E m = E (m + (n - m)) := hchain m (n - m) hleH
          have hm_eq : E m = E n := by simpa [E, hsum] using hmn'
          exact hm_eq.symm
        _ = E m := rfl

-- シンプルなチェック用例：定数過程では任意の 0/1 時刻で期待値が一致。
example
    {Ω : Prob.FiniteSampleSpace}
    (P : Prob.ProbabilityMassFunction Ω)
    (ℱ : DecidableFiltration Ω)
    (c : ℚ) (hH : 1 ≤ ℱ.timeHorizon) :
    Prob.ProbabilityMassFunction.expected P ((constProcess c) 0) =
    Prob.ProbabilityMassFunction.expected P ((constProcess c) 1) := by
  have hMart := constProcess_isMartingale (P := P) (ℱ := ℱ) (c := c)
  have h := martingale_expectation_const (P := P) (ℱ := ℱ)
      (M := constProcess c) (hMart := hMart)
      (n := 0) (m := 1) (hn := Nat.zero_le _) (hm := hH)
  simpa using h

/-!
定数停止時間の特別ケース：`τ(ω) ≡ k` のとき、`E[M_τ] = E[M_0]`。
-/
lemma optionalStopping_constTime
    {Ω : Prob.FiniteSampleSpace}
    (P : Prob.ProbabilityMassFunction Ω)
    (ℱ : DecidableFiltration Ω)
    (M : SimpleProcess Ω)
    (hMart : IsMartingale P ℱ M)
    (k : ℕ) (hk : k ≤ ℱ.timeHorizon)
    (τ : ComputableStoppingTime ℱ)
    (hτ : ∀ ω, τ.time ω = k) :
    Prob.ProbabilityMassFunction.expected P (fun ω => M (τ.time ω) ω) =
      Prob.ProbabilityMassFunction.expected P (M 0) := by
  -- `τ` が定数なので、左辺を `M k` に書き換える
  have hrewrite :
      Prob.ProbabilityMassFunction.expected P (fun ω => M (τ.time ω) ω) =
        Prob.ProbabilityMassFunction.expected P (M k) := by
    have hfun : (fun ω => M (τ.time ω) ω) = fun ω => M k ω := by
      funext ω; simp [hτ ω]
    simpa [hfun]
  -- マルチンゲールの性質で `E[M k] = E[M 0]`
  have hmart := martingale_expectation_const
      (P := P) (ℱ := ℱ) (M := M) (hMart := hMart)
      (n := 0) (m := k) (hn := Nat.zero_le _) (hm := hk)
  calc
    Prob.ProbabilityMassFunction.expected P (fun ω => M (τ.time ω) ω)
        = Prob.ProbabilityMassFunction.expected P (M k) := hrewrite
    _ = Prob.ProbabilityMassFunction.expected P (M 0) := hmart.symm

/-
## 3. 停止時間で打ち切った過程（stopped process）

停止時間 `τ` による打ち切り過程

`M^τ_n(ω) = M_{min(n, τ(ω))}(ω)`

を定義する。これは、後の Optional Stopping Theorem のステートメントで利用する。

ここでは `ComputableStoppingTime` を用いることで、`τ(ω)` が実際に
`#eval` で計算可能な「アルゴリズムとしての停止時間」であることが保証される。
-/

namespace SimpleProcess

variable {Ω : Prob.FiniteSampleSpace} {ℱ : DecidableFiltration Ω}

/--
停止時間 `τ` による打ち切り過程。

`(stopped M τ) n ω = M (min n (τ.time ω)) ω`
-/
def stopped (M : SimpleProcess Ω) (τ : ComputableStoppingTime ℱ) :
    SimpleProcess Ω :=
  fun n ω => M (Nat.min n (τ.time ω)) ω

@[simp] lemma stopped_at
    (M : SimpleProcess Ω) (τ : ComputableStoppingTime ℱ)
    (n : ℕ) (ω : Ω.carrier) :
    stopped M τ n ω = M (Nat.min n (τ.time ω)) ω := rfl

lemma stopped_before
    (M : SimpleProcess Ω) (τ : ComputableStoppingTime ℱ)
    (n : ℕ) (ω : Ω.carrier) (h : n ≤ τ.time ω) :
    stopped M τ n ω = M n ω := by
  simp [stopped, Nat.min_eq_left h]

lemma stopped_after
    (M : SimpleProcess Ω) (τ : ComputableStoppingTime ℱ)
    (n : ℕ) (ω : Ω.carrier) (h : τ.time ω ≤ n) :
    stopped M τ n ω = M (τ.time ω) ω := by
  simp [stopped, Nat.min_eq_right h]

end SimpleProcess

/-- 事象 `{τ = n}` を表す補助定義。 -/
def eventTauEq
    {Ω : Prob.FiniteSampleSpace} {ℱ : DecidableFiltration Ω}
    (τ : ComputableStoppingTime ℱ) (n : ℕ) : Prob.Event Ω.carrier :=
  {ω | τ.time ω = n}

@[simp] lemma mem_eventTauEq
    {Ω : Prob.FiniteSampleSpace} {ℱ : DecidableFiltration Ω}
    (τ : ComputableStoppingTime ℱ) (n : ℕ) (ω : Ω.carrier) :
    ω ∈ eventTauEq (ℱ := ℱ) τ n ↔ τ.time ω = n := Iff.rfl

@[simp] lemma indicator_eventTauEq
    {Ω : Prob.FiniteSampleSpace} {ℱ : DecidableFiltration Ω}
    (τ : ComputableStoppingTime ℱ) (n : ℕ) (ω : Ω.carrier) :
    (if τ.time ω = n then (1 : ℚ) else 0) =
    (if ω ∈ eventTauEq (ℱ := ℱ) τ n then 1 else 0) := by
  -- 条件 `τ.time ω = n` で場合分け
  by_cases h : τ.time ω = n
  · -- ケース1: τ.time ω = n
    -- 左右とも 1 になる
    simp [eventTauEq, h]
  · -- ケース2: τ.time ω ≠ n
    -- 左右とも 0 になる
    simp [eventTauEq, h]


/-! `τ = n` の指示関数を書き換える小補題。 -/
lemma expected_atStopping_term_rewrite
    {Ω : Prob.FiniteSampleSpace} {ℱ : DecidableFiltration Ω}
    (P : Prob.ProbabilityMassFunction Ω)
    (M : SimpleProcess Ω) (τ : ComputableStoppingTime ℱ) (n : ℕ) :
    Prob.ProbabilityMassFunction.expected P
      (fun ω => M n ω * (if τ.time ω = n then 1 else 0)) =
      Prob.ProbabilityMassFunction.expected P
        (fun ω => if ω ∈ eventTauEq (ℱ := ℱ) τ n then M n ω else 0) := by
  classical
  have h :=
    Prob.ProbabilityMassFunction.expected_indicator_mul
      (P := P) (A := eventTauEq (ℱ := ℱ) τ n) (X := fun ω => M n ω)
  simpa [eventTauEq] using h

/-- `τ = n` の指示を eventTauEq で書き換えた期待値版。 -/
lemma expected_at_tau_eq_as_event
    {Ω : Prob.FiniteSampleSpace} {ℱ : DecidableFiltration Ω}
    (P : Prob.ProbabilityMassFunction Ω)
    (M : SimpleProcess Ω)
    (τ : ComputableStoppingTime ℱ)
    (n : ℕ) :
  Prob.ProbabilityMassFunction.expected P
      (fun ω => M n ω * (if τ.time ω = n then 1 else 0))
    =
  Prob.ProbabilityMassFunction.expected P
      (fun ω => M n ω * (if ω ∈ eventTauEq (ℱ := ℱ) τ n then 1 else 0)) := by
  classical
  have hfun :
      (fun ω => M n ω * (if τ.time ω = n then 1 else 0))
        =
      (fun ω => M n ω * (if ω ∈ eventTauEq (ℱ := ℱ) τ n then 1 else 0)) := by
    funext ω
    simp [indicator_eventTauEq]   -- if の中身を書き換えるだけ
  simp [Prob.ProbabilityMassFunction.expected, hfun]

-- Note: `expected_at_tau_eq_to_probOfEvent` で
-- `E[M_n · 1_{τ=n}] = E[M_0] * P(τ=n)` を主張するのは、現状の前提では誤りになりうる。
--（`IsMartingale` が全期待値一定のみだから。）
-- 将来、条件付き期待値を導入し定理を強化したときに再検討する。


/-
停止時間で評価した値の期待値を、各時刻への分割和で書き下ろす型だけ用意しておく。
証明は将来の OST 章で埋める。
-/
lemma expected_atStopping_as_sum
    {Ω : Prob.FiniteSampleSpace}
    {ℱ : DecidableFiltration Ω}
    (P : Prob.ProbabilityMassFunction Ω)
    (M : SimpleProcess Ω)
    (τ : ComputableStoppingTime ℱ)
    (N : ℕ)
    (hBound : ∀ ω, τ.time ω ≤ N) :
    Prob.ProbabilityMassFunction.expected P (fun ω => M (τ.time ω) ω) =
      ∑ n ∈ Finset.range (N + 1),
        Prob.ProbabilityMassFunction.expected P
          (fun ω => M n ω * (if ω ∈ eventTauEq τ n then 1 else 0)) := by
  classical
  -- 1. 各 ω について、M_{τ(ω)}(ω) を有限和に書き換える補題（上で定義した expand）
  have expand :
      ∀ ω : Ω.carrier,
        M (τ.time ω) ω =
          (Finset.range (N + 1)).sum
            (fun n => M n ω * (if ω ∈ eventTauEq τ n then 1 else 0)) := by
    intro ω
    classical
    -- まず「関数 f」を明示的に束縛
    let f : ℕ → ℚ :=
      fun n => M n ω * (if ω ∈ eventTauEq τ n then 1 else 0)

    have hmem : τ.time ω ∈ Finset.range (N + 1) := by
      have h := hBound ω
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le h)

    have hsum :
        (Finset.range (N + 1)).sum f
          =
        f (τ.time ω) := by
      -- ここで `sum_eq_single_of_mem` を使う
      refine
        Finset.sum_eq_single_of_mem
          (a := τ.time ω) hmem ?hzero
      · -- 「a 以外の項」は 0 になることを示す
        intro n hn hne
        -- hne : n ≠ τ.time ω を `τ.time ω ≠ n` に向きをそろえる
        have hne' : τ.time ω ≠ n := by simpa [eq_comm] using hne
        -- その上で `if τ.time ω = n then 1 else 0 = 0` と落とす
        simp [f, hne']   -- ← ここで `f n = ... = 0` になる
    -- 右辺 `f (τ.time ω)` を展開すると `M (τ.time ω) ω * 1` なのでただの `M (τ.time ω) ω`
    have : (Finset.range (N + 1)).sum
              (fun n => M n ω * (if ω ∈ eventTauEq τ n then 1 else 0))
          = M (τ.time ω) ω := by
      simpa [f] using hsum
    -- 目標はこの等式の左右をひっくり返したもの
    exact this.symm    -- または `exact this.symm` でもよい


  -- 2. ランダム変数としての等式にする
  have hfun :
      (fun ω => M (τ.time ω) ω)
        =
      (fun ω =>
        (Finset.range (N + 1)).sum
          (fun n => M n ω * (if ω ∈ eventTauEq τ n then 1 else 0))) := by
    funext ω
    exact expand ω

  -- 3. 期待値に対してこの等式を適用
  calc
    Prob.ProbabilityMassFunction.expected P (fun ω => M (τ.time ω) ω)
        =
      Prob.ProbabilityMassFunction.expected P
        (fun ω =>
          (Finset.range (N + 1)).sum
            (fun n => M n ω * (if ω ∈ eventTauEq τ n then 1 else 0))) := by
        -- hfun を使って引数を書き換えるだけ
        simp [hfun]
    _ =
      ∑ n ∈ Finset.range (N + 1),
        Prob.ProbabilityMassFunction.expected P
          (fun ω => M n ω * (if ω ∈ eventTauEq τ n then 1 else 0)) := by
        -- 期待値と有限和の交換：expected_finset_sum をそのまま使う
        -- ここでは Finset.sum 版の補題を適用し、∑ n ∈ s を sugar として使う
        have := Prob.ProbabilityMassFunction.expected_finset_sum
          (P := P)
          (s := Finset.range (N + 1))
          (X := fun n ω => M n ω * (if ω ∈ eventTauEq τ n then 1 else 0))
        -- `expected_finset_sum` の結論は
        --   expected P (fun ω => (range (N+1)).sum ...) =
        --     (range (N+1)).sum (fun n => expected P ...)
        -- なので、notation を合わせれば `simpa` でゴールに一致するはずです。
        simpa using this


/--
離散有限標本空間上の有界停止時間に対する Optional Stopping Theorem（型だけ）。
証明は将来の拡張で埋める。
-/
lemma optionalStopping_theorem_split
    {Ω : Prob.FiniteSampleSpace}
    (P : Prob.ProbabilityMassFunction Ω)
    (ℱ : DecidableFiltration Ω)
    (M : SimpleProcess Ω)
    (τ : ComputableStoppingTime ℱ)
    (hBound : ∀ ω, τ.time ω ≤ ℱ.timeHorizon) :
    Prob.ProbabilityMassFunction.expected P (fun ω => M (τ.time ω) ω) =
      ∑ n ∈ Finset.range (ℱ.timeHorizon + 1),
        Prob.ProbabilityMassFunction.expected P
          (fun ω => M n ω * (if τ.time ω = n then 1 else 0)) := by
  classical
  -- 既存の expected_atStopping_as_sum を N = ℱ.timeHorizon で使うだけ
  simpa using
    (expected_atStopping_as_sum
      (P := P) (M := M) (τ := τ) (N := ℱ.timeHorizon) (hBound := hBound))

/-
OST のコア部分：「各 n ごとに `M_n · 1_{τ=n}` の期待値は `M_0 · 1_{τ=n}` と等しい」。
現行の `IsMartingale`（全期待値一定のみ）では証明できないため、型だけ確定し証明は将来の拡張に委ねる。
-/

/-
Finite-state, bounded stopping time version of OST, expanded as a finite sum.

前提:
* `IsMartingaleStrong` : 条件付き期待値レベルのマルチンゲール
* `τ` は `ℱ` に関する停止時間
* `∀ ω, τ.time ω ≤ ℱ.timeHorizon` （有界停止時間）

結論:
* `∑ E[M n 1_{τ=n}] = ∑ E[M 0 1_{τ=n}]`
-/


/--
Finite-state, bounded stopping time version of OST, expanded as a finite sum.

前提:
* `IsMartingaleStrong` : 条件付き期待値レベルのマルチンゲール
* `τ` は `ℱ` に関する停止時間
* `∀ ω, τ.time ω ≤ ℱ.timeHorizon` （有界停止時間）

結論:
* `∑ E[M n 1_{τ=n}] = ∑ E[M 0 1_{τ=n}]`
-/



lemma optionalStopping_sum_terms
    {Ω : Prob.FiniteSampleSpace}
    (P : Prob.ProbabilityMassFunction Ω)
    (ℱ : DecidableFiltration Ω)
    (M : SimpleProcess Ω)
    (hMart : IsMartingaleStrong P ℱ M)
    (τ : ComputableStoppingTime ℱ)
    (hBound : ∀ ω, τ.time ω ≤ ℱ.timeHorizon) :
    ∑ n ∈ Finset.range (ℱ.timeHorizon + 1),
      Prob.ProbabilityMassFunction.expected P
        (fun ω => M n ω * (if τ.time ω = n then 1 else 0))
    =
    ∑ n ∈ Finset.range (ℱ.timeHorizon + 1),
      Prob.ProbabilityMassFunction.expected P
        (fun ω => M 0 ω * (if τ.time ω = n then 1 else 0)) := by
  classical
  -- 1. 左辺を expected_atStopping_as_sum で E[M_τ] に書き換え
  -- 2. 右辺を「M 0 は時間に依存しない」＋ ∑ 1_{τ=n} = 1 で E[M_0] に書き換え
  -- 3. 強い OST: E[M_τ] = E[M_0] を使って等式を結ぶ
  sorry




/-- `M 0` を全時刻でコピーした定数過程。 -/
def timeConstProcess
    {Ω : Prob.FiniteSampleSpace} (M : SimpleProcess Ω) : SimpleProcess Ω :=
  fun _ ω => M 0 ω

/-- `M 0` の期待値を `{τ = n}` で分割した有限和に書き下ろす補題。 -/
lemma expected_M0_as_sum_over_tau
    {Ω : Prob.FiniteSampleSpace}
    (P : Prob.ProbabilityMassFunction Ω)
    (ℱ : DecidableFiltration Ω)
    (M : SimpleProcess Ω)
    (τ : ComputableStoppingTime ℱ)
    (hBound : ∀ ω, τ.time ω ≤ ℱ.timeHorizon) :
    Prob.ProbabilityMassFunction.expected P (M 0) =
      ∑ n ∈ Finset.range (ℱ.timeHorizon + 1),
        Prob.ProbabilityMassFunction.expected P
          (fun ω => M 0 ω * (if τ.time ω = n then 1 else 0)) := by
  classical
  -- expected_atStopping_as_sum を時間方向に定数な過程に適用
  have h :=
    expected_atStopping_as_sum
      (P := P)
      (M := timeConstProcess M)
      (τ := τ)
      (N := ℱ.timeHorizon)
      (hBound := hBound)
  -- `eventTauEq` を `τ.time ω = n` に書き戻した形
  have h' :
      Prob.ProbabilityMassFunction.expected P (fun ω => timeConstProcess M (τ.time ω) ω) =
        ∑ n ∈ Finset.range (ℱ.timeHorizon + 1),
          Prob.ProbabilityMassFunction.expected P
            (fun ω => timeConstProcess M n ω * (if τ.time ω = n then 1 else 0)) := by
    -- `expected_atStopping_as_sum` の右辺は `if ω ∈ eventTauEq τ n` なので書き換える
    simpa [indicator_eventTauEq] using h
  -- 左辺を書き換え
  have hfun :
      (fun ω => timeConstProcess M (τ.time ω) ω) =
        (fun ω => M 0 ω) := by
    funext ω; simp [timeConstProcess]
  -- 右辺の各項を書き換え
  have hsum :
      ∑ n ∈ Finset.range (ℱ.timeHorizon + 1),
        Prob.ProbabilityMassFunction.expected P
          (fun ω => timeConstProcess M n ω * (if τ.time ω = n then 1 else 0)) =
      ∑ n ∈ Finset.range (ℱ.timeHorizon + 1),
        Prob.ProbabilityMassFunction.expected P
          (fun ω => M 0 ω * (if τ.time ω = n then 1 else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro n hn; simp [timeConstProcess]
  calc
    Prob.ProbabilityMassFunction.expected P (M 0)
        = Prob.ProbabilityMassFunction.expected P (fun ω => timeConstProcess M (τ.time ω) ω) := by
            simpa [hfun]
    _ = ∑ n ∈ Finset.range (ℱ.timeHorizon + 1),
          Prob.ProbabilityMassFunction.expected P
            (fun ω => timeConstProcess M n ω * (if τ.time ω = n then 1 else 0)) := h'
    _ = ∑ n ∈ Finset.range (ℱ.timeHorizon + 1),
        Prob.ProbabilityMassFunction.expected P
            (fun ω => M 0 ω * (if τ.time ω = n then 1 else 0)) := hsum

/-- パスごとの増分分解：`M τ - M 0` を増分の有限和に展開する（期待値を取る前の純代数）。 -/
lemma pathwise_increment_decomp
    {Ω : Prob.FiniteSampleSpace}
    (ℱ : DecidableFiltration Ω)
    (M : SimpleProcess Ω)
    (τ : ComputableStoppingTime ℱ) :
    ∀ ω,
      M (τ.time ω) ω - M 0 ω =
        ∑ n ∈ Finset.range ℱ.timeHorizon,
          ((M (n + 1) ω - M n ω) * (if τ.time ω > n then 1 else 0)) := by
  classical
  intro ω
  set k := τ.time ω
  have hk : k ≤ ℱ.timeHorizon := τ.time_le_horizon ω
  -- 係数が 0 になる項を落として range k に縮約
  have hsplit :
      ∑ n ∈ Finset.range ℱ.timeHorizon,
        (if k > n then (M (n + 1) ω - M n ω) else 0)
      =
      ∑ n ∈ Finset.range k, (M (n + 1) ω - M n ω) := by
    -- filterで k>n を残すと range k に一致
    have hfilter :
        Finset.filter (fun n => k > n) (Finset.range ℱ.timeHorizon)
          = Finset.range k := by
      ext n
      constructor
      · intro h
        rcases Finset.mem_filter.mp h with ⟨hnTH, hlt⟩
        exact Finset.mem_range.mpr hlt
      · intro h
        have hn : n < k := Finset.mem_range.mp h
        have hnTH : n < ℱ.timeHorizon := lt_of_lt_of_le hn hk
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnTH, hn⟩
    calc
      ∑ n ∈ Finset.range ℱ.timeHorizon,
          (if k > n then (M (n + 1) ω - M n ω) else 0)
          = ∑ n ∈ (Finset.range ℱ.timeHorizon).filter (fun n => k > n),
              (M (n + 1) ω - M n ω) := by
              -- sum_filter で if を吸収
              classical
              have := Finset.sum_filter
                (s := Finset.range ℱ.timeHorizon)
                (p := fun n => k > n)
                (f := fun n => M (n + 1) ω - M n ω)
              -- sum_filter : ∑ s (if p then f else 0) = ∑ (filter p s) f
              -- ここでは左右を入れ替えて使う
              simpa using this.symm
      _ = ∑ n ∈ Finset.range k, (M (n + 1) ω - M n ω) := by
            simpa [hfilter]
  -- テレスコープ：∑_{n<k} (M_{n+1}-M_n) = M_k - M_0
  have htel :
      ∑ n ∈ Finset.range k, (M (n + 1) ω - M n ω) =
        M k ω - M 0 ω := by
    induction k with
    | zero =>
        simp
    | succ k ih =>
        calc
          ∑ n ∈ Finset.range (k + 1), (M (n + 1) ω - M n ω)
              = (∑ n ∈ Finset.range k, (M (n + 1) ω - M n ω))
                  + (M (k + 1) ω - M k ω) := by
                    simpa using
                      (Finset.sum_range_succ (f := fun n => M (n + 1) ω - M n ω) k)
          _ = (M k ω - M 0 ω) + (M (k + 1) ω - M k ω) := by
            simp [ih]
          _ = M (k + 1) ω - M 0 ω := by
            -- (a - b) + (b - c) = a - c
            have h := sub_add_sub_cancel (M (k + 1) ω) (M k ω) (M 0 ω)
            -- sub_add_sub_cancel : a - b + (b - c) = a - c
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  -- 仕上げ：0 を掛けていた項を元に戻す
  calc
    M (τ.time ω) ω - M 0 ω
        = ∑ n ∈ Finset.range k, (M (n + 1) ω - M n ω) := htel.symm
    _ = ∑ n ∈ Finset.range ℱ.timeHorizon,
          (if k > n then (M (n + 1) ω - M n ω) else 0) := hsplit.symm
    _ = ∑ n ∈ Finset.range ℱ.timeHorizon,
          ((M (n + 1) ω - M n ω) * (if k > n then 1 else 0)) := by
          -- 0/1 のスカラーを前に出す（ℚ 上）
          refine Finset.sum_congr rfl ?_
          intro n hn; by_cases h : k > n <;> simp [h]
    _ = ∑ n ∈ Finset.range ℱ.timeHorizon,
          ((M (n + 1) ω - M n ω) * (if τ.time ω > n then 1 else 0)) := by
          simp [k]

lemma expected_sub
    {Ω : Prob.FiniteSampleSpace}
    (P : Prob.ProbabilityMassFunction Ω)
    (X Y : Ω.carrier → ℚ) :
  Prob.ProbabilityMassFunction.expected P
    (fun ω => X ω - Y ω)
  =
  Prob.ProbabilityMassFunction.expected P X -
    Prob.ProbabilityMassFunction.expected P Y := by
  classical
  -- E[X - Y] = E[X + (-Y)]
  have h_add :=
    Prob.ProbabilityMassFunction.expected_add (P := P)
      (X := X) (Y := fun ω => - Y ω)
  have h_neg :
      Prob.ProbabilityMassFunction.expected P
        (fun ω => - Y ω)
      =
      - Prob.ProbabilityMassFunction.expected P Y := by
    -- -Y = (-1) * Y
    have := Prob.ProbabilityMassFunction.expected_mul_const
      (P := P) (X := Y) (c := (-1 : ℚ))
    simpa [mul_comm] using this

  calc
    Prob.ProbabilityMassFunction.expected P
      (fun ω => X ω - Y ω)
        = Prob.ProbabilityMassFunction.expected P
            (fun ω => X ω + - Y ω) := by
              simp [sub_eq_add_neg]
    _ = Prob.ProbabilityMassFunction.expected P X +
        Prob.ProbabilityMassFunction.expected P
          (fun ω => - Y ω) := by
              simpa using h_add
    _ = _ := by
      -- E[X] + E[-Y] = E[X] - E[Y]
      simpa [h_neg, sub_eq_add_neg]


/-- Step 1：局所増分の期待値が 0 になる（強マルチンゲール＋停止時間の可観測性）。 -/
lemma increment_zero
    {Ω : Prob.FiniteSampleSpace}
    (P : Prob.ProbabilityMassFunction Ω)
    (ℱ : DecidableFiltration Ω)
    (M : SimpleProcess Ω)
    (hMart : IsMartingaleStrong P ℱ M)
    (τ : ComputableStoppingTime ℱ)
    (n : ℕ) (hn1 : n + 1 ≤ ℱ.timeHorizon) :
  Prob.ProbabilityMassFunction.expected P
    (fun ω =>
      (M (n+1) ω - M n ω) *
      (if τ.time ω > n then 1 else 0)) = 0 := by
  classical
  ------------------------------------------------------------------
  -- 1. A := {τ ≤ n} の補集合 (= {τ > n}) と indicator の定義
  ------------------------------------------------------------------
  let A : Prob.Event Ω.carrier :=
    Prob.Event.complement (ComputableStoppingTime.eventLe (τ := τ) n)
  let ind : Ω.carrier → ℚ := fun ω => if ω ∈ A then 1 else 0

  have hn : n ≤ ℱ.timeHorizon :=
    Nat.le_trans (Nat.le_succ n) hn1

  -- {τ ≤ n} ∈ ℱ.observableAt n ⇒ その補集合 A も可観測
  have hA :
      A ∈ (ℱ.observableAt n hn).events := by
    have hLe :=
      ComputableStoppingTime.eventLe_mem_observable
        (τ := τ) n hn
    exact (ℱ.observableAt n hn).closed_complement hLe

  -- fair_local を A に適用
  have hfair :=
    hMart.fair_local (hn := hn) (hn1 := hn1) (A := A) hA
  -- hfair :
  --   P.expected (fun ω => M (n+1) ω * ind ω)
  --   = P.expected (fun ω => M n ω * ind ω)

  ------------------------------------------------------------------
  -- 2. E[(M_{n+1}-M_n)·ind] を「差の期待値」に落とす
  ------------------------------------------------------------------
  have hdiff :
      Prob.ProbabilityMassFunction.expected P
        (fun ω => (M (n+1) ω - M n ω) * ind ω) =
      Prob.ProbabilityMassFunction.expected P
        (fun ω => M (n+1) ω * ind ω) -
      Prob.ProbabilityMassFunction.expected P
        (fun ω => M n ω * ind ω) := by
    -- integrand を (g - h) 形にして expected_sub 適用
    have h_sub :
        (fun ω => (M (n+1) ω - M n ω) * ind ω)
          =
        (fun ω =>
          (M (n+1) ω * ind ω) -
          (M n ω * ind ω)) := by
      -- pointwise に sub_mul を使うだけ
      funext ω
      -- (a - b) * c = a*c - b*c
      simpa [ind] using
        (sub_mul (M (n+1) ω) (M n ω) (ind ω))
    -- E[(g - h)] = E[g] - E[h]
    have h_exp_sub :=
      expected_sub
        (P := P)
        (X := fun ω => M (n+1) ω * ind ω)
        (Y := fun ω => M n ω * ind ω)
    -- integrand の書き換えを反映
    simpa [h_sub] using h_exp_sub

  ------------------------------------------------------------------
  -- 3. fair_local から差が 0 になることを取り出す
  ------------------------------------------------------------------
  have hzeroA :
      Prob.ProbabilityMassFunction.expected P
        (fun ω => (M (n+1) ω - M n ω) * ind ω) = 0 := by
    -- hdiff の RHS に hfair を入れて「x - x = 0」
    have :
        Prob.ProbabilityMassFunction.expected P
          (fun ω => M (n+1) ω * ind ω) -
        Prob.ProbabilityMassFunction.expected P
          (fun ω => M n ω * ind ω) = 0 := by
      -- hfair : E[M_{n+1}·ind] = E[M_n·ind]
      -- → 差は 0
      simpa [hfair, sub_self]
    exact hdiff.trans this

  ------------------------------------------------------------------
  -- 4. ind を「{τ>n} の indicator」に書き換えて終了
  ------------------------------------------------------------------
  have hind :
      ind =
      (fun ω : Ω.carrier =>
        if τ.time ω > n then (1 : ℚ) else 0) := by
    funext ω
    dsimp [ind, A, ComputableStoppingTime.eventLe, Prob.Event.complement]
    by_cases hle : τ.time ω ≤ n
    · have hgt : ¬ τ.time ω > n := Nat.not_lt.mpr hle
      simp [hle, hgt]
    · have hgt : τ.time ω > n := Nat.lt_of_not_ge hle
      simp [hle, hgt]

  calc
    Prob.ProbabilityMassFunction.expected P
      (fun ω =>
        (M (n+1) ω - M n ω) *
        (if τ.time ω > n then 1 else 0))
      = Prob.ProbabilityMassFunction.expected P
          (fun ω =>
            (M (n+1) ω - M n ω) * ind ω) := by
            -- ind = 1_{τ>n} を使って integrand を書き換え
            simp [hind]
    _ = 0 := hzeroA



/-theorem optionalStopping_theorem
    {Ω : Prob.FiniteSampleSpace}
    (P : Prob.ProbabilityMassFunction Ω)
    (ℱ : DecidableFiltration Ω)
    (M : SimpleProcess Ω)
    (hMart : IsMartingaleStrong P ℱ M)
    (τ : ComputableStoppingTime ℱ)
    (hBound : ∀ ω, τ.time ω ≤ ℱ.timeHorizon) :
    Prob.ProbabilityMassFunction.expected P (M 0) =
      Prob.ProbabilityMassFunction.expected P (fun ω => M (τ.time ω) ω) := by
  classical
  -- Step 1: E[M_τ] を有限和に分解
  have hsplit :=
    optionalStopping_theorem_split P ℱ M τ hBound
  -- Step 2: 和の各項で M_n を M_0 に置き換える
  have hsum :=
    optionalStopping_sum_terms P ℱ M (IsMartingaleStrong.to_IsMartingale hMart) τ
  -- Step 3: M_0 側の有限和は E[M_0] に戻る
  have hM0 :=
    expected_M0_as_sum_over_tau P ℱ M τ hBound

  -- 3 つの等式をつないで結論を得る
  calc
    Prob.ProbabilityMassFunction.expected P (M 0)
        = ∑ n ∈ Finset.range (ℱ.timeHorizon + 1),
            Prob.ProbabilityMassFunction.expected P
              (fun ω => M 0 ω * (if τ.time ω = n then 1 else 0)) := by
          exact hM0
    _ = ∑ n ∈ Finset.range (ℱ.timeHorizon + 1),
            Prob.ProbabilityMassFunction.expected P
              (fun ω => M n ω * (if τ.time ω = n then 1 else 0)) := by
          exact hsum.symm
    _ = Prob.ProbabilityMassFunction.expected P (fun ω => M (τ.time ω) ω) := by
          exact hsplit.symm
-/
  /-
  証明スケッチ（今は `sorry` のまま）:
  1. `expected_atStopping_as_sum` を使って
       `E[M_τ] = ∑_{n=0}^{N} E[M_n · 1_{τ=n}]`
     に分解する。ここで `N = ℱ.timeHorizon`。
  2. マルチンゲール性から `E[M_n]` は n に依らず一定。
     定数 `E[M_0]` を取り出し、指示関数の期待値は確率 `P(τ=n)` に置き換える。
  3. 全確率の和が 1 であることを使って
       `E[M_τ] = E[M_0] * ∑_{n=0}^{N} P(τ=n) = E[M_0]`.
  -/

/-
## 4. 有界停止時間に対する Optional Stopping Theorem（ステートメント）

ここでは、有限標本空間 + 有界停止時間という強い仮定の下での
離散版 Optional Stopping Theorem の「型」を与える。

**重要**: 本バージョンでは証明は `sorry` として残し、将来の拡張に委ねる。
-/

/-
有界停止時間に対する離散 Optional Stopping Theorem（簡略版）のステートメント。

有限標本空間 `Ω` 上で：

* `P` : 確率質量関数
* `ℱ` : 離散フィルトレーション
* `M` : `P` に関して期待値が保存されるマルチンゲール
* `τ` : `ℱ` に関する計算可能な停止時間
* `N` : `τ` の一様上界（`τ.time ω ≤ N`）

とすると、

`E[M_0] = E[M_{τ}]`

が成り立つ、という形の Optional Stopping Theorem を主張する。

ここで右辺の期待値は、「`τ(ω)` 時刻で評価した `M`」を有限和で平均したものである。
-/
/-
-- Optional Stopping Theorem（証明は未実装、将来拡張）。
-- 上界はフィルトレーションの timeHorizon に合わせる。
-- theorem optionalStopping_theorem
--     {Ω : Prob.FiniteSampleSpace}
--     (P : Prob.ProbabilityMassFunction Ω)
--     (ℱ : DecidableFiltration Ω)
--     (M : SimpleProcess Ω)
--     (hMart : IsMartingale P ℱ M)
--     (τ : ComputableStoppingTime ℱ)
--     (hBound : ComputableStoppingTime.isBounded τ ℱ.timeHorizon) :
--     Prob.ProbabilityMassFunction.expected P (M 0) =
--     Prob.ProbabilityMassFunction.expected P (fun ω => M (τ.time ω) ω) := by
--   sorry

  証明の方針（スケッチ）:

  1. 有限標本空間なので、すべての和は有限和に落ちる。
  2. 各標本点 `ω` に対し、`τ(ω) ≤ N` であるから、
     `M (τ(ω)) ω` は有限個の値のうちいずれか。
  3. マルチンゲール条件 `E[M_{n+1}] = E[M_n]` を
     `n = 0, 1, ..., N-1` について繰り返し用いることで
     `E[M_0] = E[M_N]` を得る。
  4. 有界停止時間の情報を用いて、「`M_N` の期待値」と
     「`M_{τ}` の期待値」が一致することを示す。
     （有限標本空間なので、全ての標本点について場合分けが可能）
  5. 以上より `E[M_0] = E[M_τ]` が従う。

  実際の形式的証明では：
  * `Finset` による有限和展開
  * `τ.time ω` の値での分類
  * マルチンゲール条件を用いた望ましい望ましさを示す

  といったステップを Lean で実装する必要がある。
  本ファイルの現バージョンでは、ステートメントのみを提供し、
  証明は将来の課題として `sorry` に残す。
  -/

/-!
## 5. 計算例（#eval）

最後に、簡単な有限標本空間の上で

* 確率質量関数
* 単純過程
* 期待値

を実際に `#eval` で計算する例をいくつか示す。

ここでは、もっとも単純な標本空間として `Unit` を用いる。
-/

noncomputable section Examples

open Prob
open Prob.ProbabilityMassFunction

/-- `Unit` 型を標本空間とした有限標本空間。 -/
def unitSpace : Prob.FiniteSampleSpace where
  carrier := Unit
  fintype := inferInstance
  decidableEq := inferInstance

/--
`Unit` 上の「自明な」確率質量関数。

ただ一つの標本点 `()` に確率 1 を割り当てる。
-/
def unitPMF : Prob.ProbabilityMassFunction unitSpace :=
{ pmf := fun _ => (1 : ℚ)
, nonneg := by
    intro _
    -- 0 ≤ (1 : ℚ)
    simp
, sum_one := by
    classical
    -- `Unit` には 1 点しかないので、和は 1 になる
    simp [FiniteSampleSpace.instFintype, unitSpace]
}

/--
`Unit` 上の単純過程の例。

時刻 `n` で常に値 `n` をとる（標本点には依存しない）過程。
-/
def unitProcess : SimpleProcess unitSpace :=
  fun n _ => (n : ℚ)

/-- 初期時刻の期待値：`E[M_0]`。 -/
def unitProcess_E0 : ℚ :=
  expected unitPMF (unitProcess 0)

/-- 時刻 1 の期待値：`E[M_1]`。 -/
def unitProcess_E1 : ℚ :=
  expected unitPMF (unitProcess 1)

/-
`Unit` 空間では、`M_n(()) = n` なので

* `E[M_0] = 0`
* `E[M_1] = 1`

になるはずであることを #eval で確認できる。
-/
#eval unitProcess_E0   -- 0
#eval unitProcess_E1   -- 1

end Examples
