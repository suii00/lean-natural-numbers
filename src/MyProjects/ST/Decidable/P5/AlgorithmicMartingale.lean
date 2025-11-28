import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.Rat   -- brings the `Semiring` / `Field` instances for ℚ
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import MyProjects.ST.Decidable.P1.DecidableEvents
import MyProjects.ST.Decidable.P2.DecidableAlgebra
import MyProjects.ST.Decidable.P3.DecidableFiltration
import MyProjects.ST.Decidable.P4.ComputableStoppingTime

open Classical
open scoped BigOperators

open Prob

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
noncomputable def unitPMF : Prob.ProbabilityMassFunction unitSpace :=
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
