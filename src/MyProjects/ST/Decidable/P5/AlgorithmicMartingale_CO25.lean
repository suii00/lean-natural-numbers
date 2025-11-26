import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import MyProjects.ST.Decidable.P1.DecidableEvents
import MyProjects.ST.Decidable.P2.DecidableAlgebra
import MyProjects.ST.Decidable.P3.DecidableFiltration
import MyProjects.ST.Decidable.P4.ComputableStoppingTime

open Classical
open scoped BigOperators
open Prob

/-
Minimal core of Algorithmic Martingale (CO25 version):
  * ProbabilityMassFunction on finite spaces
  * expected / probOfEvent / expected_indicator
  * SimpleProcess + adapted flag + martingale (simplified)
  * stopped process
  * Optional Stopping Theorem left as a commented placeholder
-/

/-- ℚ の非単位半環インスタンスを明示。 -/
instance : NonUnitalNonAssocSemiring ℚ := inferInstance

namespace Prob

/-- 有限標本空間上の確率質量関数。 -/
structure ProbabilityMassFunction (Ω : FiniteSampleSpace) where
  pmf     : Ω.carrier → ℚ
  nonneg  : ∀ ω, 0 ≤ pmf ω
  sum_one : (∑ ω, pmf ω) = 1

namespace ProbabilityMassFunction

variable {Ω : FiniteSampleSpace}

/-- 期待値（有限和）。 -/
def expected (P : ProbabilityMassFunction Ω) (X : Ω.carrier → ℚ) : ℚ :=
  ∑ ω, P.pmf ω * X ω

/-- 定数関数の期待値。 -/
lemma expected_const (P : ProbabilityMassFunction Ω) (c : ℚ) :
    expected P (fun _ => c) = c := by
  classical
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

/-- 事象 A の確率。 -/
noncomputable def probOfEvent (P : ProbabilityMassFunction Ω) (A : Event Ω.carrier) : ℚ :=
  ∑ ω, if ω ∈ A then P.pmf ω else 0

/-- 指示関数の期待値＝事象の確率。 -/
lemma expected_indicator (P : ProbabilityMassFunction Ω) (A : Event Ω.carrier) :
    expected P (fun ω => if ω ∈ A then 1 else 0) = probOfEvent P A := by
  classical
  simp [expected, probOfEvent, Finset.mul_sum, mul_boole]

end ProbabilityMassFunction

end Prob

/-- 離散時間の単純過程。 -/
abbrev SimpleProcess (Ω : Prob.FiniteSampleSpace) := ℕ → Ω.carrier → ℚ

namespace SimpleProcess

variable {Ω : Prob.FiniteSampleSpace}

/-- 時刻 `n` のランダム変数を取り出す補助関数。 -/
def atTime (M : SimpleProcess Ω) (n : ℕ) : Ω.carrier → ℚ := M n

@[simp] lemma atTime_def (M : SimpleProcess Ω) (n : ℕ) : M.atTime n = M n := rfl

end SimpleProcess

/-- 適合性（現状はダミー）。 -/
def IsAdapted {Ω : Prob.FiniteSampleSpace}
    (ℱ : DecidableFiltration Ω) (M : SimpleProcess Ω) : Prop := True

/-- 期待値保存だけを課した簡略マルチンゲール条件。 -/
structure IsMartingale {Ω : Prob.FiniteSampleSpace}
    (P : Prob.ProbabilityMassFunction Ω) (ℱ : DecidableFiltration Ω)
    (M : SimpleProcess Ω) : Prop where
  adapted : IsAdapted ℱ M
  fair :
    ∀ ⦃n : ℕ⦄, n + 1 ≤ ℱ.timeHorizon →
      Prob.ProbabilityMassFunction.expected P (M (n + 1)) =
      Prob.ProbabilityMassFunction.expected P (M n)

namespace SimpleProcess

variable {Ω : Prob.FiniteSampleSpace} {ℱ : DecidableFiltration Ω}

/-- 停止時間で打ち切った過程。 -/
def stopped (M : SimpleProcess Ω) (τ : ComputableStoppingTime ℱ) :
    SimpleProcess Ω :=
  fun n ω => M (Nat.min n (τ.time ω)) ω

@[simp] lemma stopped_at (M : SimpleProcess Ω) (τ : ComputableStoppingTime ℱ)
    (n : ℕ) (ω : Ω.carrier) :
    stopped M τ n ω = M (Nat.min n (τ.time ω)) ω := rfl

end SimpleProcess

/-
-- Optional Stopping Theorem（証明は未実装、将来拡張）
-- theorem optionalStopping_theorem
--     {Ω : Prob.FiniteSampleSpace}
--     (P : Prob.ProbabilityMassFunction Ω)
--     (ℱ : DecidableFiltration Ω)
--     (M : SimpleProcess Ω)
--     (hMart : IsMartingale P ℱ M)
--     (τ : ComputableStoppingTime ℱ)
--     (N : ℕ)
--     (hBound : ComputableStoppingTime.isBounded τ N) :
--     Prob.ProbabilityMassFunction.expected P (M 0) =
--     Prob.ProbabilityMassFunction.expected P (fun ω => M (τ.time ω) ω) := by
--   sorry
-/

/-
-- Unit 空間での簡単な例（必要になったらコメントを外す）
-- noncomputable section Examples
-- open Prob
-- open Prob.ProbabilityMassFunction
-- def unitSpace : Prob.FiniteSampleSpace := { carrier := Unit, fintype := inferInstance, decidableEq := inferInstance }
-- def unitProcess : SimpleProcess unitSpace := fun n _ => (n : ℚ)
-- end Examples
-/
