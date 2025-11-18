import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import MyProjects.ST.Formalization.P3.StoppingTime_MinLayer

/-
# Martingale_StructureTower

`StoppingTime_MinLayer.lean` までで整備した「構造塔 × 停止時間 × 停止過程」の API を受け、
ここでは *離散時間・実数値* のマルチンゲールを最小限の道具立てで formalize する。

本ファイルのゴールは「条件付き期待値を mathlib の `condexp` でラップし、
マルチンゲールの定義とごく基本的な API を用意する」ことに絞る。

この段階ではオプショナル停止定理やドゥーブの定理は扱わず、
今後の拡張のための土台を明文化する。
-/

open scoped Classical
open MeasureTheory

namespace StructureTowerProbability

/-- 以降の章では mathlib のフィルトレーションを `MLFiltration` という別名で利用する（添字は ℕ）。 -/
abbrev MLFiltration (Ω : Type*) [m : MeasurableSpace Ω] :=
  MeasureTheory.Filtration ℕ m

/-- 離散時間実数値過程。 -/
abbrev Process (Ω : Type*) :=
  ℕ → Ω → ℝ

namespace Process

variable {Ω}

/-- 定数過程。 -/
def const (c : ℝ) : Process Ω :=
  fun _ _ => c

/-- 和。 -/
def add (X Y : Process Ω) : Process Ω :=
  fun n ω => X n ω + Y n ω

/-- スカラー倍。 -/
def smul (a : ℝ) (X : Process Ω) : Process Ω :=
  fun n ω => a * X n ω

end Process

variable {Ω : Type*} [MeasurableSpace Ω]

/--
条件付き期待値のラッパー。
mathlib 既存の `condexp μ (ℱ.𝓕 n)` を明示的に呼び出すだけだが、
構造塔側の記法 (`condExp μ ℱ n`) として定着させておく。
-/
noncomputable def condExp
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : MLFiltration Ω) (n : ℕ) (f : Ω → ℝ) : Ω → ℝ :=
  MeasureTheory.condExp (ℱ n) μ f

/--
離散時間マルチンゲールの最小定義。

* `filtration` : 参照するフィルトレーション
* `process` : 実数値過程
* `adapted` : 各時刻での強可測性
* `integrable` : 各時刻での可積分性
* `martingale` : `E[X_{n+1} | 𝓕_n] = X_n` を a.e. 等式で表現
-/
structure Martingale
    (μ : Measure Ω) [IsFiniteMeasure μ] where
  filtration : MLFiltration Ω
  process : Process Ω
  adapted :
      MeasureTheory.Adapted filtration process
  integrable :
      ∀ n, Integrable (process n) μ
  martingale :
      ∀ n,
        condExp μ filtration n (process (n + 1))
          =ᵐ[μ] process n

namespace Martingale

variable {μ : Measure Ω} [IsFiniteMeasure μ]

/-- 各時刻 `n` の可積分性を取り出す補題。 -/
lemma integrable_n (M : Martingale μ) (n : ℕ) :
    Integrable (M.process n) μ :=
  M.integrable n

/-- 適合性（`StronglyMeasurable[ℱ n]`）をそのまま取り出す補題。 -/
lemma adapted_stronglyMeasurable (M : Martingale μ) (n : ℕ) :
    StronglyMeasurable[M.filtration n] (M.process n) :=
  M.adapted n

noncomputable def const (ℱ : MLFiltration Ω) (c : ℝ) : Martingale μ := by
  classical
  refine
    { filtration := ℱ
      process := Process.const (Ω := Ω) c
      adapted := by
        simpa [Process.const] using
          (MeasureTheory.adapted_const (β := ℝ) ℱ c)
      integrable := by
        intro n
        change Integrable (fun _ : Ω => c) μ
        exact integrable_const (μ := μ) c
      martingale := by
        intro n
        have hconst :
            MeasureTheory.condExp (ℱ n) μ (fun _ : Ω => c)
              = fun _ : Ω => c :=
          MeasureTheory.condExp_const (μ := μ) (hm := ℱ.le n) c
        exact
          Filter.EventuallyEq.of_eq <|
          by simpa [Process.const, condExp] using hconst }

--!

/-- マルチンゲールの和。2 つのマルチンゲールが同じフィルトレーションに従うとき定義できる。 -/
noncomputable def add (M N : Martingale μ)
    (hℱ : M.filtration = N.filtration) : Martingale μ := by
  classical
  refine
    { filtration := M.filtration
      process := Process.add M.process N.process
      adapted := by
        have hN :
            MeasureTheory.Adapted M.filtration N.process := by
          simpa [hℱ] using N.adapted
        simpa [Process.add] using
          M.adapted.add hN
      integrable := ?_
      martingale := ?_ }
  · intro n
    simpa [Process.add] using
      (M.integrable n).add (N.integrable n)
  · intro n
    have h_add :
        condExp μ M.filtration n
            (fun ω => M.process (n + 1) ω + N.process (n + 1) ω)
          =ᵐ[μ]
            fun ω =>
              condExp μ M.filtration n (M.process (n + 1)) ω +
                condExp μ M.filtration n (N.process (n + 1)) ω := by
      simpa [condExp, Process.add] using
        (MeasureTheory.condExp_add (μ := μ) (m := M.filtration n)
          (hf := M.integrable (n + 1))
          (hg := N.integrable (n + 1)))
    have h_sum :
        (fun ω =>
            condExp μ M.filtration n (M.process (n + 1)) ω +
              condExp μ M.filtration n (N.process (n + 1)) ω)
          =ᵐ[μ]
          fun ω => M.process n ω + N.process n ω := by
      refine (M.martingale n).add ?_
      simpa [condExp, hℱ] using N.martingale n
    refine h_add.trans ?_
    simpa [Process.add, condExp] using h_sum

@[simp]
lemma add_filtration (M N : Martingale μ) (hℱ : M.filtration = N.filtration) :
    (add (μ := μ) M N hℱ).filtration = M.filtration :=
  rfl

/-- マルチンゲールのスカラー倍。 -/
noncomputable def smul (a : ℝ) (M : Martingale μ) : Martingale μ := by
  classical
  refine
    { filtration := M.filtration
      process := Process.smul a M.process
      adapted := by
        simpa [Process.smul] using
          M.adapted.smul a
      integrable := ?_
      martingale := ?_ }
  · intro n
    simpa [Process.smul] using
      (M.integrable n).smul a
  · intro n
    have h_smul :
        condExp μ M.filtration n (fun ω => a * M.process (n + 1) ω)
          =ᵐ[μ]
            fun ω => a * condExp μ M.filtration n (M.process (n + 1)) ω := by
      simpa [Process.smul, condExp] using
        (MeasureTheory.condExp_smul (μ := μ) (c := a)
          (m := M.filtration n) (f := M.process (n + 1)))
    have h_scaled :
        (fun _ : Ω => a) =ᵐ[μ] fun _ : Ω => a :=
      Filter.EventuallyEq.rfl
    have h_target :=
        h_scaled.smul (M.martingale n)
    refine h_smul.trans ?_
    simpa [Process.smul, condExp] using h_target

@[simp]
lemma smul_filtration (a : ℝ) (M : Martingale μ) :
    (smul (μ := μ) a M).filtration = M.filtration :=
  rfl

/-- マルチンゲールを停止時間 `τ` で止めたパスワイズ過程。 -/
def stoppedProcess (M : Martingale μ) (τ : Ω → ℕ) : Process Ω :=
  StructureTowerProbability.stopped M.process τ

/-- 停止時間より前では元の過程と一致。 -/
lemma stoppedProcess_eq_of_le (M : Martingale μ) (τ : Ω → ℕ)
    {n : ℕ} {ω : Ω} (hn : n ≤ τ ω) :
    M.stoppedProcess τ n ω = M.process n ω := by
  change StructureTowerProbability.stopped _ _ _ _ = _
  simpa using
    (StructureTowerProbability.stopped_eq_of_le
      (X := M.process) (τ := τ) (n := n) (ω := ω) hn)

/-- 停止後は値が固定される。 -/
lemma stoppedProcess_const_of_ge (M : Martingale μ) (τ : Ω → ℕ)
    {n m : ℕ} {ω : Ω} (hτ : τ ω ≤ n) (hnm : n ≤ m) :
    M.stoppedProcess τ m ω = M.stoppedProcess τ n ω := by
  change
      StructureTowerProbability.stopped _ _ _ _
        = StructureTowerProbability.stopped _ _ _ _
  simpa using
    (StructureTowerProbability.stopped_const_of_ge
      (X := M.process) (τ := τ) (n := n) (m := m) (ω := ω) hτ hnm)

/-- 十分大きな時刻で止めると `atStoppingTime` と一致。 -/
lemma stoppedProcess_eq_atStoppingTime (M : Martingale μ) (τ : Ω → ℕ)
    {N : ℕ} {ω : Ω} (hN : τ ω ≤ N) :
    M.stoppedProcess τ N ω
      = StructureTowerProbability.atStoppingTime M.process τ ω := by
  change
      StructureTowerProbability.stopped _ _ _ _
        = StructureTowerProbability.atStoppingTime _ _ _
  simpa using
    (StructureTowerProbability.stopped_eq_atStoppingTime
      (X := M.process) (τ := τ) (N := N) (ω := ω) hN)

/-- マルチンゲールの「マルチンゲール性」をそのまま取り出す補題。 -/
lemma condExp_next (M : Martingale μ) (n : ℕ) :
    condExp μ M.filtration n (M.process (n + 1))
      =ᵐ[μ] M.process n :=
  M.martingale n

end Martingale

/-
## 今後の拡張方針 (覚書)

1. `condExp` まわりの基本補題
   * 塔の性質 (`condExp μ ℱ m (condExp μ ℱ n f) = condExp μ ℱ m f`, `m ≤ n`)
   * 定数・線形性といった簡単な性質
2. `Martingale` の基本例
   * 定数過程
   * 適合過程の有限線形結合
3. `StoppingTime_MinLayer.lean` の停止過程 API との接続
   * 停止過程が依然として適合・可積分であるための sufficient condition
4. Optional stopping / Doob convergence へ着手
-/

end StructureTowerProbability
