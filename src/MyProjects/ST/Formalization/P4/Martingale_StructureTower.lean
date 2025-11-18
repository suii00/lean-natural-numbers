import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.LocallyIntegrable

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

/-- 以降の章では mathlib の `Filtration` をそのまま利用する（添字は ℕ）。 -/
abbrev Filtration (Ω : Type*) [m : MeasurableSpace Ω] :=
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
    (ℱ : Filtration Ω) (n : ℕ) (f : Ω → ℝ) : Ω → ℝ :=
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
  filtration : Filtration Ω
  process : Process Ω
  adapted :
      ∀ n, StronglyMeasurable[filtration n] (process n)
  integrable :
      ∀ n, Integrable (process n) μ
  martingale :
      ∀ n,
        condExp μ filtration n (process (n + 1))
          =ᵐ[μ] process n

namespace Martingale

variable {μ : Measure Ω} [IsFiniteMeasure μ]

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
