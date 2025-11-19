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

/-- 停止過程の増分を「元の増分か 0 か」で書いたもの。 -/
lemma stoppedProcess_succ_sub (M : Martingale μ) (τ : Ω → ℕ)
    (n : ℕ) (ω : Ω) :
    M.stoppedProcess τ (n + 1) ω - M.stoppedProcess τ n ω =
      (if τ ω ≤ n then 0
        else M.process (n + 1) ω - M.process n ω) := by
  classical
  by_cases h : τ ω ≤ n
  · have hconst :=
      M.stoppedProcess_const_of_ge (τ := τ)
        (n := n) (m := n + 1) (ω := ω) h (Nat.le_succ _)
    simpa [h, hconst] using sub_eq (M.stoppedProcess τ (n + 1) ω)
      (M.stoppedProcess τ n ω)
  · have hlt : n < τ ω := Nat.lt_of_not_ge h
    have hsucc : n + 1 ≤ τ ω := Nat.succ_le_of_lt hlt
    have hle : n ≤ τ ω := Nat.le_of_lt hlt
    have h₁ :=
      M.stoppedProcess_eq_of_le (τ := τ) (n := n + 1) (ω := ω) hsucc
    have h₂ :=
      M.stoppedProcess_eq_of_le (τ := τ) (n := n) (ω := ω) hle
    simp [h, h₁, h₂]

/-- 指示関数を用いた停止過程の増分表示。 -/
lemma stoppedProcess_increment_indicator (M : Martingale μ) (τ : Ω → ℕ)
    (n : ℕ) (ω : Ω) :
    M.stoppedProcess τ (n + 1) ω - M.stoppedProcess τ n ω =
      Set.indicator {ω | τ ω > n}
        (fun ω => M.process (n + 1) ω - M.process n ω) ω := by
  classical
  have h := M.stoppedProcess_succ_sub (τ := τ) (n := n) ω
  by_cases hτ : τ ω ≤ n
  · have : ω ∉ {ω : Ω | τ ω > n} := by
      simpa [Set.mem_setOf_eq, not_lt.mpr hτ]
    simpa [Set.indicator_of_notMem, this, hτ] using h
  · have : ω ∈ {ω : Ω | τ ω > n} := by
      simpa [Set.mem_setOf_eq] using not_le.mp hτ
    simpa [Set.indicator_of_mem, this, hτ] using h

/-- マルチンゲールの「マルチンゲール性」をそのまま取り出す補題。 -/
lemma condExp_next (M : Martingale μ) (n : ℕ) :
    condExp μ M.filtration n (M.process (n + 1))
      =ᵐ[μ] M.process n :=
  M.martingale n

/-- 停止過程の適合性。 -/
lemma stoppedProcess_adapted_of_measurableSets
    (M : Martingale μ) (τ : Ω → ℕ)
    (hτ :
      ∀ n, @MeasurableSet Ω (M.filtration n) {ω : Ω | τ ω ≤ n}) :
    MeasureTheory.Adapted M.filtration (M.stoppedProcess τ) := by
  classical
  intro n
  simpa [Martingale.stoppedProcess] using
    (StructureTowerProbability.stopped_stronglyMeasurable_of_stoppingSets
      (ℱ := M.filtration) (X := M.process) (hX := M.adapted)
      (τ := τ) (hτ := hτ) n)

/-- 有界停止時間のもとで停止過程が可積分であること。 -/
lemma stoppedProcess_integrable_of_bdd
    (M : Martingale μ) (τ : Ω → ℕ)
    (hτ :
      ∀ n, @MeasurableSet Ω (M.filtration n) {ω : Ω | τ ω ≤ n})
    (hτ_bdd : ∃ K, ∀ ω, τ ω ≤ K) :
    ∀ n, Integrable (M.stoppedProcess τ n) μ := by
  classical
  intro n
  simpa [Martingale.stoppedProcess] using
    (StructureTowerProbability.stopped_integrable_of_bdd
      (ℱ := M.filtration) (X := M.process)
      (hX := M.integrable) (τ := τ)
      (hτ := hτ) (hτ_bdd := hτ_bdd) n)

/-- 有界停止時間で止めた過程のマルチンゲール性。 -/
lemma stoppedProcess_martingale_property_of_bdd
    (M : Martingale μ) (τ : Ω → ℕ)
    (hτ :
      ∀ n, @MeasurableSet Ω (M.filtration n) {ω : Ω | τ ω ≤ n})
    (hτ_bdd : ∃ K, ∀ ω, τ ω ≤ K) :
    ∀ n,
      condExp μ M.filtration n (M.stoppedProcess τ (n + 1))
        =ᵐ[μ] M.stoppedProcess τ n := by
  classical
  have h_stop_strong :
      ∀ k,
        StronglyMeasurable[M.filtration k]
          (StructureTowerProbability.stopped M.process τ k) :=
    StructureTowerProbability.stopped_stronglyMeasurable_of_stoppingSets
      (ℱ := M.filtration) (X := M.process)
      (hX := M.adapted) (τ := τ) (hτ := hτ)
  have h_stop_int :
      ∀ k,
        Integrable (StructureTowerProbability.stopped M.process τ k) μ :=
    StructureTowerProbability.stopped_integrable_of_bdd
      (ℱ := M.filtration) (X := M.process)
      (hX := M.integrable) (τ := τ) (hτ := hτ) (hτ_bdd := hτ_bdd)
  intro n
  have h_stop_int_n := h_stop_int n
  have h_stop_int_succ := h_stop_int (n + 1)
  have h_diff_int :
      Integrable
        (fun ω =>
          M.stoppedProcess τ (n + 1) ω - M.stoppedProcess τ n ω) μ :=
    h_stop_int_succ.sub h_stop_int_n
  have h_cond_split :
      condExp μ M.filtration n (M.stoppedProcess τ (n + 1)) =ᵐ[μ]
        condExp μ M.filtration n (M.stoppedProcess τ n) +
          condExp μ M.filtration n
            (fun ω =>
              M.stoppedProcess τ (n + 1) ω - M.stoppedProcess τ n ω) := by
    have h_add :=
      (MeasureTheory.condExp_add
          (μ := μ) (m := M.filtration n)
          (hf := h_stop_int_n) (hg := h_diff_int))
    have h_sum :
        (fun ω =>
            M.stoppedProcess τ n ω +
              (M.stoppedProcess τ (n + 1) ω - M.stoppedProcess τ n ω)) =
          fun ω => M.stoppedProcess τ (n + 1) ω := by
      funext ω; simp
    have h_sum_ae :
        (fun ω =>
            M.stoppedProcess τ n ω +
              (M.stoppedProcess τ (n + 1) ω - M.stoppedProcess τ n ω)) =ᵐ[μ]
          fun ω => M.stoppedProcess τ (n + 1) ω :=
      Filter.EventuallyEq.of_eq h_sum
    have h_congr :=
      MeasureTheory.condExp_congr_ae
        (μ := μ) (m := M.filtration n) h_sum_ae
    exact h_congr.symm.trans h_add
  have h_stop_meas :
      StronglyMeasurable[M.filtration n] (M.stoppedProcess τ n) := by
    simpa [Martingale.stoppedProcess] using h_stop_strong n
  have h_cond_stop_eq :
      condExp μ M.filtration n (M.stoppedProcess τ n)
        = M.stoppedProcess τ n :=
    MeasureTheory.condExp_of_stronglyMeasurable
      (hm := M.filtration.le n)
      (hf := h_stop_meas)
      (hfi := h_stop_int_n)
  have h_cond_stop :
      condExp μ M.filtration n (M.stoppedProcess τ n)
        =ᵐ[μ] M.stoppedProcess τ n :=
    Filter.EventuallyEq.of_eq h_cond_stop_eq
  have h_diff_fun :
      (fun ω =>
          M.stoppedProcess τ (n + 1) ω - M.stoppedProcess τ n ω)
        = fun ω =>
            Set.indicator {ω : Ω | τ ω > n}
              (fun ω => M.process (n + 1) ω - M.process n ω) ω := by
    funext ω
    simpa [Martingale.stoppedProcess] using
      (Martingale.stoppedProcess_increment_indicator
        (M := M) (τ := τ) (n := n) (ω := ω))
  have h_meas :
      @MeasurableSet Ω (M.filtration n)
        {ω : Ω | τ ω > n} := by
    have h_le := hτ n
    have h_eq :
        {ω : Ω | τ ω > n}
          = ({ω : Ω | τ ω ≤ n})ᶜ := by
      ext ω; simp [Set.mem_setOf_eq, not_le]
    simpa [h_eq] using h_le.compl
  have hΔ_int :
      Integrable
        (fun ω => M.process (n + 1) ω - M.process n ω) μ :=
    (M.integrable (n + 1)).sub (M.integrable n)
  have h_cond_sub :
      condExp μ M.filtration n
          (fun ω => M.process (n + 1) ω - M.process n ω)
        =ᵐ[μ]
          condExp μ M.filtration n (M.process (n + 1)) -
            condExp μ M.filtration n (M.process n) := by
    simpa [condExp] using
      (MeasureTheory.condExp_sub
        (μ := μ) (m := M.filtration n)
        (hf := M.integrable (n + 1))
        (hg := M.integrable n))
  have h_cond_proc_eq :
      condExp μ M.filtration n (M.process n) = M.process n :=
    MeasureTheory.condExp_of_stronglyMeasurable
      (hm := M.filtration.le n)
      (hf := M.adapted n)
      (hfi := M.integrable n)
  have h_cond_proc :
      condExp μ M.filtration n (M.process n) =ᵐ[μ] M.process n :=
    Filter.EventuallyEq.of_eq h_cond_proc_eq
  have hΔ_cond :
      condExp μ M.filtration n
          (fun ω => M.process (n + 1) ω - M.process n ω)
        =ᵐ[μ] 0 := by
    refine h_cond_sub.trans ?_
    have h_diff_zero :
        (fun ω =>
            condExp μ M.filtration n (M.process (n + 1)) ω +
              (-condExp μ M.filtration n (M.process n) ω))
          =ᵐ[μ]
            fun ω => M.process n ω + (-M.process n ω) := by
      refine (M.martingale n).add ?_
      have h_cond_proc_neg :
          (fun ω => -condExp μ M.filtration n (M.process n) ω)
            =ᵐ[μ] fun ω => -M.process n ω := by
        exact h_cond_proc.neg
      exact h_cond_proc_neg
    have h_zero_eq :
        (fun ω => M.process n ω + (-M.process n ω))
          = fun _ => 0 := by
      funext ω; simp
    have h_zero :
        (fun ω => M.process n ω + (-M.process n ω)) =ᵐ[μ] fun _ => 0 := by
      refine Filter.EventuallyEq.of_eq ?_
      exact h_zero_eq
    exact h_diff_zero.trans h_zero
  have h_indicator :
      condExp μ M.filtration n
          (fun ω =>
            Set.indicator {ω : Ω | τ ω > n}
              (fun ω => M.process (n + 1) ω - M.process n ω) ω)
        =ᵐ[μ]
          fun ω =>
            Set.indicator {ω : Ω | τ ω > n}
              (fun ω =>
                condExp μ M.filtration n
                  (fun ω =>
                    M.process (n + 1) ω - M.process n ω) ω) ω := by
    simpa [condExp] using
      (MeasureTheory.condExp_indicator
        (μ := μ) (m := M.filtration n)
        (hf_int := hΔ_int) (hs := h_meas))
  have h_cond_delta :
      condExp μ M.filtration n
          (fun ω =>
            M.stoppedProcess τ (n + 1) ω - M.stoppedProcess τ n ω)
        =ᵐ[μ] 0 := by
    have h_delta' :
        condExp μ M.filtration n
            (fun ω =>
              M.stoppedProcess τ (n + 1) ω - M.stoppedProcess τ n ω)
          =ᵐ[μ]
            condExp μ M.filtration n
              (fun ω =>
                Set.indicator {ω : Ω | τ ω > n}
                  (fun ω =>
                    M.process (n + 1) ω - M.process n ω) ω) := by
      refine condExp_congr_ae ?_
      simpa [h_diff_fun]
    refine h_delta'.trans ?_
    refine h_indicator.trans ?_
    have h_indicator_zero :
        (fun ω =>
            Set.indicator {ω : Ω | τ ω > n}
              (fun ω =>
                condExp μ M.filtration n
                  (fun ω =>
                    M.process (n + 1) ω - M.process n ω) ω) ω)
          =ᵐ[μ]
            fun ω =>
              Set.indicator {ω : Ω | τ ω > n}
                (fun _ : Ω => (0 : ℝ)) ω := by
      refine hΔ_cond.mono ?_
      intro ω hω
      by_cases hmem : ω ∈ {ω : Ω | τ ω > n}
      · simp [Set.indicator_of_mem, hmem, hω]
      · simp [Set.indicator_of_notMem, hmem]
    have h_indicator_zero_eq :
        (fun ω =>
            Set.indicator {ω : Ω | τ ω > n}
              (fun _ : Ω => (0 : ℝ)) ω)
          = fun _ => 0 := by
      funext ω
      by_cases hmem : ω ∈ {ω : Ω | τ ω > n}
      · simp [Set.indicator_of_mem, hmem]
      · simp [Set.indicator_of_notMem, hmem]
    have h_indicator_zero' :
        (fun ω =>
          Set.indicator {ω : Ω | τ ω > n}
            (fun _ : Ω => (0 : ℝ)) ω)
          =ᵐ[μ] fun _ => 0 := by
      refine Filter.EventuallyEq.of_eq ?_
      exact h_indicator_zero_eq
    exact h_indicator_zero.trans h_indicator_zero'
  have h_rhs :
      (fun ω =>
          condExp μ M.filtration n (M.stoppedProcess τ n) ω +
            condExp μ M.filtration n
              (fun ω => M.stoppedProcess τ (n + 1) ω - M.stoppedProcess τ n ω) ω)
        =ᵐ[μ] M.stoppedProcess τ n := by
    have h_sum := (h_cond_stop.add h_cond_delta)
    refine h_sum.trans ?_
    have h_final :
        (fun ω => M.stoppedProcess τ n ω + 0) =
          fun ω => M.stoppedProcess τ n ω := by
      funext ω; simp
    exact Filter.EventuallyEq.of_eq h_final
  exact h_cond_split.trans h_rhs

/-- 定数停止時間 `τ ≡ 0` で止めた過程は常に `M.process 0` に等しい。 -/
lemma stoppedProcess_const_zero (M : Martingale μ) :
    ∀ n ω, M.stoppedProcess (fun _ => 0) n ω = M.process 0 ω := by
  intro n ω
  have h_fix :
      M.stoppedProcess (fun _ => 0) 0 ω = M.process 0 ω := by
    simpa using
      (M.stoppedProcess_eq_of_le (τ := fun _ => 0)
        (n := 0) (ω := ω) (Nat.le_of_eq rfl))
  have h_const :
      M.stoppedProcess (fun _ => 0) n ω =
        M.stoppedProcess (fun _ => 0) 0 ω := by
    simpa using
      (M.stoppedProcess_const_of_ge (τ := fun _ => 0)
        (n := 0) (m := n) (ω := ω)
        (by exact Nat.le_of_eq rfl) (Nat.zero_le n))
  simpa [h_const] using h_fix

/-- 定数停止時間の可測性（集合は自明）。 -/
lemma measurableSet_constStopping (M : Martingale μ) (K n : ℕ) :
    @MeasurableSet Ω (M.filtration n)
      {ω : Ω | (fun _ : Ω => K) ω ≤ n} := by
  classical
  by_cases h : K ≤ n
  · have hset :
        {ω : Ω | (fun _ : Ω => K) ω ≤ n} = (Set.univ : Set Ω) := by
      ext ω; simp [h]
    simpa [hset] using (MeasurableSet.univ :
      @MeasurableSet Ω (M.filtration n) Set.univ)
  · have hset :
        {ω : Ω | (fun _ : Ω => K) ω ≤ n} = (∅ : Set Ω) := by
      ext ω; simp [h]
    simpa [hset] using (MeasurableSet.empty :
      @MeasurableSet Ω (M.filtration n) (∅ : Set Ω))

/-- 定数停止時間は自明に有界。 -/
lemma constStopping_bdd (K : ℕ) :
    ∃ L : ℕ, ∀ ω : Ω, (fun _ : Ω => K) ω ≤ L :=
  ⟨K, by intro ω; exact le_rfl⟩

lemma stoppedProcess_stronglyMeasurable_of_stoppingSets
    (M : Martingale μ)
    (τ : Ω → ℕ)
    (hτ :
      ∀ n, @MeasurableSet Ω (M.filtration n) {ω : Ω | τ ω ≤ n}) :
  ∀ n,
    StronglyMeasurable[M.filtration n]
      (M.stoppedProcess τ n) := by
  classical
  -- P3 の bridge lemma そのまま利用
  have h_stop_strong :
    ∀ n,
      StronglyMeasurable[M.filtration n]
        (StructureTowerProbability.stopped M.process τ n) :=
    StructureTowerProbability.stopped_stronglyMeasurable_of_stoppingSets
      (ℱ := M.filtration) (X := M.process)
      (hX := M.adapted) (τ := τ) (hτ := hτ)
  intro n
  -- stoppedProcess が P3 の stopped のラッパであることを使って書き換え
  simpa [Martingale.stoppedProcess] using h_stop_strong n

/-- 有界停止時間で止めた過程がマルチンゲール性を満たすこと（本体）。 -/
lemma stoppedProcess_martingaleProperty_of_bdd
    (M : Martingale μ)
    (τ : Ω → ℕ)
    (hτ :
      ∀ n, @MeasurableSet Ω (M.filtration n) {ω : Ω | τ ω ≤ n})
    (hτ_bdd : ∃ K, ∀ ω, τ ω ≤ K) :
  ∀ n,
    condExp μ M.filtration n
      (M.stoppedProcess τ (n + 1)) =ᵐ[μ]
    M.stoppedProcess τ n := by
  classical
  simpa using
    (stoppedProcess_martingale_property_of_bdd
      (M := M) (τ := τ) (hτ := hτ) (hτ_bdd := hτ_bdd))


/-- 有界停止時間で止めたマルチンゲールは再びマルチンゲールになる。 -/
noncomputable def stoppedProcess_martingale_of_bdd
    (M : Martingale μ)
    (τ : Ω → ℕ)
    (hτ :
      ∀ n, @MeasurableSet Ω (M.filtration n) {ω : Ω | τ ω ≤ n})
    (hτ_bdd : ∃ K, ∀ ω, τ ω ≤ K) :
  Martingale μ :=
by
  classical
  refine
    { filtration := M.filtration
      , process    := M.stoppedProcess τ
      , adapted    := M.stoppedProcess_stronglyMeasurable_of_stoppingSets τ hτ
      , integrable := M.stoppedProcess_integrable_of_bdd τ hτ hτ_bdd
      , martingale := M.stoppedProcess_martingaleProperty_of_bdd τ hτ hτ_bdd }

/-- `stoppedProcess_martingale_of_bdd` を `τ ≡ 0` に適用したときの sanity check。 -/
lemma stoppedProcess_martingale_of_bdd_zero_process
    (M : Martingale μ) :
    ∀ (n : ℕ) (ω : Ω),
      (stoppedProcess_martingale_of_bdd (M := M) (τ := fun _ => 0)
          (hτ :=
            measurableSet_constStopping (M := M) (K := 0))
          (hτ_bdd := constStopping_bdd (K := 0))).process n ω
        = M.process 0 ω := by
  intro n ω
  change M.stoppedProcess (fun _ => 0) n ω = M.process 0 ω
  simpa using (stoppedProcess_const_zero (M := M) n ω)

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
