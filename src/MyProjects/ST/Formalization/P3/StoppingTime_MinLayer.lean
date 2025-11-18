import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
import Mathlib.Probability.Process.Filtration
import MyProjects.ST.Formalization.P2.SigmaAlgebraTower_Skeleton

/-!
# StoppingTime_MinLayer

このモジュールは構造塔アプローチで停止時間を扱うための最小骨格を提供する。

* 構造塔 `StructureTowerMin` とフィルトレーション `SigmaAlgebraFiltrationWithCovers` の橋渡し
* 停止時間/停止集合/停止 σ-代数/停止フィルトレーション核の定義
* 後続の optional stopping に向けた停止過程 `stopped` の純粋関数レベル定義

`SigmaAlgebraTower_Skeleton.lean` で構築したフィルトレーション/構造塔を
停止時間へ適用する最初のステップ。
このモジュールは optional stopping 章から参照される基盤 API 集である。

GPT4.md の方針:

1. フィルトレーションの上で停止時間を再定義
2. 構造塔の層 `layer n` と停止集合 `{τ ≤ n}` を直接結びつける
3. `minLayer` による「単点が初めて可測になる時刻」を導入

まだ多くの証明は未実装（`TODO` コメント付の `sorry`）。
-/

open scoped Classical
open Set MeasureTheory
open StructureTowerProbability

namespace StructureTowerProbability

/-- フィルトレーション型の alias。 -/
abbrev Filtration (Ω : Type*) [MeasurableSpace Ω] :=
  SigmaAlgebraFiltrationWithCovers (Ω := Ω)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- フィルトレーションを構造塔に昇格する。 -/
noncomputable def towerOf (ℱ : Filtration Ω) :
    StructureTowerMin (Set Ω) ℕ :=
  SigmaAlgebraFiltrationWithCovers.FiltrationToTower (Ω := Ω) ℱ

/-- 古典的停止時間。 -/
structure StoppingTime (ℱ : Filtration Ω) where
  τ : Ω → ℕ
  measurable : ∀ n, @MeasurableSet Ω (ℱ.base.𝓕 n) {ω | τ ω ≤ n}

/-- 停止集合 {τ ≤ n} は構造塔 `layer n` に属する。 -/
lemma stopping_sets_in_tower (ℱ : Filtration Ω)
    (τ : StoppingTime ℱ) (n : ℕ) :
    {ω : Ω | τ.τ ω ≤ n} ∈ (towerOf (Ω := Ω) ℱ).layer n := by
  change @MeasurableSet Ω (ℱ.base.𝓕 n) {ω : Ω | τ.τ ω ≤ n}
  exact τ.measurable n

/-- 単点 {ω} が初めて可測になる時刻。 -/
noncomputable def firstMeasurableTime (ℱ : Filtration Ω) (ω : Ω) : ℕ :=
  (towerOf (Ω := Ω) ℱ).minLayer {ω}

/-- 単点は first measurable time で可測。 -/
theorem singleton_measurable_at_first_time (ℱ : Filtration Ω) (ω : Ω) :
    @MeasurableSet Ω (ℱ.base.𝓕 (firstMeasurableTime ℱ ω)) {ω} := by
  unfold firstMeasurableTime
  exact (towerOf (Ω := Ω) ℱ).minLayer_mem {ω}

/-- first measurable time の極小性。 -/
theorem first_measurable_time_minimal (ℱ : Filtration Ω) (ω : Ω)
    (n : ℕ) (h : @MeasurableSet Ω (ℱ.base.𝓕 n) {ω}) :
    firstMeasurableTime ℱ ω ≤ n := by
  unfold firstMeasurableTime
  exact (towerOf (Ω := Ω) ℱ).minLayer_minimal {ω} n h

/-- 停止時間の値は自明に自身と一致する（placeholder）。 -/
theorem stopping_time_respects_minLayer (ℱ : Filtration Ω)
    (τ : StoppingTime ℱ) (ω : Ω) : τ.τ ω = τ.τ ω := rfl

/-- 停止 σ-代数（補題は TODO）。 -/
def StoppedSigmaAlgebra (ℱ : Filtration Ω) (τ : StoppingTime ℱ) :
    MeasurableSpace Ω where
  MeasurableSet' A :=
    ∀ n, @MeasurableSet Ω (ℱ.base.𝓕 n) (A ∩ {ω | τ.τ ω ≤ n})
  measurableSet_empty := by
    intro n; simp
  measurableSet_compl := by
    classical
    intro A hA n
    have hτ : @MeasurableSet Ω (ℱ.base.𝓕 n) {ω | τ.τ ω ≤ n} :=
      τ.measurable n
    have hA' : @MeasurableSet Ω (ℱ.base.𝓕 n) (A ∩ {ω | τ.τ ω ≤ n}) :=
      hA n
    have hDiff :
        @MeasurableSet Ω (ℱ.base.𝓕 n)
          ({ω | τ.τ ω ≤ n} \ (A ∩ {ω | τ.τ ω ≤ n})) :=
      hτ.diff hA'
    have hEq :
        Aᶜ ∩ {ω | τ.τ ω ≤ n}
          = ({ω | τ.τ ω ≤ n} \ (A ∩ {ω | τ.τ ω ≤ n})) := by
      ext ω; constructor
      · intro hω
        refine ⟨hω.2, ?_⟩
        intro hmem
        have hnot : ω ∉ A := hω.1
        exact hnot hmem.1
      · intro hω
        refine ⟨?_, hω.1⟩
        intro hAω
        apply hω.2
        exact ⟨hAω, hω.1⟩
    simpa [hEq] using hDiff
  measurableSet_iUnion := by
    classical
    intro f hf n
    have hUnion :
        @MeasurableSet Ω (ℱ.base.𝓕 n)
          (⋃ i, f i ∩ {ω | τ.τ ω ≤ n}) :=
      by
        apply MeasurableSet.iUnion
        intro i
        exact hf i n
    have hEq :
        (⋃ i, f i) ∩ {ω | τ.τ ω ≤ n}
          = ⋃ i, f i ∩ {ω | τ.τ ω ≤ n} := by
      ext ω; constructor
      · rintro ⟨hUnionMem, hτ⟩
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hUnionMem
        exact Set.mem_iUnion.mpr ⟨i, ⟨hi, hτ⟩⟩
      · intro hω
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hω
        exact ⟨Set.mem_iUnion.mpr ⟨i, hi.1⟩, hi.2⟩
    simpa [hEq] using hUnion

/-- Stopped σ-代数の定義を展開するための便利な同値。 -/
lemma mem_stoppedSigma_iff (ℱ : Filtration Ω)
    (τ : StoppingTime ℱ) (A : Set Ω) :
    (StoppedSigmaAlgebra ℱ τ).MeasurableSet' A
      ↔ ∀ n, @MeasurableSet Ω (ℱ.base.𝓕 n) (A ∩ {ω | τ.τ ω ≤ n}) :=
  Iff.rfl

/-- 停止集合自身も停止 σ-代数に属する。 -/
lemma stoppingSet_mem_stoppedSigma (ℱ : Filtration Ω)
    (τ : StoppingTime ℱ) (n : ℕ) :
    (StoppedSigmaAlgebra ℱ τ).MeasurableSet' {ω : Ω | τ.τ ω ≤ n} := by
  intro k
  have hEq :
      {ω : Ω | τ.τ ω ≤ n} ∩ {ω : Ω | τ.τ ω ≤ k}
        = {ω : Ω | τ.τ ω ≤ Nat.min n k} := by
    ext ω; constructor
    · rintro ⟨h1, h2⟩
      exact (Nat.le_min).mpr ⟨h1, h2⟩
    · intro hω
      exact ⟨le_trans hω (Nat.min_le_left _ _),
        le_trans hω (Nat.min_le_right _ _)⟩
  have hmin :
      @MeasurableSet Ω (ℱ.base.𝓕 (Nat.min n k))
        {ω : Ω | τ.τ ω ≤ Nat.min n k} :=
    τ.measurable (Nat.min n k)
  have hmono :
      ℱ.base.𝓕 (Nat.min n k) ≤ ℱ.base.𝓕 k :=
    ℱ.base.mono (Nat.min_le_right _ _)
  have hmeas : @MeasurableSet Ω (ℱ.base.𝓕 k)
      {ω : Ω | τ.τ ω ≤ Nat.min n k} :=
    hmono _ hmin
  simpa [hEq] using hmeas

/-- 停止時間が大きいほど停⽌ σ-代数も大きくなる。 -/
lemma stoppedSigma_le_of_pointwise_le (ℱ : Filtration Ω)
    {τ₁ τ₂ : StoppingTime ℱ}
    (hτ : ∀ ω, τ₁.τ ω ≤ τ₂.τ ω) :
    StoppedSigmaAlgebra ℱ τ₁ ≤ StoppedSigmaAlgebra ℱ τ₂ := by
  intro A hA n
  have hτ₂ : @MeasurableSet Ω (ℱ.base.𝓕 n) {ω | τ₂.τ ω ≤ n} :=
    τ₂.measurable n
  have hsubset :
      {ω : Ω | τ₂.τ ω ≤ n} ⊆ {ω : Ω | τ₁.τ ω ≤ n} := by
    intro ω hω
    exact le_trans (hτ ω) hω
  have hEq :
      A ∩ {ω : Ω | τ₂.τ ω ≤ n}
        = (A ∩ {ω : Ω | τ₁.τ ω ≤ n})
          ∩ {ω : Ω | τ₂.τ ω ≤ n} := by
    ext ω; constructor
    · intro hω
      refine ⟨⟨hω.1, hsubset hω.2⟩, hω.2⟩
    · intro hω
      exact ⟨hω.1.1, hω.2⟩
  have hinter :
      @MeasurableSet Ω (ℱ.base.𝓕 n)
        ((A ∩ {ω : Ω | τ₁.τ ω ≤ n})
          ∩ {ω : Ω | τ₂.τ ω ≤ n}) :=
    (hA n).inter hτ₂
  simpa [hEq] using hinter

/-- 切り詰め停止時間 `τ ∧ n`。 -/
def truncateStoppingTime (ℱ : Filtration Ω) (τ : StoppingTime ℱ)
    (n : ℕ) : StoppingTime ℱ :=
{ τ := fun ω ↦ Nat.min (τ.τ ω) n
  measurable := by
    intro k
    classical
    by_cases hk : k < n
    · have hk' : ¬ n ≤ k := Nat.not_le_of_gt hk
      have hEq :
          {ω : Ω | (τ.τ ω).min n ≤ k}
            = {ω : Ω | τ.τ ω ≤ k} := by
        ext ω; constructor
        · intro hω
          have hcases := le_total (τ.τ ω) n
          cases hcases with
          | inl hτn =>
              have hmin : (τ.τ ω).min n ≤ k := hω
              have : τ.τ ω ≤ k := by
                simpa [min_eq_left hτn] using hmin
              exact this
          | inr hnτ =>
              have hmin : (τ.τ ω).min n ≤ k := hω
              have : n ≤ k := by
                simpa [min_eq_right hnτ] using hmin
              exact (hk' this).elim
        · intro hω
          exact le_trans (min_le_left (τ.τ ω) n) hω
      have hrewrite :
          @MeasurableSet Ω (ℱ.base.𝓕 k) {ω : Ω | τ.τ ω ≤ k}
            = @MeasurableSet Ω (ℱ.base.𝓕 k)
                {ω : Ω | (τ.τ ω).min n ≤ k} :=
        congrArg
          (fun s => @MeasurableSet Ω (ℱ.base.𝓕 k) s) hEq.symm
      exact hrewrite ▸ τ.measurable k
    · have hnk : n ≤ k := Nat.le_of_not_gt hk
      have hEq :
          {ω : Ω | (τ.τ ω).min n ≤ k} = Set.univ := by
        ext ω; constructor
        · intro _; trivial
        · intro _; exact le_trans (min_le_right (τ.τ ω) n) hnk
      have hrewrite :
          @MeasurableSet Ω (ℱ.base.𝓕 k) (Set.univ : Set Ω)
            = @MeasurableSet Ω (ℱ.base.𝓕 k)
                {ω : Ω | (τ.τ ω).min n ≤ k} :=
        congrArg
          (fun s => @MeasurableSet Ω (ℱ.base.𝓕 k) s) hEq.symm
      exact hrewrite ▸ (MeasurableSet.univ :
        @MeasurableSet Ω (ℱ.base.𝓕 k) Set.univ) }

/-- `τ ∧ n` は `τ ∧ m` 以下で単調。 -/
lemma truncateStoppingTime_le (ℱ : Filtration Ω) (τ : StoppingTime ℱ)
    {n m : ℕ} (hnm : n ≤ m) :
    ∀ ω, (truncateStoppingTime ℱ τ n).τ ω
        ≤ (truncateStoppingTime ℱ τ m).τ ω := by
  intro ω
  dsimp [truncateStoppingTime]
  simpa using min_le_min le_rfl hnm

/-- 停止時間 `τ` に対応する停止フィルトレーションの「核」。
`Gₙ := StoppedSigmaAlgebra ℱ (τ ∧ n)` だけを保持し、covers は要求しない。 -/
def stoppedFiltrationCore (ℱ : Filtration Ω) (τ : StoppingTime ℱ) :
    SigmaAlgebraFiltration.Core (Ω := Ω) (ι := ℕ) where
  𝓕 n := StoppedSigmaAlgebra ℱ (truncateStoppingTime ℱ τ n)
  mono := by
    intro n m hnm
    refine
      stoppedSigma_le_of_pointwise_le (ℱ := ℱ)
        (τ₁ := truncateStoppingTime ℱ τ n)
        (τ₂ := truncateStoppingTime ℱ τ m) ?_
    intro ω
    exact truncateStoppingTime_le (ℱ := ℱ) (τ := τ) hnm ω

/-- 停止フィルトレーション(核)の各層は元のフィルトレーションに含まれる。 -/
lemma stoppedFiltrationCore_le (ℱ : Filtration Ω) (τ : StoppingTime ℱ) :
    ∀ n, (stoppedFiltrationCore ℱ τ).𝓕 n ≤ ℱ.base.𝓕 n := by
  intro n A hA
  change
      (StoppedSigmaAlgebra ℱ (truncateStoppingTime ℱ τ n)).MeasurableSet' A at hA
  have hset : {ω : Ω | (truncateStoppingTime ℱ τ n).τ ω ≤ n} = Set.univ := by
    ext ω; constructor
    · intro _; trivial
    · intro _; exact Nat.min_le_right _ _
  have hmeas :
      @MeasurableSet Ω (ℱ.base.𝓕 n)
        (A ∩ {ω : Ω | (truncateStoppingTime ℱ τ n).τ ω ≤ n}) :=
    hA n
  simpa [hset] using hmeas

/-- 停止集合 `{τ ≤ n}` は停止フィルトレーション核の層 `n` で可測。 -/
lemma stoppingSet_measurable_in_stoppedFiltrationCore (ℱ : Filtration Ω)
    (τ : StoppingTime ℱ) (n : ℕ) :
    @MeasurableSet Ω ((stoppedFiltrationCore ℱ τ).𝓕 n)
        {ω : Ω | τ.τ ω ≤ n} := by
  change
      (StoppedSigmaAlgebra ℱ (truncateStoppingTime ℱ τ n)).MeasurableSet'
        {ω : Ω | τ.τ ω ≤ n}
  intro k
  classical
  by_cases hk : k < n
  · have hk' : ¬ n ≤ k := Nat.not_le_of_gt hk
    have hEq :
        {ω : Ω | τ.τ ω ≤ n} ∩
            {ω : Ω | (truncateStoppingTime ℱ τ n).τ ω ≤ k}
          = {ω : Ω | τ.τ ω ≤ k} := by
      ext ω; constructor
      · rintro ⟨hτn, hmin⟩
        dsimp [truncateStoppingTime] at hmin
        have hcases := le_total (τ.τ ω) n
        cases hcases with
        | inl hτle =>
            have : τ.τ ω ≤ k := by
              simpa [Nat.min_eq_left hτle] using hmin
            exact this
        | inr hnle =>
            have : n ≤ k := by
              simpa [Nat.min_eq_right hnle] using hmin
            exact (hk' this).elim
      · intro hτk
        refine ⟨le_trans hτk (le_of_lt hk), ?_⟩
        dsimp [truncateStoppingTime]
        exact le_trans (Nat.min_le_left _ _) hτk
    simpa [hEq] using τ.measurable k
  · have hnk : n ≤ k := Nat.le_of_not_gt hk
    have hEq :
        {ω : Ω | τ.τ ω ≤ n} ∩
            {ω : Ω | (truncateStoppingTime ℱ τ n).τ ω ≤ k}
          = {ω : Ω | τ.τ ω ≤ n} := by
      ext ω; constructor
      · intro hω; exact hω.1
      · intro hω
        refine ⟨hω, ?_⟩
        dsimp [truncateStoppingTime]
        exact le_trans (Nat.min_le_right _ _) hnk
    have hmeas :
        @MeasurableSet Ω (ℱ.base.𝓕 n) {ω : Ω | τ.τ ω ≤ n} :=
      τ.measurable n
    have hmeas' :
        @MeasurableSet Ω (ℱ.base.𝓕 k) {ω : Ω | τ.τ ω ≤ n} :=
      ℱ.base.mono hnk _ hmeas
    simpa [hEq] using hmeas'

/-- 停止過程（純粋に関数レベルの定義）。 -/
def stopped {β : Type*} (X : ℕ → Ω → β) (τ : Ω → ℕ) :
    ℕ → Ω → β :=
  fun n ω => X (Nat.min n (τ ω)) ω

/-- 停止時刻より前では元の過程と一致する。 -/
lemma stopped_eq_of_le {β : Type*} (X : ℕ → Ω → β) (τ : Ω → ℕ)
    {n : ℕ} {ω : Ω} (hn : n ≤ τ ω) :
    stopped X τ n ω = X n ω := by
  simp [stopped, Nat.min_eq_left hn]

/-- 停止時刻以降では値が固定される。 -/
lemma stopped_const_of_ge {β : Type*} (X : ℕ → Ω → β) (τ : Ω → ℕ)
    {n m : ℕ} {ω : Ω} (hτ : τ ω ≤ n) (hnm : n ≤ m) :
    stopped X τ m ω = stopped X τ n ω := by
  have hτm : τ ω ≤ m := le_trans hτ hnm
  simp [stopped, Nat.min_eq_right hτ, Nat.min_eq_right hτm]

/-- 停止時刻そのものの値 `X (τ ω)`. -/
def atStoppingTime {β : Type*} (X : ℕ → Ω → β) (τ : Ω → ℕ) : Ω → β :=
  fun ω => X (τ ω) ω

/-- 停止過程を停止時刻以上で評価すると `atStoppingTime` と一致。 -/
lemma stopped_eq_atStoppingTime {β : Type*} (X : ℕ → Ω → β) (τ : Ω → ℕ)
    {N : ℕ} {ω : Ω} (hN : τ ω ≤ N) :
    stopped X τ N ω = atStoppingTime X τ ω := by
  simp [stopped, atStoppingTime, Nat.min_eq_right hN]

/-- 停止過程をラップする薄い構造体。 -/
structure StoppedProcess (ℱ : Filtration Ω) (β : Type*) where
  /-- 元の過程。 -/
  X : ℕ → Ω → β
  /-- 停止時間。 -/
  τ : StoppingTime ℱ

namespace StoppedProcess

variable {ℱ : Filtration Ω} {β : Type*}

/-- 停止過程の値。 -/
def value (SP : StoppedProcess ℱ β) : ℕ → Ω → β :=
  stopped SP.X SP.τ.τ

/-- 停止時刻での値。 -/
def valueAt (SP : StoppedProcess ℱ β) : Ω → β :=
  atStoppingTime SP.X SP.τ.τ

/-- 停止前では元の過程と一致。 -/
lemma eq_before_stopping (SP : StoppedProcess ℱ β)
    {n : ℕ} {ω : Ω} (hn : n ≤ SP.τ.τ ω) :
    SP.value n ω = SP.X n ω := by
  unfold value
  exact stopped_eq_of_le SP.X SP.τ.τ hn

/-- 停止後は値が固定される。 -/
lemma const_after_stopping (SP : StoppedProcess ℱ β)
    {n m : ℕ} {ω : Ω} (hτ : SP.τ.τ ω ≤ n) (hnm : n ≤ m) :
    SP.value m ω = SP.value n ω := by
  unfold value
  exact stopped_const_of_ge SP.X SP.τ.τ hτ hnm

/-- 停止時刻での値と一致する。 -/
lemma value_eq_valueAt_of_le (SP : StoppedProcess ℱ β)
    {N : ℕ} {ω : Ω} (hN : SP.τ.τ ω ≤ N) :
    SP.value N ω = SP.valueAt ω := by
  unfold value valueAt
  exact stopped_eq_atStoppingTime SP.X SP.τ.τ hN

end StoppedProcess

/-
## 測度論モジュールとの橋渡し (下準備)

`StoppingTime_MinLayer` は構造塔と停止時間の骨格を担う一方、P4 側では
mathlib 標準のフィルトレーション/過程（`MeasureTheory.Filtration`、`Adapted`）を扱う。
そこで、停止過程 `stopped` が可測性・可積分性を保つという命題の**型**だけを先に配置し、
証明は今後の optional stopping 章で埋める方針とする。
-/
section MeasureBridge

open MeasureTheory

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω}

/-- TODO(bridge_adapted): 停止時集合 `{τ ≤ n}` の可測性から、停止過程も適合
(`StronglyMeasurable` 版) であることを示す。 -/
lemma stopped_stronglyMeasurable_of_stoppingSets
    (ℱ : MeasureTheory.Filtration ℕ m)
    (X : ℕ → Ω → ℝ)
    (hX : ∀ n, StronglyMeasurable[ℱ n] (X n))
    (τ : Ω → ℕ)
    (hτ : ∀ n, @MeasurableSet Ω (ℱ n) {ω : Ω | τ ω ≤ n}) :
    ∀ n, StronglyMeasurable[ℱ n]
      (StructureTowerProbability.stopped X τ n) := by
  -- TODO(bridge_adapted): 分割 `{τ = k}`・`{τ > n}` による有限貼り合わせで証明する。
  sorry

/-- TODO(bridge_integrable): 有界停止時間の仮定から停止過程の各時刻が Integrable
であることを示す。 -/
lemma stopped_integrable_of_bdd
    (X : ℕ → Ω → ℝ)
    (hX : ∀ n, Integrable (X n) μ)
    (τ : Ω → ℕ) (hτ_bdd : ∃ K, ∀ ω, τ ω ≤ K) :
    ∀ n, Integrable (StructureTowerProbability.stopped X τ n) μ := by
  -- TODO(bridge_integrable): `{τ = k}` ごとの有限和表示を使って証明する。
  sorry

end MeasureBridge

/-! ## TODO: 停止過程・オプショナル停止への接続 -/

/-
- StoppingTime 由来の σ-代数 `StoppedSigmaAlgebra` の補題を完成させる
- `towerOf ℱ` の `minLayer` を使って停止時間を再構成する
- 停止過程/マルチンゲールの骨格を追加
-/

end StructureTowerProbability

/-! ## 使用例 (雛形) -/

example {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : StructureTowerProbability.Filtration Ω)
    (ω : Ω) :
    @MeasurableSet Ω (ℱ.base.𝓕
      (StructureTowerProbability.firstMeasurableTime ℱ ω)) {ω} := by
  simpa using
    StructureTowerProbability.singleton_measurable_at_first_time
      (Ω := Ω) ℱ ω

example {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : StructureTowerProbability.Filtration Ω)
    (τ : StructureTowerProbability.StoppingTime ℱ)
    (n : ℕ) :
    @MeasurableSet Ω
        ((StructureTowerProbability.stoppedFiltrationCore ℱ τ).𝓕 n)
        {ω : Ω | τ.τ ω ≤ n} := by
  simpa using
    StructureTowerProbability.stoppingSet_measurable_in_stoppedFiltrationCore
      (ℱ := ℱ) (τ := τ) n

example {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℕ) (τ : Ω → ℕ) (ω : Ω) :
    StructureTowerProbability.stopped X τ 0 ω = X 0 ω := by
  simpa using
    StructureTowerProbability.stopped_eq_of_le
      (X := X) (τ := τ) (n := 0) (ω := ω) (hn := Nat.zero_le _)

example {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : StructureTowerProbability.Filtration Ω)
    (X : ℕ → Ω → ℝ) (τ : StructureTowerProbability.StoppingTime ℱ)
    (ω : Ω) (n : ℕ) (hn : n ≤ τ.τ ω) :
    let SP : StructureTowerProbability.StoppedProcess ℱ ℝ :=
      ⟨X, τ⟩
    SP.value n ω = X n ω := by
  intro SP
  exact StructureTowerProbability.StoppedProcess.eq_before_stopping SP hn

example {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : StructureTowerProbability.Filtration Ω)
    (X : ℕ → Ω → ℝ) (τ : StructureTowerProbability.StoppingTime ℱ)
    (ω : Ω) (hτ : τ.τ ω ≤ 5) :
    let SP : StructureTowerProbability.StoppedProcess ℱ ℝ :=
      ⟨X, τ⟩
    SP.value 10 ω = SP.value 5 ω := by
  intro SP
  exact StructureTowerProbability.StoppedProcess.const_after_stopping
    SP hτ (by decide : 5 ≤ 10)
