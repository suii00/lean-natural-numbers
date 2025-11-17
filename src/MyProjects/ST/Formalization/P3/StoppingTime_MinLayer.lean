import Mathlib.MeasureTheory.MeasurableSpace.Basic
import MyProjects.ST.Formalization.P2.SigmaAlgebraTower_Skeleton

/-!
# StoppingTime_MinLayer

`SigmaAlgebraTower_Skeleton.lean` で構築したフィルトレーション/構造塔を
停止時間へ適用する最初のステップ。

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

/-- 停止フィルトレーション（covers なしの核）。 -/
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
        {ω : Ω |
          (StructureTowerProbability.truncateStoppingTime ℱ τ n).τ ω ≤ n} := by
  simpa using
    StructureTowerProbability.stoppingSet_mem_stoppedSigma
      (ℱ := ℱ)
      (τ := StructureTowerProbability.truncateStoppingTime ℱ τ n) n
