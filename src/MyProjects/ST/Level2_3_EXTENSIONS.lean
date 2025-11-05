/-
このファイルは Level2_3_DoobDecomposition.lean の末尾に追加できる拡張コードです。
既存の実装を保ちながら、存在定理、一意性、具体例を追加します。
-/

/-! ## 存在と一意性の定理 -/

/-- Doob分解の存在を主張する公理。

任意の適合過程は、マルチンゲール成分と予測可能成分に分解できる。
実際の構成的証明は測度論を要するため、ここでは公理として与える。

**使用法**:
```lean
obtain D := doob_decomposition_exists F C X h_adapted
-- これで D : DoobDecomposition F C X が得られる
```
-/
axiom doob_decomposition_exists
    (F : DiscreteFiltration Ω)
    (C : ConditionalExpectationStructure F)
    (X : ℕ → RandomVariable Ω)
    (h_adapted : ∀ n r, {ω : Ω | X n ω ≤ r} ∈ F.sigma n) :
    DoobDecomposition F C X

/-- マルチンゲールに対する存在は構成的に示せる。 -/
theorem doob_decomposition_exists_for_martingale
    {F : DiscreteFiltration Ω}
    {C : ConditionalExpectationStructure F}
    {X : ℕ → RandomVariable Ω}
    (hX : IsMartingale F C X) :
    DoobDecomposition F C X :=
  DoobDecomposition.of_martingale hX

/-- Doob分解の一意性を主張する公理。

二つの分解 X = M₁ + A₁ = M₂ + A₂ が与えられたとき、
マルチンゲール成分と予測可能成分はそれぞれ一致する。

**証明の概略**:
M₁ - M₂ = A₂ - A₁ は予測可能かつマルチンゲールなので定数。
両方とも0で始まるため、恒等的に0。よって M₁ = M₂, A₁ = A₂。
-/
axiom doob_decomposition_unique
    {F : DiscreteFiltration Ω}
    {C : ConditionalExpectationStructure F}
    {X : ℕ → RandomVariable Ω}
    (D₁ D₂ : DoobDecomposition F C X) :
    D₁.martingale = D₂.martingale ∧
    D₁.predictable.value = D₂.predictable.value

/-- 一意性の系：各時刻で成分が一致。 -/
theorem doob_decomposition_unique_pointwise
    {F : DiscreteFiltration Ω}
    {C : ConditionalExpectationStructure F}
    {X : ℕ → RandomVariable Ω}
    (D₁ D₂ : DoobDecomposition F C X) :
    (∀ n, D₁.martingale n = D₂.martingale n) ∧
    (∀ n, D₁.predictable.value n = D₂.predictable.value n) := by
  obtain ⟨hM, hA⟩ := doob_decomposition_unique D₁ D₂
  exact ⟨fun n => congrFun hM n, fun n => congrFun hA n⟩

/-! ## サブマルチンゲールとの関係 -/

/-- サブマルチンゲールのDoob分解は増加過程を与える（公理）。

X がサブマルチンゲールなら、予測可能成分は増加過程として取れる。
これがDoob-Meyer分解の離散版。
-/
axiom doob_decomposition_of_submartingale_increasing
    {F : DiscreteFiltration Ω}
    {C : ConditionalExpectationStructure F}
    {X : ℕ → RandomVariable Ω}
    (hX : IsSubmartingale F C X)
    (D : DoobDecomposition F C X) :
    ∃ A_inc : IncreasingProcess F,
      D.predictable.value = A_inc.value

/-! ## Optional Stoppingとの互換性 -/

section StoppingTheorems

variable {F : DiscreteFiltration Ω}
variable {C : ConditionalExpectationStructure F}

/-- 停止された過程のDoob分解。

X = M + A なら、X^τ = M^τ + A^τ でこれもDoob分解を持つ。
-/
def doob_decomposition_of_stopped
    {X : ℕ → RandomVariable Ω}
    (D : DoobDecomposition F C X)
    (τ : StoppingTime F)
    (h_stopped_martingale : IsMartingale F C (stoppedProcess D.martingale τ)) :
    DoobDecomposition F C (stoppedProcess X τ) :=
  { martingale := stoppedProcess D.martingale τ
    predictable := {
      value := fun n ω => D.predictable.value (min n (τ.value ω)) ω
      value_zero_const := D.predictable.value_zero_const
    }
    is_martingale := h_stopped_martingale
    decomposition := by
      intro n ω
      have := D.decomposition (min n (τ.value ω)) ω
      simp [stoppedProcess]
      exact this
  }

/-- 停止されたマルチンゲール成分は元のマルチンゲールの停止。 -/
@[simp]
theorem stopped_decomposition_martingale
    {X : ℕ → RandomVariable Ω}
    (D : DoobDecomposition F C X)
    (τ : StoppingTime F)
    (h : IsMartingale F C (stoppedProcess D.martingale τ)) :
    (doob_decomposition_of_stopped D τ h).martingale =
    stoppedProcess D.martingale τ :=
  rfl

end StoppingTheorems

/-! ## 具体例の追加 -/

section Examples

variable {F : DiscreteFiltration Ω}
variable {C : ConditionalExpectationStructure F}

/-- 例2: 線形ドリフトを持つマルチンゲール。 -/
example
    (M : ℕ → RandomVariable Ω)
    (hM : IsMartingale F C M)
    (drift : ℝ)
    (hdrift : 0 < drift) :
    let X := fun n ω => M n ω + drift * (n : ℝ)
    let A : PredictableProcess F := 
      PredictableProcess.const (fun n => drift * (n : ℝ))
    ∃ D : DoobDecomposition F C X,
      D.martingale = M ∧
      D.predictable.value = A.value := by
  intro X A
  -- X = M + (drift * n) の形
  -- M はマルチンゲール、drift * n は予測可能
  refine ⟨{
    martingale := M
    predictable := A
    is_martingale := hM
    decomposition := by
      intro n ω
      simp [X, A, PredictableProcess.const]
      ring
  }, rfl, rfl⟩

/-- 例3: 二つの分解が等しいことを示す。 -/
example
    (M : ℕ → RandomVariable Ω)
    (hM : IsMartingale F C M) :
    let D₁ := DoobDecomposition.of_martingale (F := F) (C := C) hM
    let D₂ := DoobDecomposition.of_martingale (F := F) (C := C) hM
    D₁.martingale = D₂.martingale := by
  intro D₁ D₂
  rfl

/-- 例4: 分解の使用例（Optional Stoppingとの組み合わせ）。 -/
example
    (X : ℕ → RandomVariable Ω)
    (h_adapted : ∀ n r, {ω : Ω | X n ω ≤ r} ∈ F.sigma n)
    (τ : StoppingTime F)
    (hτ : τ.IsBounded 10) :
    -- X の分解を取得し、停止された過程も分解を持つ
    let D := doob_decomposition_exists F C X h_adapted
    ∃ D_stopped : DoobDecomposition F C (stoppedProcess X τ), True := by
  intro D
  -- 停止されたマルチンゲールがマルチンゲールであることが示せれば
  -- doob_decomposition_of_stopped を使える
  sorry  -- IsMartingale (stoppedProcess D.martingale τ) が必要

end Examples

/-! ## 分解の基本性質 -/

section BasicProperties

variable {F : DiscreteFiltration Ω}
variable {C : ConditionalExpectationStructure F}

/-- 分解の線形性：和の分解。 -/
theorem doob_decomposition_add
    {X Y : ℕ → RandomVariable Ω}
    (DX : DoobDecomposition F C X)
    (DY : DoobDecomposition F C Y) :
    DoobDecomposition F C (processAdd X Y) :=
  { martingale := processAdd DX.martingale DY.martingale
    predictable := {
      value := processAdd DX.predictable.value DY.predictable.value
      value_zero_const := by
        obtain ⟨cX, hX⟩ := DX.predictable.value_zero_const
        obtain ⟨cY, hY⟩ := DY.predictable.value_zero_const
        use cX + cY
        funext ω
        simp [processAdd, hX, hY]
    }
    is_martingale := by
      sorry  -- マルチンゲールの和はマルチンゲール
    decomposition := by
      intro n ω
      simp [processAdd]
      have hX := DX.decomposition n ω
      have hY := DY.decomposition n ω
      linarith
  }

/-- 分解のスカラー倍。 -/
theorem doob_decomposition_smul
    {X : ℕ → RandomVariable Ω}
    (D : DoobDecomposition F C X)
    (c : ℝ) :
    DoobDecomposition F C (fun n ω => c * X n ω) :=
  { martingale := fun n ω => c * D.martingale n ω
    predictable := {
      value := fun n ω => c * D.predictable.value n ω
      value_zero_const := by
        obtain ⟨c₀, h₀⟩ := D.predictable.value_zero_const
        use c * c₀
        funext ω
        simp [h₀]
    }
    is_martingale := by
      sorry  -- マルチンゲールのスカラー倍はマルチンゲール
    decomposition := by
      intro n ω
      have := D.decomposition n ω
      simp
      linarith
  }

end BasicProperties

/-! ## 使用例のまとめ -/

/-
# Doob分解の使用パターン

## パターン1: 既知のマルチンゲールから
```lean
def M : ℕ → RandomVariable Ω := ...  -- マルチンゲール
have hM : IsMartingale F C M := ...

-- 自明な分解を取得
let D := DoobDecomposition.of_martingale hM
-- D.predictable は常に0
```

## パターン2: 一般の過程から（公理使用）
```lean
def X : ℕ → RandomVariable Ω := ...  -- 適合過程
have h_adapted : ∀ n r, {ω | X n ω ≤ r} ∈ F.sigma n := ...

-- 存在定理を使用
obtain D := doob_decomposition_exists F C X h_adapted
-- D : DoobDecomposition F C X

-- マルチンゲール成分を取り出す
let M := D.martingale
-- M はマルチンゲール

-- 予測可能成分を取り出す
let A := D.predictable.value
-- A は予測可能
```

## パターン3: 分解の操作
```lean
-- 線形結合
let D_sum := doob_decomposition_add DX DY
let D_scaled := doob_decomposition_smul D c

-- 停止
let D_stopped := doob_decomposition_of_stopped D τ h_mart
```

## パターン4: 一意性の利用
```lean
-- 二つの分解を比較
have h_unique := doob_decomposition_unique D₁ D₂
-- h_unique : D₁.martingale = D₂.martingale ∧ ...
```
-/
