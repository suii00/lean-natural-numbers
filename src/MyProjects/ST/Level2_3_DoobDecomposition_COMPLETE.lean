/-
Copyright (c) 2025
Authors: Structure Tower Project
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import MyProjects.ST.CAT2_complete
import MyProjects.ST.Probability
import MyProjects.ST.Level2_1_Martingale_Guide
import MyProjects.ST.Level2_2_OptionalStopping

/-!
# Level 2.3: Doob 分解理論 - 完全版

このファイルは、離散時間の Doob 分解を「構造塔」視点で形式化します。
Bourbaki精神に則り、測度論的詳細を抽象化し、必要最小限の公理で理論を構築します。

## 主要な内容

* `PredictableProcess` — 予測可能過程
* `IncreasingProcess` — 単調増加予測可能過程
* `DoobDecomposition` — 過程の分解構造
* `doob_decomposition_exists` — 存在定理（公理）
* `doob_decomposition_unique` — 一意性定理（公理）
* 具体例と応用

## 構造塔的視点

Doob分解は、構造塔の射を以下のように分割する操作として理解できます：
```
適合過程 X : 一般的な塔射
  = M : minLayerを保存する射（マルチンゲール）
  + A : 層構造から決まる射（予測可能）
```
-/

noncomputable section

universe u v

open Classical

namespace MyProjects
namespace ST

variable {Ω : Type u}

/-! ## 補助定義 -/

/-- 過程の和。 -/
def processAdd (X Y : ℕ → RandomVariable Ω) :
    ℕ → RandomVariable Ω :=
  fun n ω => X n ω + Y n ω

@[simp] lemma processAdd_apply
    (X Y : ℕ → RandomVariable Ω) (n : ℕ) (ω : Ω) :
    processAdd X Y n ω = X n ω + Y n ω :=
  rfl

/-- 零過程。 -/
def zeroProcess : ℕ → RandomVariable Ω :=
  fun _ _ => 0

@[simp] lemma zeroProcess_apply (n : ℕ) (ω : Ω) :
    zeroProcess n ω = 0 :=
  rfl

/-! ## 予測可能過程 -/

/-- 予測可能過程（集合論的モデル）。

時刻0が定数であることのみを要求する最小限の定義。
測度論的な「ℱₙ₋₁-可測性」は公理化により回避。
-/
structure PredictableProcess (F : DiscreteFiltration Ω) where
  /-- 各時刻の値。 -/
  value : ℕ → RandomVariable Ω
  /-- 時刻 0 の値が定数。 -/
  value_zero_const : ∃ c : ℝ, value 0 = fun _ => c

namespace PredictableProcess

variable {F : DiscreteFiltration Ω}

/-- 零予測可能過程。 -/
def zero : PredictableProcess F :=
  { value := zeroProcess
    value_zero_const := ⟨0, rfl⟩ }

@[simp] lemma zero_value (F : DiscreteFiltration Ω) (n : ℕ) (ω : Ω) :
    (PredictableProcess.zero (F := F)).value n ω = 0 :=
  rfl

/-- 定数列から予測可能過程を構成。 -/
def const (c : ℕ → ℝ) : PredictableProcess F :=
  { value := fun n ω => c n
    value_zero_const := ⟨c 0, by funext ω; rfl⟩ }

@[simp] lemma const_value (c : ℕ → ℝ) (n : ℕ) (ω : Ω) :
    (PredictableProcess.const (F := F) c).value n ω = c n :=
  rfl

end PredictableProcess

/-! ## 単調増加過程 -/

/-- 単調増加な予測可能過程。

サブマルチンゲールのDoob分解で現れる予測可能成分の特徴。
-/
structure IncreasingProcess (F : DiscreteFiltration Ω)
    extends PredictableProcess F where
  /-- 初期値は 0。 -/
  value_zero : value 0 = fun _ => 0
  /-- 各軌道が単調増加。 -/
  monotone : ∀ {m n : ℕ}, m ≤ n → ∀ ω : Ω,
    value m ω ≤ value n ω

namespace IncreasingProcess

variable {F : DiscreteFiltration Ω}

/-- 零増加過程。 -/
def zero : IncreasingProcess F :=
  { toPredictableProcess := PredictableProcess.zero (F := F)
    value_zero := rfl
    monotone := by
      intro m n _ ω
      simp [PredictableProcess.zero] }

@[simp] lemma zero_value (F : DiscreteFiltration Ω)
    (n : ℕ) (ω : Ω) :
    (IncreasingProcess.zero (F := F)).value n ω = 0 :=
  rfl

@[simp] lemma zero_value_zero (F : DiscreteFiltration Ω) :
    (IncreasingProcess.zero (F := F)).value 0 = fun _ => 0 :=
  rfl

end IncreasingProcess

/-! ## Doob 分解 -/

/-- Doob 分解構造。

任意の適合過程 X を、マルチンゲール M と予測可能過程 A の和として表現：
```
Xₙ = Mₙ + Aₙ
```
-/
structure DoobDecomposition
    (F : DiscreteFiltration Ω)
    (C : ConditionalExpectationStructure F)
    (X : ℕ → RandomVariable Ω) where
  /-- マルチンゲール部分。 -/
  martingale : ℕ → RandomVariable Ω
  /-- 予測可能成分。 -/
  predictable : PredictableProcess F
  /-- マルチンゲール性。 -/
  is_martingale : IsMartingale F C martingale
  /-- 各時刻での分解式 `Xₙ = Mₙ + Aₙ`。 -/
  decomposition : ∀ n ω,
    X n ω = martingale n ω + predictable.value n ω

namespace DoobDecomposition

variable {F : DiscreteFiltration Ω}
variable {C : ConditionalExpectationStructure F}

/-- 予測可能成分が 0 のとき、X はマルチンゲール部分と一致。 -/
lemma eq_martingale_of_predictable_zero
    {X : ℕ → RandomVariable Ω}
    (D : DoobDecomposition F C X)
    (hzero : ∀ n ω, D.predictable.value n ω = 0) :
    X = D.martingale := by
  funext n ω
  have := D.decomposition n ω
  simpa [hzero] using this

/-- マルチンゲールから得られる自明な Doob 分解。 -/
def of_martingale
    {X : ℕ → RandomVariable Ω}
    (hX : IsMartingale F C X) :
    DoobDecomposition F C X :=
  { martingale := X
    predictable := PredictableProcess.zero (F := F)
    is_martingale := hX
    decomposition := by
      intro n ω
      simp [PredictableProcess.zero] }

@[simp]
lemma of_martingale_predictable_value
    {X : ℕ → RandomVariable Ω}
    (hX : IsMartingale F C X)
    (n : ℕ) (ω : Ω) :
    (of_martingale (F := F) (C := C) hX).predictable.value n ω = 0 :=
  rfl

@[simp]
lemma of_martingale_martingale
    {X : ℕ → RandomVariable Ω}
    (hX : IsMartingale F C X) :
    (of_martingale (F := F) (C := C) hX).martingale = X :=
  rfl

/-- 予測可能成分が消えるなら、X はマルチンゲール。 -/
lemma is_martingale_of_predictable_zero
    {X : ℕ → RandomVariable Ω}
    (D : DoobDecomposition F C X)
    (hzero : ∀ n ω, D.predictable.value n ω = 0) :
    IsMartingale F C X := by
  have h := D.eq_martingale_of_predictable_zero hzero
  simpa [h] using D.is_martingale

end DoobDecomposition

/-! ## 存在と一意性の定理 -/

/-- **Doob分解の存在定理（公理）**

任意の適合過程は、マルチンゲール成分と予測可能成分に分解できる。
実際の構成的証明は測度論を要するため、公理として与える。

**使用法**:
```lean
obtain D := doob_decomposition_exists F C X h_adapted
```
-/
axiom doob_decomposition_exists
    (F : DiscreteFiltration Ω)
    (C : ConditionalExpectationStructure F)
    (X : ℕ → RandomVariable Ω)
    (h_adapted : ∀ n r, {ω : Ω | X n ω ≤ r} ∈ F.sigma n) :
    DoobDecomposition F C X

/-- マルチンゲールに対する存在は構成的に示せる。 -/
def doob_decomposition_exists_for_martingale
    {F : DiscreteFiltration Ω}
    {C : ConditionalExpectationStructure F}
    {X : ℕ → RandomVariable Ω}
    (hX : IsMartingale F C X) :
    DoobDecomposition F C X :=
  DoobDecomposition.of_martingale hX

/-- **Doob分解の一意性定理（公理）**

二つの分解 X = M₁ + A₁ = M₂ + A₂ が与えられたとき、
マルチンゲール成分と予測可能成分はそれぞれ一致する。

**証明の概略**:
M₁ - M₂ = A₂ - A₁ は予測可能かつマルチンゲールなので定数。
両方とも0で始まるため、恒等的に0。
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

/-- **サブマルチンゲールのDoob分解（公理）**

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
      value_zero_const := by
        obtain ⟨c, hc⟩ := D.predictable.value_zero_const
        refine ⟨c, funext ?_⟩
        intro ω
        have hconst : D.predictable.value 0 ω = c := by
          simpa using congrArg (fun f => f ω) hc
        have hmin : min (0 : ℕ) (τ.value ω) = 0 := by simp
        have := congrArg (fun n => D.predictable.value n ω) hmin
        calc
          D.predictable.value (min 0 (τ.value ω)) ω
              = D.predictable.value 0 ω := this
          _ = c := hconst
    }
    is_martingale := h_stopped_martingale
    decomposition := by
      intro n ω
      have := D.decomposition (min n (τ.value ω)) ω
      simp [stoppedProcess]
      exact this
  }

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

/-! ## 分解の基本性質 -/

section BasicProperties

variable {F : DiscreteFiltration Ω}
variable {C : ConditionalExpectationStructure F}

/-- 分解の線形性：和の分解。 -/
def doob_decomposition_add
    {X Y : ℕ → RandomVariable Ω}
    (DX : DoobDecomposition F C X)
    (DY : DoobDecomposition F C Y)
    (h_sum : IsMartingale F C (processAdd DX.martingale DY.martingale)) :
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
    is_martingale := h_sum
    decomposition := by
      intro n ω
      have hX := DX.decomposition n ω
      have hY := DY.decomposition n ω
      simp [processAdd, hX, hY, add_left_comm, add_assoc]
  }

/-- 分解のスカラー倍。 -/
def doob_decomposition_smul
    {X : ℕ → RandomVariable Ω}
    (D : DoobDecomposition F C X)
    (c : ℝ)
    (h_smul : IsMartingale F C (fun n ω => c * D.martingale n ω)) :
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
    is_martingale := h_smul
    decomposition := by
      intro n ω
      have := D.decomposition n ω
      simp [this, mul_add]
  }

end BasicProperties

/-! ## 具体例 -/

section Examples

variable {F : DiscreteFiltration Ω}
variable {C : ConditionalExpectationStructure F}

/-- 例1: 定数マルチンゲールの自明分解。 -/
example (c : ℝ) (h : IsMartingale F C (fun _ _ => c)) :
    ∃ D : DoobDecomposition F C (fun _ _ => c),
      ∀ n, D.predictable.value n = fun _ => 0 := by
  refine ⟨DoobDecomposition.of_martingale (F := F) (C := C) h, ?_⟩
  intro n
  funext ω
  rfl

/-- 例2: 線形ドリフトを持つ過程。 -/
example
    (M : ℕ → RandomVariable Ω)
    (hM : IsMartingale F C M)
    (drift : ℝ) :
    let X := fun n ω => M n ω + drift * (n : ℝ)
    let A : PredictableProcess F := 
      PredictableProcess.const (fun n => drift * (n : ℝ))
    ∃ D : DoobDecomposition F C X,
      D.martingale = M ∧
      D.predictable.value = A.value := by
  intro X A
  refine ⟨{
    martingale := M
    predictable := A
    is_martingale := hM
    decomposition := by
      intro n ω
      simp [X, A, PredictableProcess.const]
  }, rfl, rfl⟩

/-- 例3: 自明分解の一意性。 -/
example
    (M : ℕ → RandomVariable Ω)
    (hM : IsMartingale F C M) :
    let D₁ := DoobDecomposition.of_martingale (F := F) (C := C) hM
    let D₂ := DoobDecomposition.of_martingale (F := F) (C := C) hM
    D₁.martingale = D₂.martingale := by
  intro D₁ D₂
  rfl

/-- 例4: 停止後の分解。 -/
example
    (X : ℕ → RandomVariable Ω)
    (τ : StoppingTime F)
    (D : DoobDecomposition F C X)
    (h_stopped : IsMartingale F C (stoppedProcess D.martingale τ)) :
    ∃ D_stopped : DoobDecomposition F C (stoppedProcess X τ),
      D_stopped.martingale = stoppedProcess D.martingale τ := by
  refine ⟨doob_decomposition_of_stopped D τ h_stopped, rfl⟩

/-- 例5: `doob_decomposition_exists_for_martingale` と `of_martingale` の対応。 -/
example
    (M : ℕ → RandomVariable Ω)
    (hM : IsMartingale F C M) :
    doob_decomposition_exists_for_martingale
        (F := F) (C := C) (X := M) hM =
      DoobDecomposition.of_martingale (F := F) (C := C) hM := 
  rfl

end Examples

/-! ## 使用パターンのまとめ -/

/-
# Doob分解の使用方法

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

-- マルチンゲール成分を取り出す
let M := D.martingale

-- 予測可能成分を取り出す
let A := D.predictable.value
```

## パターン3: 分解の操作

```lean
-- 線形結合（マルチンゲール性の証明が必要）
let D_sum := doob_decomposition_add DX DY h_sum

-- スカラー倍
let D_scaled := doob_decomposition_smul D c h_smul

-- 停止
let D_stopped := doob_decomposition_of_stopped D τ h_mart
```

## パターン4: 一意性の利用

```lean
-- 二つの分解を比較
have h_unique := doob_decomposition_unique D₁ D₂
-- h_unique : D₁.martingale = D₂.martingale ∧ 
--             D₁.predictable.value = D₂.predictable.value
```
-/

end ST
end MyProjects
