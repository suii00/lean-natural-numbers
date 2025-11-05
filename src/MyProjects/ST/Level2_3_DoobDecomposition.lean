/-
Copyright (c) 2025
Authors: Structure Tower Project
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import MyProjects.ST.CAT2_complete
import MyProjects.ST.Probability
import MyProjects.ST.Level2_1_Martingale_Guide

/-
# Level 2.3: Doob 分解の抽象モデル

このファイルでは、`Probability.md` の Level 2.3 に基づき、
離散時間の Doob 分解を「構造塔」視点で簡潔にモデル化します。
厳密な測度論や条件付き期待値の詳細は扱わず、以下の最小限の情報を整理します。

* `PredictableProcess` — 予測可能過程（時刻 0 が定数であることのみ記録）
* `IncreasingProcess` — 各軌道が単調増加する予測可能過程
* `DoobDecomposition` — 過程 `X` をマルチンゲール部分と予測可能部分に分解したデータ

Lean での実装は集合論的・構造主義的アプローチに徹し、Doob 分解が
「塔の射をマルチンゲール射と予測可能射に分割する」イメージを保持します。
-/

noncomputable section

universe u v

open Classical

namespace MyProjects
namespace ST

variable {Ω : Type u}

/-- 過程の和を表す補助定義。 -/
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

/-- 予測可能過程（集合論的なモデル）。 -/
structure PredictableProcess (F : DiscreteFiltration Ω) where
  /-- 各時刻の値。 -/
  value : ℕ → RandomVariable Ω
  /-- 時刻 0 の値が定数であることを記録する。 -/
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

/-- 任意の定数列から予測可能過程を得る。 -/
def const (c : ℕ → ℝ) : PredictableProcess F :=
  { value := fun n ω => c n
    value_zero_const := ⟨c 0, by funext ω; rfl⟩ }

@[simp] lemma const_value (c : ℕ → ℝ) (n : ℕ) (ω : Ω) :
    (PredictableProcess.const (F := F) c).value n ω = c n :=
  rfl

end PredictableProcess

/-- 単調増加な予測可能過程。 -/
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

/-- Doob 分解を保持する構造体。 -/
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

/-- 予測可能成分が 0 のとき、`X` はマルチンゲール部分と一致する。 -/
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

/-- 自明分解において予測可能成分は常に 0。 -/
@[simp]
lemma of_martingale_predictable_value
    {X : ℕ → RandomVariable Ω}
    (hX : IsMartingale F C X)
    (n : ℕ) (ω : Ω) :
    (of_martingale (F := F) (C := C) hX).predictable.value n ω = 0 :=
  rfl

/-- 自明分解では `X` とマルチンゲール部分が一致する。 -/
@[simp]
lemma of_martingale_martingale
    {X : ℕ → RandomVariable Ω}
    (hX : IsMartingale F C X) :
    (of_martingale (F := F) (C := C) hX).martingale = X :=
  rfl

/-- 自明分解では分解式が `X = X + 0` に簡約される。 -/
@[simp]
lemma of_martingale_decomposition
    {X : ℕ → RandomVariable Ω}
    (hX : IsMartingale F C X) (n : ℕ) (ω : Ω) :
    X n ω =
      (of_martingale (F := F) (C := C) hX).martingale n ω +
      (of_martingale (F := F) (C := C) hX).predictable.value n ω :=
  (of_martingale (F := F) (C := C) hX).decomposition n ω

/-- 予測可能成分が消えるなら、`X` はマルチンゲールである。 -/
lemma is_martingale_of_predictable_zero
    {X : ℕ → RandomVariable Ω}
    (D : DoobDecomposition F C X)
    (hzero : ∀ n ω, D.predictable.value n ω = 0) :
    IsMartingale F C X := by
  have h := D.eq_martingale_of_predictable_zero hzero
  simpa [h] using D.is_martingale

end DoobDecomposition

/-- 具体例：定数マルチンゲールの Doob 分解（仮定付き）。 -/
example {F : DiscreteFiltration Ω}
    {C : ConditionalExpectationStructure F}
    (c : ℝ)
    (h : IsMartingale F C (fun _ _ => c)) :
    ∃ D : DoobDecomposition F C (fun _ _ => c),
      ∀ n, D.predictable.value n = fun _ => 0 := by
  refine ⟨DoobDecomposition.of_martingale (F := F) (C := C) h, ?_⟩
  intro n
  funext ω
  rfl

end ST
end MyProjects
