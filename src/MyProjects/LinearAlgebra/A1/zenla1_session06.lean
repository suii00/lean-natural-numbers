import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.RowCol
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Fin.VecNotation

namespace ZenLA1.Session06

open scoped Matrix BigOperators
open Matrix

noncomputable section

/-- 係数行列 A と右辺ベクトル b に対し、m×n 行列を ℝ 上で扱う略記。 -/
abbrev CoeffMatrix (m n : Nat) := Matrix (Fin m) (Fin n) ℝ

/-- m 次元の列ベクトルを ℝ 上で扱う略記。 -/
abbrev ColVector (m : Nat) := Fin m → ℝ

/-- 増結された行列 [A|b] を ℝ 上で表す略記。 -/
abbrev AugmentedMatrix (m n : Nat) := Matrix (Fin m) (Fin (n + 1)) ℝ

/-- 連立一次方程式 Ax = b の解であることを表す述語。 -/
def isSolution {m n : Nat} (A : CoeffMatrix m n) (b : ColVector m) (x : ColVector n) : Prop :=
  A.mulVec x = b

/-- 同次方程式 Ax = 0 の解であることを表す述語。 -/
def isHomogeneousSolution {m n : Nat} (A : CoeffMatrix m n) (x : ColVector n) : Prop :=
  A.mulVec x = 0

/-- 行列 A と列ベクトル b から [A|b] を構成する。 -/
def augment {m n : Nat} (A : CoeffMatrix m n) (b : ColVector m) : AugmentedMatrix m n :=
  fun i j => if h : (j : Nat) < n then A i (Fin.mk j h) else b i

/-- 2 行を入れ替える初等変形。 -/
def swapRows {m n : Nat} (M : Matrix (Fin m) (Fin n) ℝ) (r₁ r₂ : Fin m) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => if i = r₁ then M r₂ j else if i = r₂ then M r₁ j else M i j

/-- 1 行を定数倍する初等変形。 -/
def scaleRow {m n : Nat} (M : Matrix (Fin m) (Fin n) ℝ) (r : Fin m) (c : ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => if i = r then c * M i j else M i j

/-- ある行に別の行の定数倍を加える初等変形。 -/
def addRow {m n : Nat} (M : Matrix (Fin m) (Fin n) ℝ) (rTarget rSource : Fin m) (c : ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => if i = rTarget then M i j + c * M rSource j else M i j

@[simp] lemma augment_apply {m n : Nat} (A : CoeffMatrix m n) (b : ColVector m)
    (i : Fin m) (j : Fin (n + 1)) :
    augment A b i j = if h : (j : Nat) < n then A i (Fin.mk j h) else b i := rfl

@[simp] lemma isSolution_iff {m n : Nat} (A : CoeffMatrix m n) (b : ColVector m)
    (x : ColVector n) : isSolution A b x ↔ A.mulVec x = b := Iff.rfl

@[simp] lemma isHomogeneousSolution_iff {m n : Nat} (A : CoeffMatrix m n)
    (x : ColVector n) : isHomogeneousSolution A x ↔ A.mulVec x = 0 := Iff.rfl

/-- 2×2 行列。 -/
def A1 : CoeffMatrix 2 2 := !![1, 2; 1, 3]

/-- 右辺ベクトル。 -/
def b1 : ColVector 2 := ![5, 7]

/-- 上三角 3×3 行列。 -/
def A2 : CoeffMatrix 3 3 := !![1, 2, 3; 0, 1, 2; 0, 0, 1]

/-- 右辺ベクトル。 -/
def b2 : ColVector 3 := ![6, 3, 1]

/-- 階数落ちする 2×3 行列。 -/
def A3 : CoeffMatrix 2 3 := !![1, 2, 1; 2, 4, 2]

/-- 右辺ベクトル。 -/
def b3 : ColVector 2 := ![3, 6]

/-- 3×2 行列。 -/
def A4 : CoeffMatrix 3 2 := !![1, 2; 3, 4; 5, 6]

/-- 右辺ベクトル。 -/
def b4 : ColVector 3 := ![3, 7, 11]

/-- 連立一次方程式 A1 x = b1 に対して x = [1, 2] が解である。 -/
theorem Q1 : isSolution A1 b1 ![1, 2] := by
  ext i <;> fin_cases i <;>
    simp [isSolution, A1, b1, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- 上三角行列 A2 を用いた方程式で x = [1, 1, 1] が解である。 -/
theorem Q2 : isSolution A2 b2 ![1, 1, 1] := by
  ext i <;> fin_cases i <;>
    simp [isSolution, A2, b2, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- 方程式 A3 x = b3 は 2 つの異なる解を持つ。 -/
theorem Q3 : isSolution A3 b3 ![1, 1, 0] ∧ isSolution A3 b3 ![0, 0, 3] := by
  constructor <;>
    ext i <;> fin_cases i <;>
      simp [isSolution, A3, b3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- A4 x = b4 に対し x = [1, 1] が解である。 -/
theorem Q4 : isSolution A4 b4 ![1, 1] := by
  ext i <;> fin_cases i <;>
    simp [isSolution, A4, b4, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- 同次方程式 A3 x = 0 に非自明解が存在する。 -/
theorem Q5 : isHomogeneousSolution A3 ![2, -1, 0] ∧ ![2, -1, 0] ≠ 0 := by
  constructor
  · ext i <;> fin_cases i <;>
      simp [isHomogeneousSolution, A3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · intro h
    have : (2 : ℝ) ≠ 0 := by norm_num
    exact this (by simpa using congrArg (fun v : ColVector 3 => v 0) h)

/-- パラメータ付き行列。 -/
def A_param (t : ℝ) : CoeffMatrix 2 2 := !![1, t; t, 1]

/-- t = 2 のときの特定解。 -/
theorem Challenge : isSolution (A_param 2) ![4, 4] ![4 / 3, 4 / 3] := by
  ext i <;> fin_cases i <;>
    simp [isSolution, A_param, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-! チェックコマンド。 -/
#check Q1
#check Q2
#check Q3
#check Q4
#check Q5
#check Challenge

end

end ZenLA1.Session06
