/-
ZEN大学「線形代数1」(MTH-1-C1-1030-004, 2025, オンデマンド)
第6回：連立方程式と行列（基礎問題5＋チャレンジ1）— 提出形式：Lean 4 ファイル

提出物：このファイルの `sorry` をすべて消して証明／計算を完成させてください。
想定環境：Lean 4 + mathlib（最新版）。`lake exe cache get` 等で mathlib を取得してください。

学習目標（第6回）
- 連立一次方程式を行列表現 Ax = b として定式化する。
- 拡大係数行列 [A|b] と解の存在性・一意性の関係を理解する。
- 掃き出し法（ガウス消去法）による連立方程式の解法を実践する。
- 同次連立方程式の解空間の構造を学ぶ。
- チャレンジ：パラメータ付き連立方程式の解の分類。
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.RowCol
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.DotProduct

namespace ZenLA1.Session06

open BigOperators Matrix
open scoped Matrix

/-! ## 下準備：連立方程式と行列の型定義 -/

/-- m×n係数行列 -/
abbrev CoeffMatrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- m次元列ベクトル -/
abbrev ColVector (m : ℕ) := Fin m → ℝ

/-- 拡大係数行列 [A|b] の型（m×(n+1)行列）-/
abbrev AugmentedMatrix (m n : ℕ) := Matrix (Fin m) (Fin (n + 1)) ℝ

/-- 連立方程式 Ax = b の解であるかを判定 -/
def isSolution {m n : ℕ} (A : CoeffMatrix m n) (b : ColVector m) (x : ColVector n) : Prop :=
  A.mulVec x = b

/-- 同次連立方程式 Ax = 0 の解であるかを判定 -/
def isHomogeneousSolution {m n : ℕ} (A : CoeffMatrix m n) (x : ColVector n) : Prop :=
  A.mulVec x = 0

/-- 拡大係数行列を作成 -/
def augment {m n : ℕ} (A : CoeffMatrix m n) (b : ColVector m) : AugmentedMatrix m n :=
  fun i j => if h : j.val < n then A i ⟨j.val, h⟩ else b i

/-- 行基本変形：行の交換 -/
def swapRows {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (r₁ r₂ : Fin m) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => if i = r₁ then M r₂ j else if i = r₂ then M r₁ j else M i j

/-- 行基本変形：行のスカラー倍 -/
def scaleRow {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (r : Fin m) (c : ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => if i = r then c * M i j else M i j

/-- 行基本変形：行の加算 -/
def addRow {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (r₁ r₂ : Fin m) (c : ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => if i = r₁ then M i j + c * M r₂ j else M i j

/-! ### 補助：簡単な `simp` 用の補題 -/

@[simp] lemma augment_def {m n : ℕ} (A : CoeffMatrix m n) (b : ColVector m) (i : Fin m) (j : Fin (n + 1)) :
  augment A b i j = if h : j.val < n then A i ⟨j.val, h⟩ else b i := rfl

@[simp] lemma isSolution_def {m n : ℕ} (A : CoeffMatrix m n) (b : ColVector m) (x : ColVector n) :
  isSolution A b x ↔ A.mulVec x = b := Iff.rfl

@[simp] lemma isHomogeneousSolution_def {m n : ℕ} (A : CoeffMatrix m n) (x : ColVector n) :
  isHomogeneousSolution A x ↔ A.mulVec x = 0 := Iff.rfl

/-! ## データ：この回で用いる具体的な連立方程式 -/

/-- 2×2係数行列 A₁ = [[2, 1], [1, 3]] -/
def A₁ : CoeffMatrix 2 2 := !![2, 1; 1, 3]

/-- 右辺ベクトル b₁ = [4, 7] -/
def b₁ : ColVector 2 := ![4, 7]

/-- 3×3係数行列（正則）A₂ = [[1, 2, 3], [0, 1, 2], [0, 0, 1]] -/
def A₂ : CoeffMatrix 3 3 := !![1, 2, 3; 0, 1, 2; 0, 0, 1]

/-- 右辺ベクトル b₂ = [6, 3, 1] -/
def b₂ : ColVector 3 := ![6, 3, 1]

/-- 2×3係数行列（劣決定系）A₃ = [[1, 2, 1], [2, 4, 2]] -/
def A₃ : CoeffMatrix 2 3 := !![1, 2, 1; 2, 4, 2]

/-- 右辺ベクトル b₃ = [3, 6] -/
def b₃ : ColVector 2 := ![3, 6]

/-- 3×2係数行列（過決定系）A₄ = [[1, 2], [3, 4], [5, 6]] -/
def A₄ : CoeffMatrix 3 2 := !![1, 2; 3, 4; 5, 6]

/-- 右辺ベクトル b₄ = [3, 7, 11] -/
def b₄ : ColVector 3 := ![3, 7, 11]

/-! ## 提出ルール
- 各問題は `theorem` / `lemma` / `example` のいずれかを完成させてください。
- 「計算問題」は `simp`, `ring`, `norm_num` などで示せます。
- 「性質の問題」は `ext`, `simp`, `ring` 等の方針をコメントで示すと加点。
- 途中の補題を自由に作って構いません。 -/

/-! ---
## 基礎問題（5問）
--- -/

/-- **Q1** 連立方程式 A₁x = b₁ の解が x = [1, 2] であることを確認せよ。 -/
theorem Q1 : isSolution A₁ b₁ ![1, 2] := by
  ext i <;> fin_cases i <;>
    (simp [A₁, b₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; try norm_num)

/-- **Q2** 上三角行列 A₂ を用いた連立方程式 A₂x = b₂ を後退代入で解き、
x = [1, 1, 1] が解であることを示せ。 -/
theorem Q2 : isSolution A₂ b₂ ![1, 1, 1] := by
  ext i <;> fin_cases i <;>
    (simp [A₂, b₂, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; try norm_num)

/-- **Q3** 劣決定系 A₃x = b₃ において、x = [1, 1, 0] と x = [0, 0, 3] が
両方とも解であることを示せ（解の非一意性）。 -/
theorem Q3 : isSolution A₃ b₃ ![1, 1, 0] ∧ isSolution A₃ b₃ ![0, 0, 3] := by
  constructor
  · ext i <;> fin_cases i <;>
      (simp [A₃, b₃, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; try norm_num)
  · ext i <;> fin_cases i <;>
      (simp [A₃, b₃, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; try norm_num)
/-- **Q4** 過決定系 A₄x = b₄ が解を持つことを示せ（x = [1, 1] が解）。 -/
theorem Q4 : isSolution A₄ b₄ ![1, 1] := by
  ext i <;> fin_cases i <;>
    (simp [A₄, b₄, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; try norm_num)

/-- **Q5** 同次連立方程式 A₁x = 0 において、非自明解 x = [3, -6] が存在することを示せ。
ただし、実際には A₁ は正則なので、この問題設定を変更する必要がある。
代わりに、A₃x = 0 の非自明解 x = [2, -1, 0] を示す。 -/
theorem Q5 : isHomogeneousSolution A₃ ![2, -1, 0] ∧ ![2, -1, 0] ≠ 0 := by
  constructor
  · ext i <;> fin_cases i <;>
      (simp [A₃, Matrix.mulVec, dotProduct, Fin.sum_univ_three]; try norm_num)
  · intro h
    have hfun : (![2, -1, 0] : Fin 3 → ℝ) = 0 := by simpa using h
    have h0 : (2 : ℝ) = 0 := by
      have := congrArg (fun v : Fin 3 → ℝ => v 0) hfun
      simpa using this
    have : (2 : ℝ) ≠ 0 := by norm_num
    exact this h0

/-! ---
## チャレンジ（応用1問）
- パラメータ t を含む連立方程式の解の分類：
  係数行列 A(t) = [[1, t], [t, 1]] に対して、
  - t ≠ ±1 のとき一意解
  - t = 1 のとき無限個の解
  - t = -1 のとき解なし（b ≠ 0 の場合）
  を証明せよ。具体的に t = 2 での一意解を求める。
--- -/

/-- パラメータ付き係数行列 -/
def A_param (t : ℝ) : CoeffMatrix 2 2 := !![1, t; t, 1]

/-- **Challenge** t = 2 のとき、A(2)x = [4, 4] の解は x = [4/3, 4/3]。 -/
theorem Challenge :
  isSolution (A_param 2) ![4, 4] ![4/3, 4/3] := by
  ext i <;> fin_cases i <;>
    norm_num [isSolution_def, A_param, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-! ## 参考：動作確認コマンド（提出時は残してOK）
#check Q1
#check Q2
#check Q3
#check Q4
#check Q5
#check Challenge
-/

end ZenLA1.Session06












