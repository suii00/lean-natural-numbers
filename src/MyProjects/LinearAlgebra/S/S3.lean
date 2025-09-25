/-
file: HW_S3.lean
ZEN大学「線形代数1」（MTH-1-C1-1030-004, 2025, オンデマンド）
提出用 Lean ファイル雛形（S3：行列—和・スカラー倍・積・転置・ベクトルとの積）

使い方：
- 各定理 `S3_P01`〜`S3_P05` と `S3_CH` の `sorry` を証明に置き換えてください。
- 既定の行列は `Matrix (Fin m) (Fin n) ℝ`、ベクトルは `Fin n → ℝ` を用います。
- 依存：Lean 4 + mathlib4（`import Mathlib` ほか）

採点目安（参考）：
- 基礎 P01..P05 各10点（正しさ6・明快さ2・Lean記法2）
- チャレンジ CH 15点（正しさ9・構造的洞察6）
-/

import Mathlib

namespace HW_S3

open Matrix
open scoped BigOperators
open scoped Matrix

/-! ### 基礎問題 -/

/-! ## S3_P01
(1) タイトル：転置は和に関して線形
(2) 学習目標：`(A + B)ᵀ = Aᵀ + Bᵀ`
(3) 課題文：任意の `A,B : Matrix (Fin m) (Fin n) ℝ`
(4) Lean目標：下記の等式
(5) ヒント：`ext i j; simp [Matrix.transpose, Matrix.add_apply]`
-/
theorem S3_P01 {m n : Nat}
    (A B : Matrix (Fin m) (Fin n) ℝ) :
    (A + B)ᵀ = Aᵀ + Bᵀ := by
  simpa using Matrix.transpose_add A B


/-! ## S3_P02
(1) タイトル：転置とスカラー倍の可換性
(2) 学習目標：`(c • A)ᵀ = c • Aᵀ`
(3) 課題文：任意の `c : ℝ` と `A : Matrix (Fin m) (Fin n) ℝ`
(4) Lean目標：上記等式
(5) ヒント：`ext i j; simp [Matrix.transpose, Matrix.smul_apply]`
-/
theorem S3_P02 {m n : Nat}
    (c : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    (c • A)ᵀ = c • Aᵀ := by
  simpa using Matrix.transpose_smul (c := c) (M := A)


/-! ## S3_P03
(1) タイトル：行列積の左分配法則
(2) 学習目標：`A * (B + C) = A * B + A * C`
(3) 課題文：`A : Matrix (Fin m) (Fin n) ℝ`, `B C : Matrix (Fin n) (Fin p) ℝ`
(4) Lean目標：上記等式
(5) ヒント：`simpa using Matrix.mul_add A B C`
-/
theorem S3_P03 {m n p : Nat}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (B C : Matrix (Fin n) (Fin p) ℝ) :
    A * (B + C) = A * B + A * C := by
  simpa using Matrix.mul_add A B C


/-! ## S3_P04
(1) タイトル：積の転置
(2) 学習目標：`(A * B)ᵀ = Bᵀ * Aᵀ`
(3) 課題文：`A : Matrix (Fin m) (Fin n) ℝ`, `B : Matrix (Fin n) (Fin p) ℝ`
(4) Lean目標：上記等式
(5) ヒント：`simpa using Matrix.transpose_mul A B`
-/
theorem S3_P04 {m n p : Nat}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ) :
    (A * B)ᵀ = Bᵀ * Aᵀ := by
  simpa using Matrix.transpose_mul A B


/-! ## S3_P05
(1) タイトル：行列とベクトルの積の加法性
(2) 学習目標：`Matrix.mulVec A (x + y) = Matrix.mulVec A x + Matrix.mulVec A y`
(3) 課題文：`A : Matrix (Fin m) (Fin n) ℝ`, `x y : (Fin n → ℝ)`
(4) Lean目標：上記等式
(5) ヒント：`simpa using Matrix.mulVec_add A x y`
-/
theorem S3_P05 {m n : Nat}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x y : Fin n → ℝ) :
    Matrix.mulVec A (x + y) =
      Matrix.mulVec A x + Matrix.mulVec A y := by
  simpa using Matrix.mulVec_add A x y


/-! ### チャレンジ -/

/-! ## S3_CH
(1) タイトル：転置と内積の両立（アジョイント関係）
(2) 学習目標：`dotProduct (A.mulVec x) y = dotProduct x (Aᵀ.mulVec y)`
(3) 課題文：`A : Matrix (Fin m) (Fin n) ℝ`, `x : Fin n → ℝ`, `y : Fin m → ℝ`
(4) Lean目標：上記等式
(5) ヒント：`simpa using Matrix.dotProduct_mulVec (A:=A) (x:=x) (y:=y)`
-/
theorem S3_CH {m n : Nat}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) :
    dotProduct (Matrix.mulVec A x) y =
      dotProduct x (Matrix.mulVec Aᵀ y) := by
  classical
  have h₁ : dotProduct (Matrix.mulVec A x) y =
      dotProduct y (Matrix.mulVec A x) := dotProduct_comm _ _
  have h₂ : dotProduct (Matrix.mulVec Aᵀ y) x =
      dotProduct x (Matrix.mulVec Aᵀ y) := dotProduct_comm _ _
  have h_vec : Matrix.vecMul y A = Matrix.mulVec Aᵀ y := by
    simpa [Matrix.transpose_transpose] using
      (Matrix.vecMul_transpose (A := Aᵀ) (x := y))
  have h₀ : dotProduct y (Matrix.mulVec A x) =
      dotProduct (Matrix.mulVec Aᵀ y) x := by
    simpa [h_vec] using
      (Matrix.dotProduct_mulVec (v := y) (A := A) (w := x))
  exact h₁.trans <| h₀.trans h₂

example {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) :
    (A + 0)ᵀ = Aᵀ := by
  simpa using S3_P01 A 0

end HW_S3




