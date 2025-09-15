/-
ZEN大学「線形代数1」(MTH-1-C1-1030-004, 2025, オンデマンド)
第4回：行列式（基礎問題5＋チャレンジ1）— 提出形式：Lean 4 ファイル

提出物：このファイルの `sorry` をすべて消して証明／計算を完成させてください。
想定環境：Lean 4 + mathlib（最新版）。`lake exe cache get` 等で mathlib を取得してください。

学習目標（第4回）
- 2×2、3×3行列の行列式の定義と計算方法を習得する。
- 行列式の基本性質（転置不変性、多重線形性、交代性）を理解する。
- 余因子展開（Laplace展開）による行列式の計算を実践する。
- 行列式と行列の正則性（可逆性）の関係を形式化する。
- チャレンジ：Vandermonde行列式の計算と一般形の証明。
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace ZenLA1.Session04

open BigOperators Matrix

/-! ## 下準備：行列型と行列式 -/

/-- 2×2実行列の型。 -/
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

/-- 3×3実行列の型。 -/
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

/-- 2×2行列の行列式（自作定義）。 -/
def det2 (A : Mat2) : ℝ := A 0 0 * A 1 1 - A 0 1 * A 1 0

/-- 3×3行列の行列式（Sarrusの規則による自作定義）。 -/
def det3 (A : Mat3) : ℝ :=
  A 0 0 * A 1 1 * A 2 2 + A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1
  - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2 - A 0 2 * A 1 1 * A 2 0

/-- 橋渡し：2×2 の自作定義 `det2` は `Matrix.det` と一致。 -/
@[simp] lemma det2_eq_det (A : Mat2) : det2 A = Matrix.det A := by
  classical
  simpa [det2] using (Matrix.det_fin_two (A := A)).symm

/-- 橋渡し：3×3 の自作定義 `det3` は `Matrix.det` と一致。 -/
@[simp] lemma det3_eq_det (A : Mat3) : det3 A = Matrix.det A := by
  classical
  -- `Matrix.det_fin_three` の式は項の並びが異なるだけなので演算律で整形
  simpa [ det3
       , sub_eq_add_neg
       , add_comm, add_left_comm, add_assoc
       , mul_comm, mul_left_comm, mul_assoc ]
    using (Matrix.det_fin_three (A := A)).symm

/-- 逆向き：2×2 で `Matrix.det` は `det2` に等しい。 -/
lemma det_eq_det2 (A : Mat2) : Matrix.det A = det2 A := by
  classical
  simpa using (det2_eq_det (A := A)).symm

/-- 逆向き：3×3 で `Matrix.det` は `det3` に等しい。 -/
lemma det_eq_det3 (A : Mat3) : Matrix.det A = det3 A := by
  classical
  simpa using (det3_eq_det (A := A)).symm

/-- 2×2行列が正則（可逆）であるための条件。 -/
def isRegular2 (A : Mat2) : Prop := det2 A ≠ 0

/-- 3×3行列が正則（可逆）であるための条件。 -/
def isRegular3 (A : Mat3) : Prop := det3 A ≠ 0

/-! ### 補助：簡単な `simp` 用の補題 -/

@[simp] lemma det2_def (A : Mat2) :
  det2 A = A 0 0 * A 1 1 - A 0 1 * A 1 0 := rfl

@[simp] lemma det3_def (A : Mat3) :
  det3 A = A 0 0 * A 1 1 * A 2 2 + A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1
          - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2 - A 0 2 * A 1 1 * A 2 0 := rfl

/-! ## データ：この回で用いる具体行列 -/

/-- 2×2行列 A = [[3, 2], [1, 4]]。 -/
def A : Mat2 := !![3, 2; 1, 4]

/-- 2×2行列 B = [[2, -1], [3, 2]]。 -/
def B : Mat2 := !![2, -1; 3, 2]

/-- 3×3行列 C = [[1, 2, 3], [0, 1, 4], [5, 6, 0]]。 -/
def C : Mat3 := !![1, 2, 3; 0, 1, 4; 5, 6, 0]

/-- 3×3行列 D（第1列に沿った余因子展開用）= [[2, 1, 3], [0, 4, 2], [0, 0, 5]]。 -/
def D : Mat3 := !![2, 1, 3; 0, 4, 2; 0, 0, 5]

/-- 3×3 Vandermonde行列 V = [[1, 1, 1], [1, 2, 4], [1, 3, 9]]。 -/
def V : Mat3 := !![1, 1, 1; 1, 2, 4; 1, 3, 9]

/-! ## 提出ルール
- 各問題は `theorem` / `lemma` / `example` のいずれかを完成させてください。
- 「計算問題」は `simp`, `ring`, `norm_num` などで示せます。
- 「性質の問題」は `ext`, `simp`, `ring` 等の方針をコメントで示すと加点。
- 途中の補題を自由に作って構いません。 -/

/-! ---
## 基礎問題（5問）
--- -/

/-- **Q1** 2×2行列 `A * B` の行列式を計算せよ（積の行列式 = 行列式の積）。 -/
theorem Q1 : det2 (A * B) = det2 A * det2 B := by
  -- 具体行列に対して項別に展開して同値を示す
  simp [det2, A, B, Matrix.mul_apply, Fin.sum_univ_two]
  ring
  -- ヒント：左辺を `simp [det2, A, B, Matrix.mul_apply, Fin.sum_univ_two]` で展開し、
  -- 右辺も同様に展開して `ring` で一致を示す。

/-- **Q2** 2×2行列の転置不変性：`det2 A^T = det2 A` を示せ。 -/
theorem Q2 (A : Mat2) : det2 (transpose A) = det2 A := by
  -- 成分で書き下ろし，転置の定義から直ちに従う
  simp [det2, transpose_apply]
  ring
  -- ヒント：`simp [det2, transpose_apply]` → `ring`。

/-- **Q3** 3×3行列 C の行列式を計算せよ。 -/
theorem Q3 : det3 C = 1 := by
  -- Sarrus 展開を数値計算で確認
  simp [det3, C]
  norm_num
  -- ヒント：`simp [det3, C]` → `norm_num`。

/-- **Q4** 上三角行列 D の行列式は対角成分の積：`det3 D = D 0 0 * D 1 1 * D 2 2` を示せ。 -/
theorem Q4 : det3 D = D 0 0 * D 1 1 * D 2 2 := by
  -- 上三角なので Sarrus 展開の多くが 0 となり，対角積に一致
  -- `simp` のみで両辺とも同じ式に簡約され，反射律で閉じる
  simp [det3, D]
  -- ヒント：`simp [det3, D]` → `norm_num` で確認。
  -- 一般的な証明は、下三角部分が0であることを使う。

/-- **Q5** 2×2行列が正則 ⇔ 行列式≠0 を利用して、A が正則であることを示せ。 -/
theorem Q5 : isRegular2 A := by
  -- 行列式が 0 でないことを直接計算
  simp [isRegular2, det2, A]
  norm_num
  -- ヒント：`simp [isRegular2, det2, A]` → `norm_num`。

/-! ---
## チャレンジ（応用1問）
- 3×3 Vandermonde行列 V(1,2,3) の行列式を計算し、
  一般に V(a,b,c) の行列式が `(b-a)(c-a)(c-b)` となることを証明せよ。
  ただし、V(a,b,c) = [[1, 1, 1], [a, b, c], [a^2, b^2, c^2]]。
--- -/

/-- Vandermonde行列の定義。 -/
def vandermonde (a b c : ℝ) : Mat3 :=
  !![1, 1, 1; a, b, c; a^2, b^2, c^2]

theorem Challenge :
  (det3 V = 2) ∧
  (∀ a b c : ℝ, det3 (vandermonde a b c) = (b - a) * (c - a) * (c - b)) := by
  constructor
  · -- V = V(1,2,3) の行列式を計算
    simp [det3, V]
    norm_num
    -- ヒント：`simp [det3, V]` → `norm_num`。
  · -- 一般形の証明
    intro a b c
    -- Sarrus 展開を成分で書き下ろし，右辺を展開して同型化
    simp [det3, vandermonde]
    ring
    /- ヒント：
       - `simp [det3, vandermonde]` で展開
       - 展開した式を `ring` で整理
       - 因数分解の形 `(b-a)(c-a)(c-b)` になることを示す
       - あるいは、行基本変形を使った議論も可能
    -/

/-! ## 参考：動作確認コマンド（提出時は残してOK）
#check Q1
#check Q2
#check Q3
#check Q4
#check Q5
#check Challenge
-/

end ZenLA1.Session04

/-! #############################################################################
一般 n×n 版の定理化（補遺）
############################################################################# -/

namespace ZenLA1.Session04.General

open Matrix BigOperators

variable {ι R : Type*}
  [Fintype ι] [DecidableEq ι] [CommRing R]

/-- 一般 n×n：転置で行列式は不変。 -/
theorem det_transpose (A : Matrix ι ι R) : det (Matrix.transpose A) = det A := by
  classical
  simpa using Matrix.det_transpose (A := A)

/-- 一般 n×n：積の行列式は行列式の積。 -/
theorem det_mul (A B : Matrix ι ι R) : det (A * B) = det A * det B := by
  classical
  simpa using Matrix.det_mul A B

-- Fin 指標に特化した上三角の対角積（`Fin` は線形順序を持つ）
variable {n : ℕ}

/-- 一般 n×n：上三角（対角より下が 0）なら行列式は対角積。 -/

theorem det_upperTriangular_fin
    (A : Matrix (Fin n) (Fin n) R)
    (h : ∀ ⦃i j : Fin n⦄, i < j → A j i = 0) :
    det A = ∏ i, A i i := by
  classical
  -- `BlockTriangular id` へ構造化（j<i → A i j = 0）
  have hBlock : Matrix.BlockTriangular A id := by
    intro i j hij
    exact h (i := j) (j := i) hij
  simpa using Matrix.det_of_upperTriangular (M := A) hBlock

-- しばしば用いる下三角 0 条件 `j < i → A i j = 0` からの派生版
theorem det_upperTriangular_fin'
    (A : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, j < i → A i j = 0) :
    det A = ∏ i, A i i := by
  classical
  -- そのまま `BlockTriangular id` と一致
  have hBlock : Matrix.BlockTriangular A id := by
    intro i j hij
    exact h i j hij
  simpa using Matrix.det_of_upperTriangular (M := A) hBlock

end ZenLA1.Session04.General

/-! #############################################################################
Fin 指標向け：defeq を良くする行列積 `Matrix.mulᵣ`
############################################################################# -/

namespace ZenLA1.Session04.FinMul

open Matrix

universe u

/- Fin ベクトル（= 関数）とその map -/
abbrev FinVec (n : ℕ) (α : Type u) := Fin n → α

namespace Matrix

  /-- Fin に沿った再帰で定義したドット積（`Add` と `Mul` と `Zero` のみを要求）。 -/
  def dotProductᵣ {α : Type u} [Mul α] [Add α] [Zero α]
      {m : ℕ} (v₁ v₂ : Fin m → α) : α :=
    match m with
    | 0 => 0
    | Nat.succ m =>
        v₁ 0 * v₂ 0 + dotProductᵣ (m := m) (fun i => v₁ i.succ) (fun i => v₂ i.succ)

  /-- `Fin` 指標での defeq を重視した行列積（成分定義）。 -/
  def mulᵣ {l m n : ℕ} {α : Type u} [Mul α] [Add α] [Zero α]
      (A : Matrix (Fin l) (Fin m) α) (B : Matrix (Fin m) (Fin n) α) :
      Matrix (Fin l) (Fin n) α :=
    fun i j => Matrix.dotProductᵣ (fun k => A i k) (fun k => B k j)

  @[simp] theorem mulᵣ_apply {l m n : ℕ} {α : Type u} [Mul α] [Add α] [Zero α]
      (A : Matrix (Fin l) (Fin m) α) (B : Matrix (Fin m) (Fin n) α)
      (i : Fin l) (j : Fin n) :
      mulᵣ A B i j =
        Matrix.dotProductᵣ (fun k => A i k) (fun k => B k j) := rfl

end Matrix

end ZenLA1.Session04.FinMul
