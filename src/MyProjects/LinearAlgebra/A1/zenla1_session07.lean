/-
ZEN大学「線形代数1」(MTH-1-C1-1030-004, 2025, オンデマンド)
第7回：逆行列（基礎問題5＋チャレンジ1）— 提出形式：Lean 4 ファイル

提出物：このファイルの `sorry` をすべて消して証明／計算を完成させてください。
想定環境：Lean 4 + mathlib（最新版）。`lake exe cache get` 等で mathlib を取得してください。

学習目標（第7回）
- 逆行列の定義と存在条件（行列式≠0）を理解する。
- 2×2、3×3行列の逆行列の公式を習得する。
- 逆行列の性質（積の逆、転置の逆、逆の逆）を証明する。
- 逆行列を用いた連立方程式の解法（クラメルの公式）を実践する。
- チャレンジ：ブロック行列の逆行列公式の証明。
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Invertible
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace ZenLA1.Session07

open BigOperators Matrix
open scoped Matrix

/-! ## 下準備：逆行列の型定義と基本演算 -/

/-- 2×2実行列の型 -/
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

/-- 3×3実行列の型 -/
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

/-- 2×2行列の行列式（第4回から継承）-/
def det2 (A : Mat2) : ℝ := A 0 0 * A 1 1 - A 0 1 * A 1 0

/-- 3×3行列の行列式（第4回から継承）-/
def det3 (A : Mat3) : ℝ :=
  A 0 0 * A 1 1 * A 2 2 + A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1
  - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2 - A 0 2 * A 1 1 * A 2 0

/-- 2×2行列が可逆であるための条件 -/
def isInvertible2 (A : Mat2) : Prop := det2 A ≠ 0

/-- 3×3行列が可逆であるための条件 -/
def isInvertible3 (A : Mat3) : Prop := det3 A ≠ 0

/-- 2×2行列の逆行列の公式（行列式≠0の場合）-/
def inv2 (A : Mat2) (h : det2 A ≠ 0) : Mat2 :=
  (1 / det2 A) • !![A 1 1, -A 0 1; -A 1 0, A 0 0]

/-- 余因子行列の(i,j)成分（2×2の場合）-/
def cofactor2 (A : Mat2) (i j : Fin 2) : ℝ :=
  (-1 : ℝ) ^ (i.val + j.val) * 
  (if i = 0 ∧ j = 0 then A 1 1
   else if i = 0 ∧ j = 1 then A 1 0
   else if i = 1 ∧ j = 0 then A 0 1
   else A 0 0)

/-- 左逆行列であるかの判定 -/
def isLeftInverse {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  B * A = 1

/-- 右逆行列であるかの判定 -/
def isRightInverse {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A * B = 1

/-! ### 補助：簡単な `simp` 用の補題 -/

@[simp] lemma det2_def (A : Mat2) :
  det2 A = A 0 0 * A 1 1 - A 0 1 * A 1 0 := rfl

@[simp] lemma det3_def (A : Mat3) :
  det3 A = A 0 0 * A 1 1 * A 2 2 + A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1
          - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2 - A 0 2 * A 1 1 * A 2 0 := rfl

@[simp] lemma inv2_def (A : Mat2) (h : det2 A ≠ 0) :
  inv2 A h = (1 / det2 A) • !![A 1 1, -A 0 1; -A 1 0, A 0 0] := rfl

/-! ## データ：この回で用いる具体的な行列 -/

/-- 2×2行列 A = [[3, 2], [1, 4]] （det = 10）-/
def A : Mat2 := !![3, 2; 1, 4]

/-- 2×2行列 B = [[2, -1], [3, 2]] （det = 7）-/
def B : Mat2 := !![2, -1; 3, 2]

/-- 3×3上三角行列 C = [[1, 2, 3], [0, 2, 1], [0, 0, 3]] （det = 6）-/
def C : Mat3 := !![1, 2, 3; 0, 2, 1; 0, 0, 3]

/-- 2×2行列 D（直交行列のスケール版）= [[3, 4], [-4, 3]] / 5 -/
def D : Mat2 := (1/5 : ℝ) • !![3, 4; -4, 3]

/-- 2×2単位行列のブロック [[1, 0], [0, 1]] -/
def I2 : Mat2 := 1

/-! ## 提出ルール
- 各問題は `theorem` / `lemma` / `example` のいずれかを完成させてください。
- 「計算問題」は `simp`, `ring`, `norm_num`, `field_simp` などで示せます。
- 「性質の問題」は `ext`, `simp`, `ring` 等の方針をコメントで示すと加点。
- 途中の補題を自由に作って構いません。 -/

/-! ---
## 基礎問題（5問）
--- -/

/-- **Q1** 行列 A の行列式を計算し、可逆であることを示せ。 -/
theorem Q1 : det2 A = 10 ∧ isInvertible2 A := by
  sorry
  -- ヒント：`constructor` → `simp [det2, A]` → `norm_num` と `simp [isInvertible2]` → `norm_num`。

/-- **Q2** 2×2行列 A の逆行列を計算し、A * A⁻¹ = I を確認せよ。 -/
theorem Q2 (h : det2 A ≠ 0) : A * (inv2 A h) = 1 := by
  sorry
  -- ヒント：`ext i j` → `fin_cases i; fin_cases j` → 
  -- `simp [A, inv2, mul_apply, Fin.sum_univ_two]` → `field_simp` → `ring`。

/-- **Q3** 積の逆行列の性質：(AB)⁻¹ = B⁻¹A⁻¹ を示せ（A, B は上で定義）。 -/
theorem Q3 (hA : det2 A ≠ 0) (hB : det2 B ≠ 0) (hAB : det2 (A * B) ≠ 0) :
  inv2 (A * B) hAB = inv2 B hB * inv2 A hA := by
  sorry
  -- ヒント：両辺に (A * B) を掛けて単位行列になることを示す、または成分計算。

/-- **Q4** 上三角行列 C の逆行列も上三角であることを示せ（対角成分の逆数から始まる）。 -/
theorem Q4 : ∃ C_inv : Mat3, isRightInverse C C_inv ∧ 
  C_inv 1 0 = 0 ∧ C_inv 2 0 = 0 ∧ C_inv 2 1 = 0 := by
  sorry
  -- ヒント：C_inv = !![1, -1, -1/6; 0, 1/2, -1/6; 0, 0, 1/3] を構成し、
  -- 右逆であることと下三角成分が0であることを確認。

/-- **Q5** 転置の逆行列の性質：(Aᵀ)⁻¹ = (A⁻¹)ᵀ を確認せよ（A で具体的に）。 -/
theorem Q5 (h : det2 A ≠ 0) : 
  inv2 (transpose A) (by simp [det2, A]; norm_num : det2 (transpose A) ≠ 0) = 
  transpose (inv2 A h) := by
  sorry
  -- ヒント：`ext i j` → `fin_cases` → `simp [inv2, transpose_apply, A]` → `norm_num`。

/-! ---
## チャレンジ（応用1問）
- 2×2ブロック行列の逆行列公式：
  M = [[A, B], [C, D]] (各ブロックは n×n) において、
  A が可逆で、Schur補行列 S = D - CA⁻¹B も可逆のとき、
  M⁻¹ = [[A⁻¹ + A⁻¹BS⁻¹CA⁻¹, -A⁻¹BS⁻¹], [-S⁻¹CA⁻¹, S⁻¹]]
  を証明せよ。具体例として 2×2 を 1×1 ブロック4つに分割した場合を扱う。
--- -/

/-- 2×2行列を1×1ブロック4つとして扱った場合の逆行列 -/
theorem Challenge : 
  -- M = [[3, 2], [1, 4]] の場合、各成分を1×1ブロックとして
  -- A = 3, B = 2, C = 1, D = 4
  -- Schur補行列 S = 4 - 1*(1/3)*2 = 4 - 2/3 = 10/3
  -- 逆行列の(0,0)成分は A⁻¹ + A⁻¹BS⁻¹CA⁻¹ = 1/3 + (1/3)*2*(3/10)*1*(1/3) = 2/5
  let M := A  -- [[3, 2], [1, 4]]
  let M_inv := inv2 M (by simp [det2, A]; norm_num : det2 M ≠ 0)
  M_inv 0 0 = 2/5 := by
  sorry
  /- ヒント：
     - `simp [inv2, A]` で逆行列の定義を展開
     - 分数の計算は `norm_num` で処理
     - ブロック行列の一般論は、1×1の場合は通常のスカラー演算に帰着
  -/

/-! ## 参考：動作確認コマンド（提出時は残してOK）
#check Q1
#check Q2
#check Q3
#check Q4
#check Q5
#check Challenge
-/

end ZenLA1.Session07