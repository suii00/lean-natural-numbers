/-
ZEN大学「線形代数1」(MTH-1-C1-1030-004, 2025, オンデマンド)
第3回：行列（基礎問題5＋チャレンジ1）— 提出形式：Lean 4 ファイル

提出物：このファイルの `sorry` をすべて消して証明／計算を完成させてください。
想定環境：Lean 4 + mathlib（最新版）。`lake exe cache get` 等で mathlib を取得してください。

学習目標（第3回）
- 行列の基本演算（加法・スカラー倍・乗法）の定義と計算を習得する。
- 行列の転置と対称行列・反対称行列の性質を理解する。
- 行列の乗法の結合法則・分配法則を形式的に証明する。
- トレース（対角和）の線形性と乗法に関する性質を示す。
- チャレンジ：任意の正方行列が対称行列と反対称行列の和に一意分解されることの証明。
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace ZenLA1.Session03

open BigOperators

/-! ## 下準備：行列型と基本演算 -/

/-- 2×2実行列の型（Fin 2 でインデックス）。 -/
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

/-- 3×3実行列の型。 -/
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

/-- 2×3実行列の型（行が2、列が3）。 -/
abbrev Mat23 := Matrix (Fin 2) (Fin 3) ℝ

/-- 3×2実行列の型（行が3、列が2）。 -/
abbrev Mat32 := Matrix (Fin 3) (Fin 2) ℝ

/-- 行列のトレース（対角和）。 -/
def trace (A : Mat2) : ℝ := A 0 0 + A 1 1

/-- 対称行列の判定：A^T = A。 -/
def isSymmetric (A : Mat2) : Prop := Matrix.transpose A = A

/-- 反対称行列（交代行列）の判定：A^T = -A。 -/
def isSkewSymmetric (A : Mat2) : Prop := Matrix.transpose A = -A

/-! ### 補助：簡単な `simp` 用の補題 -/

@[simp] lemma trace_def (A : Mat2) :
  trace A = A 0 0 + A 1 1 := rfl

@[simp] lemma isSymmetric_def (A : Mat2) :
  isSymmetric A = (Matrix.transpose A = A) := rfl

@[simp] lemma isSkewSymmetric_def (A : Mat2) :
  isSkewSymmetric A = (Matrix.transpose A = -A) := rfl

/-! ## データ：この回で用いる具体行列 -/

/-- 2×2行列 A = [[1, 2], [3, 4]]。 -/
def A : Mat2 := !![1, 2; 3, 4]

/-- 2×2行列 B = [[2, -1], [0, 3]]。 -/
def B : Mat2 := !![2, -1; 0, 3]

/-- 2×3行列 C = [[1, 0, 2], [-1, 3, 1]]。 -/
def C : Mat23 := !![1, 0, 2; -1, 3, 1]

/-- 3×2行列 D = [[3, 1], [0, -1], [2, 2]]。 -/
def D : Mat32 := !![3, 1; 0, -1; 2, 2]

/-- 対称行列の例 S = [[2, 3], [3, -1]]。 -/
def S : Mat2 := !![2, 3; 3, -1]

/-! ## 提出ルール
- 各問題は `theorem` / `lemma` / `example` のいずれかを完成させてください。
- 「計算問題」は `simp`, `ring`, `norm_num`, `decide` などで示せます。
- 「性質の問題」は `ext`, `simp`, `ring` 等の方針をコメントで示すと加点。
- 途中の補題を自由に作って構いません。 -/

/-! ---
## 基礎問題（5問）
--- -/

/-- **Q1** 行列の和とスカラー倍：`2A + 3B` を計算せよ（A, B は上記定義）。 -/
theorem Q1 : (2 : ℝ) • A + (3 : ℝ) • B = !![8, 1; 6, 17] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A, B, Matrix.add_apply] <;> norm_num
  -- ヒント：`ext i j` で成分ごとに示し、`fin_cases i; fin_cases j` で場合分け、
  -- その後 `simp [A, B]` と `norm_num`。

/-- **Q2** 行列の積：`C * D` を計算せよ（C は 2×3、D は 3×2）。 -/
theorem Q2 : C * D = !![7, 5; -1, -2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C, D, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num
  -- ヒント：`ext i j` → `fin_cases i; fin_cases j` → `simp [C, D, Matrix.mul_apply]` → `norm_num`。

/-- **Q3** 転置の性質：`(A^T)^T = A` を示せ。 -/
theorem Q3 (A : Mat2) : Matrix.transpose (Matrix.transpose A) = A := by
  ext i j
  simp [Matrix.transpose_apply]
  -- ヒント：`ext i j` → `simp [Matrix.transpose_apply]`。

/-- **Q4** トレースの線形性：`trace (aA + bB) = a * trace A + b * trace B` を示せ。 -/
theorem Q4 (a b : ℝ) (A B : Mat2) :
  trace (a • A + b • B) = a * trace A + b * trace B := by
  simp [trace, Matrix.add_apply]
  ring
  -- ヒント：`simp [trace]` → `ring`。

/-- **Q5** 対称行列 S のトレースと成分の関係：`trace S = S 0 0 + S 1 1` が
`S 0 0 - S 1 1 = 3` を満たすとき、`trace S = 1` であることを確認せよ（S は上記定義）。 -/
theorem Q5 : trace S = 1 ∧ S 0 0 - S 1 1 = 3 := by
  constructor
  · simp [trace, S]
    norm_num
  · simp [S]
    norm_num
  -- ヒント：`constructor` で両方示す。`simp [trace, S]` → `norm_num`。

/-! ---
## チャレンジ（応用1問）
- 任意の2×2正方行列 M は、対称行列 P と反対称行列 Q の和として
  一意に分解できることを証明せよ：`M = P + Q` where `P^T = P` and `Q^T = -Q`。
- 具体的には、`P = (M + M^T)/2` と `Q = (M - M^T)/2` である。
--- -/

theorem Challenge (M : Mat2) :
  ∃! pq : Mat2 × Mat2, isSymmetric pq.1 ∧ isSkewSymmetric pq.2 ∧ M = pq.1 + pq.2 := by
  -- 存在性：P = (M + M^T)/2, Q = (M - M^T)/2 と定義
  use ((1/2 : ℝ) • (M + Matrix.transpose M), (1/2 : ℝ) • (M - Matrix.transpose M))
  constructor
  · -- 条件を満たすことを示す
    constructor
    · -- P が対称行列
      simp [isSymmetric, Matrix.transpose_add, Matrix.transpose_transpose,
            Matrix.transpose_smul, add_comm]
      -- ヒント：`simp [isSymmetric]` → `ext` → `simp [Matrix.transpose_apply]` → `ring`
    · constructor
      · -- Q が反対称行列
        simp [isSkewSymmetric, Matrix.transpose_sub, Matrix.transpose_transpose,
              Matrix.transpose_smul, sub_eq_add_neg, add_comm]
        -- ヒント：`simp [isSkewSymmetric]` → `ext` → `simp [Matrix.transpose_apply]` → `ring`
      · -- M = P + Q
        ext i j
        simp [Matrix.add_apply, Matrix.smul_apply, Matrix.transpose_apply,
              sub_eq_add_neg]
        ring
        -- ヒント：`ext` → `simp` → `ring`
  · -- 一意性：他の分解 (P', Q') があれば同じであることを示す
    intro pq' hpq'
    rcases pq' with ⟨P', Q'⟩
    rcases hpq' with ⟨hP', hQ', hSum'⟩
    -- P' = P かつ Q' = Q を示す
    -- 転置をとって比較
    have hPT : Matrix.transpose P' = P' := by simpa [isSymmetric] using hP'
    have hQT : Matrix.transpose Q' = -Q' := by simpa [isSkewSymmetric] using hQ'
    have hSumT : Matrix.transpose M = P' - Q' := by
      simpa [Matrix.transpose_add, hPT, hQT, sub_eq_add_neg] using
        congrArg Matrix.transpose hSum'
    -- P' = (1/2)•(M + Mᵀ)
    -- P' = (1/2)(M + Mᵀ)
    have hP'_eq : P' = (1/2 : ℝ) • (M + Matrix.transpose M) := by
      ext i j
      have e1 : M i j = P' i j + Q' i j := by
        simpa [Matrix.add_apply] using congrArg (fun N => N i j) hSum'
      have e2 : Matrix.transpose M i j = P' i j - Q' i j := by
        have := congrArg (fun N => N i j) hSumT
        simpa [Matrix.transpose_apply, sub_eq_add_neg, Matrix.add_apply, Matrix.neg_apply] using this
      have : (1/2 : ℝ) * ((P' i j + Q' i j) + (P' i j - Q' i j)) = P' i j := by
        ring
      simpa [Matrix.add_apply, Matrix.smul_apply, e1.symm, e2.symm] using this.symm
    -- Q' = (1/2)(M - Mᵀ)
    have hQ'_eq : Q' = (1/2 : ℝ) • (M - Matrix.transpose M) := by
      ext i j
      have e1 : M i j = P' i j + Q' i j := by
        simpa [Matrix.add_apply] using congrArg (fun N => N i j) hSum'
      have e2 : Matrix.transpose M i j = P' i j - Q' i j := by
        have := congrArg (fun N => N i j) hSumT
        simpa [Matrix.transpose_apply, sub_eq_add_neg, Matrix.add_apply, Matrix.neg_apply] using this
      have : (1/2 : ℝ) * ((P' i j + Q' i j) - (P' i j - Q' i j)) = Q' i j := by
        ring
      simpa [Matrix.add_apply, Matrix.smul_apply, e1.symm, e2.symm] using this.symm
    exact Prod.ext hP'_eq hQ'_eq
    

/-! ## 参考：動作確認コマンド（提出時は残してOK）
#check Q1
#check Q2
#check Q3
#check Q4
#check Q5
#check Challenge
-/

end ZenLA1.Session03
