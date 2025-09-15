/-
ZEN大学「線形代数1」(MTH-1-C1-1030-004, 2025, オンデマンド)
第5回：グラフと行列（基礎問題5＋チャレンジ1）— 提出形式：Lean 4 ファイル

提出物：このファイルの `sorry` をすべて消して証明／計算を完成させてください。
想定環境：Lean 4 + mathlib（最新版）。`lake exe cache get` 等で mathlib を取得してください。

学習目標（第5回）
- グラフの隣接行列表現と行列演算の対応関係を理解する。
- 隣接行列のべき乗とグラフ上の歩数（walk）の関係を形式化する。
- グラフのラプラシアン行列と次数行列の性質を学ぶ。
- 無向グラフの連結性と行列の性質の関連を探る。
- チャレンジ：完全グラフのラプラシアン行列の固有値計算。
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct

namespace ZenLA1.Session05

open BigOperators Matrix
open scoped Matrix

/-! ### 数値簡約のための補助補題 -/

@[simp] lemma one_add_one_eq_two_real : (1 : ℝ) + 1 = 2 := by
  norm_num

/-! ## 下準備：グラフと行列の型定義 -/

/-- 頂点数 n の隣接行列（0-1値の実数行列として扱う）。 -/
abbrev AdjMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- 頂点の次数（隣接する辺の数）を計算。 -/
def degree {n : ℕ} (A : AdjMatrix n) (i : Fin n) : ℝ :=
  ∑ j : Fin n, A i j

/-- 次数行列（対角成分が各頂点の次数）。 -/
def degreeMatrix {n : ℕ} (A : AdjMatrix n) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal (fun i => degree A i)

/-- ラプラシアン行列 L = D - A（次数行列 - 隣接行列）。 -/
def laplacian {n : ℕ} (A : AdjMatrix n) : Matrix (Fin n) (Fin n) ℝ :=
  degreeMatrix A - A

/-- 隣接行列が無向グラフを表す（対称行列）。 -/
def isUndirected {n : ℕ} (A : AdjMatrix n) : Prop :=
  transpose A = A

/-- 隣接行列が単純グラフを表す（対角成分0、他は0または1）。 -/
def isSimpleGraph {n : ℕ} (A : AdjMatrix n) : Prop :=
  (∀ i : Fin n, A i i = 0) ∧ (∀ i j : Fin n, A i j = 0 ∨ A i j = 1)

/-! ### 補助：簡単な `simp` 用の補題 -/

@[simp] lemma degree_def {n : ℕ} (A : AdjMatrix n) (i : Fin n) :
  degree A i = ∑ j : Fin n, A i j := rfl

@[simp] lemma degreeMatrix_def {n : ℕ} (A : AdjMatrix n) (i j : Fin n) :
  degreeMatrix A i j = if i = j then degree A i else 0 := by
  simp [degreeMatrix, diagonal_apply]

@[simp] lemma laplacian_def {n : ℕ} (A : AdjMatrix n) :
  laplacian A = degreeMatrix A - A := rfl

/-! ### 補助：K₃ 専用の次数計算（K3 定義の後に置く） -/

/-! ## データ：この回で用いる具体的なグラフ -/

/-- 4頂点のパスグラフ: 0-1-2-3 -/
def pathGraph : AdjMatrix 4 :=
  !![0, 1, 0, 0;
     1, 0, 1, 0;
     0, 1, 0, 1;
     0, 0, 1, 0]

/-- 4頂点のサイクルグラフ: 0-1-2-3-0 -/
def cycleGraph : AdjMatrix 4 :=
  !![0, 1, 0, 1;
     1, 0, 1, 0;
     0, 1, 0, 1;
     1, 0, 1, 0]

/-- 3頂点の完全グラフ K₃ -/
def K3 : AdjMatrix 3 :=
  !![0, 1, 1;
     1, 0, 1;
     1, 1, 0]

/-- 4頂点の完全グラフ K₄ -/
def K4 : AdjMatrix 4 :=
  !![0, 1, 1, 1;
     1, 0, 1, 1;
     1, 1, 0, 1;
     1, 1, 1, 0]

@[simp] lemma sum_row_K4 (i : Fin 4) : ∑ j : Fin 4, K4 i j = 3 := by
  fin_cases i <;>
    (simp [K4, Fin.sum_univ_four]; norm_num)

@[simp] lemma sum_ite_fin4 (i : Fin 4) (x : ℝ) :
  ∑ j : Fin 4, (if i = j then x else 0) = x := by
  fin_cases i <;> simp [Fin.sum_univ_four]

lemma degree_K3 (i : Fin 3) : degree K3 i = 2 := by
  fin_cases i <;>
    simp [degree, K3, Fin.sum_univ_three]

@[simp] lemma sum_row_K3 (i : Fin 3) : ∑ j : Fin 3, K3 i j = 2 := by
  simpa [degree] using degree_K3 i

/-! ## 提出ルール
- 各問題は `theorem` / `lemma` / `example` のいずれかを完成させてください。
- 「計算問題」は `simp`, `ring`, `norm_num` などで示せます。
- 「性質の問題」は `ext`, `simp`, `ring` 等の方針をコメントで示すと加点。
- 途中の補題を自由に作って構いません。 -/

/-! ---
## 基礎問題（5問）
--- -/

/-- **Q1** パスグラフの各頂点の次数を計算せよ（端点は次数1、中間は次数2）。 -/
theorem Q1 :
  degree pathGraph 0 = 1 ∧
  degree pathGraph 1 = 2 ∧
  degree pathGraph 2 = 2 ∧
  degree pathGraph 3 = 1 := by
  constructor
  · simp [degree, pathGraph, Fin.sum_univ_four]
  · constructor
    · simp [degree, pathGraph, Fin.sum_univ_four]
    · constructor
      · simp [degree, pathGraph, Fin.sum_univ_four]
      · simp [degree, pathGraph, Fin.sum_univ_four]
  -- ヒント：`simp [degree, pathGraph, Fin.sum_univ_four]` → `norm_num`。

/-- **Q2** サイクルグラフが無向グラフであることを示せ。 -/
theorem Q2 : isUndirected cycleGraph := by
  unfold isUndirected
  ext i j
  -- 各成分で一致を示す（対称性）
  fin_cases i <;> fin_cases j <;> simp [cycleGraph]
  -- ヒント：`simp [isUndirected, cycleGraph]` → `ext` → `fin_cases` → `simp`。

/-- **Q3** 隣接行列の2乗の (i,j) 成分は、頂点 i から j への長さ2の歩数を表す。
パスグラフで頂点0から頂点2への長さ2の歩数を計算せよ。 -/
theorem Q3 : (pathGraph * pathGraph) 0 2 = 1 := by
  -- 0→1→2 の唯一の長さ2の歩が寄与
  simp [mul_apply, pathGraph, Fin.sum_univ_four]
  -- ヒント：`simp [mul_apply, pathGraph, Fin.sum_univ_four]` → `norm_num`。

/-- **Q4** 完全グラフ K₃ のラプラシアン行列を計算せよ。 -/
theorem Q4 : laplacian K3 = !![2, -1, -1; -1, 2, -1; -1, -1, 2] := by
  ext i j
  -- 小次元なので総当たりで評価するのが確実
  fin_cases i <;> fin_cases j <;>
    simp [laplacian, degreeMatrix_def, K3, Fin.sum_univ_three]
  -- ヒント：まず次数を計算 `simp [laplacian, degreeMatrix, degree, K3]`、
  -- その後 `ext` → `fin_cases` → `simp` → `norm_num`。

/-- **Q5** ラプラシアン行列の行和（各行の成分の和）は常に0であることを示せ。 -/
theorem Q5 {n : ℕ} (A : AdjMatrix n) (_hSimple : isSimpleGraph A)
    (_hUndirected : isUndirected A) (i : Fin n) :
  ∑ j : Fin n, laplacian A i j = 0 := by
  classical
  -- 行和は (∑ D行) − (∑ A行)。D行和は degree，A行和も degree。
  have hdiag : ∑ j : Fin n, degreeMatrix A i j = degree A i := by
    simp [degreeMatrix_def]
  simpa [laplacian, Matrix.sub_apply, Finset.sum_sub_distrib, hdiag, degree]
  -- ヒント：`simp [laplacian, degreeMatrix, degree]` で展開、
  -- 対角成分とその他で場合分けして計算。

/-! ---
## チャレンジ（応用1問）
- 完全グラフ K_n のラプラシアン行列は、固有値 0（重複度1）と
  固有値 n（重複度 n-1）を持つことを証明せよ。
- 具体的に K₄ について、全1ベクトルが固有値0の固有ベクトルであることを示す。
--- -/

/-- 全1ベクトル -/
def allOnes (n : ℕ) : Fin n → ℝ := fun _ => 1

/-- 全1行列 J_n -/
def J (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun _ _ => (1 : ℝ)

/-- K_n のラプラシアン行列（一般形）-/
def laplacianKn (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  -- 一般に K_n のラプラシアンは L = n I - J（J は全1行列）
  (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) - J n

theorem Challenge :
  -- K₄のラプラシアン行列に全1ベクトルを掛けると0ベクトルになる（固有値0）
  (laplacian K4).mulVec (allOnes 4) = 0 := by
  classical
  ext i
  -- mulVec の成分は行和に等しいので、(3 − 3) = 0
  simp [Matrix.mulVec, dotProduct, allOnes, laplacian, Matrix.sub_apply,
        degreeMatrix_def, degree, sum_row_K4, Fin.sum_univ_four,
        Finset.sum_sub_distrib]
  /- ヒント：
     - `ext i` でベクトルの各成分を示す
     - `simp [laplacian, mulVec, dotProduct, allOnes]` で展開
     - K₄の構造から、各行の和が0になることを使う
     - `fin_cases i` で各成分を個別に計算してもよい
  -/

/-! ## 参考：動作確認コマンド（提出時は残してOK）
#check Q1
#check Q2
#check Q3
#check Q4
#check Q5
#check Challenge
-/

end ZenLA1.Session05
