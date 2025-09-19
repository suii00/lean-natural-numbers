/-
ZEN大学「線形代数1」(MTH-1-C1-1030-004, 2025, オンデマンド)
第8回：行列の階数（基礎問題5＋チャレンジ1）— 提出形式：Lean 4 ファイル

提出物：このファイルの `sorry` をすべて消して証明／計算を完成させてください。
想定環境：Lean 4 + mathlib（最新版）。`lake exe cache get` 等で mathlib を取得してください。

学習目標（第8回）
- 行列の階数（rank）の定義と意味を理解する。
- 行基本変形による階数の計算方法を習得する。
- 階数と線形独立性・従属性の関係を学ぶ。
- 階数と連立方程式の解の存在性・一意性の関連を理解する。
- チャレンジ：階数・退化次数定理（rank-nullity theorem）の証明。
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.RowCol
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Finset.Card

namespace ZenLA1.Session08

open BigOperators Matrix
open scoped Matrix

/-! ## 下準備：階数の型定義と基本演算 -/

/-- m×n実行列の型 -/
abbrev MatrixMN (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- 列ベクトルが線形独立であるかの判定（簡易版）-/
def areColsIndependent {m n : ℕ} (A : MatrixMN m n) (cols : Finset (Fin n)) : Prop :=
  ∀ c : Fin n → ℝ, (∑ j in cols, c j • A.col j = 0) → (∀ j ∈ cols, c j = 0)

/-- 行が線形独立であるかの判定（簡易版）-/
def areRowsIndependent {m n : ℕ} (A : MatrixMN m n) (rows : Finset (Fin m)) : Prop :=
  ∀ c : Fin m → ℝ, (∑ i in rows, c i • A.row i = 0) → (∀ i ∈ rows, c i = 0)

/-- 階数：最大の線形独立な列ベクトルの個数（簡易定義）-/
def rank {m n : ℕ} (A : MatrixMN m n) : ℕ :=
  Finset.univ.image (fun s : Finset (Fin n) => if areColsIndependent A s then s.card else 0)
    |>.max'
    (by simp [Finset.image_nonempty, Finset.univ_nonempty] : _)

/-- 行階数：最大の線形独立な行ベクトルの個数（簡易定義）-/
def rowRank {m n : ℕ} (A : MatrixMN m n) : ℕ :=
  Finset.univ.image (fun s : Finset (Fin m) => if areRowsIndependent A s then s.card else 0)
    |>.max'
    (by simp [Finset.image_nonempty, Finset.univ_nonempty] : _)

/-- 階段行列であるかの判定（簡易版：上三角に近い形）-/
def isRowEchelon {m n : ℕ} (A : MatrixMN m n) : Prop :=
  ∀ i j k : Fin m, i < j → (∀ l : Fin n, l < k → A j l = 0) → A i k ≠ 0 → A j k = 0

/-- ピボット（非零要素）の位置を取得 -/
def pivotCol {m n : ℕ} (A : MatrixMN m n) (i : Fin m) : Option (Fin n) :=
  (Finset.univ.filter (fun j => A i j ≠ 0)).min

/-- 退化次数（nullity）：解空間の次元 -/
def nullity {m n : ℕ} (A : MatrixMN m n) : ℕ := n - rank A

/-! ### 補助：簡単な `simp` 用の補題 -/

@[simp] lemma col_def {m n : ℕ} (A : MatrixMN m n) (j : Fin n) :
  A.col j = fun i => A i j := rfl

@[simp] lemma row_def {m n : ℕ} (A : MatrixMN m n) (i : Fin m) :
  A.row i = fun j => A i j := rfl

/-! ## データ：この回で用いる具体的な行列 -/

/-- 3×4行列（rank = 2）-/
def A : MatrixMN 3 4 := !![1, 2, 3, 4; 2, 4, 6, 8; 0, 0, 1, 0]

/-- 3×3上三角行列（rank = 3）-/
def B : MatrixMN 3 3 := !![1, 2, 3; 0, 1, 2; 0, 0, 1]

/-- 2×3行列（rank = 2）-/
def C : MatrixMN 2 3 := !![1, 0, 2; 0, 1, -1]

/-- 4×3行列（rank = 2）-/
def D : MatrixMN 4 3 := !![1, 2, 3; 2, 4, 6; 0, 1, 1; 1, 3, 4]

/-- 3×3退化行列（rank = 2）-/
def E : MatrixMN 3 3 := !![1, 2, 3; 4, 5, 6; 7, 8, 9]

/-! ## 提出ルール
- 各問題は `theorem` / `lemma` / `example` のいずれかを完成させてください。
- 「計算問題」は具体的な階数の値を求めます。
- 「性質の問題」は `ext`, `simp`, `ring` 等の方針をコメントで示すと加点。
- 途中の補題を自由に作って構いません。 -/

/-! ---
## 基礎問題（5問）
--- -/

/-- **Q1** 上三角行列 B の階数は対角成分が全て非零なら3であることを示せ。 -/
theorem Q1 : B 0 0 ≠ 0 ∧ B 1 1 ≠ 0 ∧ B 2 2 ≠ 0 := by
  sorry
  -- ヒント：`simp [B]` → `norm_num` で各対角成分が非零であることを確認。
  -- 上三角かつ対角非零 → フルランクの原理。

/-- **Q2** 行列 C の第1列と第2列が線形独立であることを示せ。 -/
theorem Q2 : ∀ c₁ c₂ : ℝ, c₁ • C.col 0 + c₂ • C.col 1 = 0 → c₁ = 0 ∧ c₂ = 0 := by
  sorry
  -- ヒント：成分ごとに展開して連立方程式を解く。
  -- `ext i` → `fin_cases i` → `simp [C]` で係数の条件を導出。

/-- **Q3** 行列 D において第1行と第2行が線形従属（比例）であることを示せ。 -/
theorem Q3 : D.row 1 = 2 • D.row 0 := by
  sorry
  -- ヒント：`ext j` → `fin_cases j` → `simp [D]` → `norm_num`。

/-- **Q4** 行列 E の行列式が0であることを確認し、階数が3未満であることを示せ。 -/
theorem Q4 : 
  -- 3×3行列の行列式（第4回の定義を使用）
  let det3_E := E 0 0 * E 1 1 * E 2 2 + E 0 1 * E 1 2 * E 2 0 + E 0 2 * E 1 0 * E 2 1
              - E 0 0 * E 1 2 * E 2 1 - E 0 1 * E 1 0 * E 2 2 - E 0 2 * E 1 1 * E 2 0
  det3_E = 0 := by
  sorry
  -- ヒント：`simp [E]` → `norm_num` で行列式を計算。
  -- 行列式 = 0 ⇔ 階数 < 3（正方行列の場合）。

/-- **Q5** 行列 A の第3行を第1行に加えても階数は変わらないことを示せ（行基本変形）。 -/
theorem Q5 : 
  let A' := fun i j => if i = 0 then A 0 j + A 2 j else A i j
  -- 階数の不変性を示すために、変形後も第3列が独立であることを確認
  A' 0 2 ≠ 0 ∨ A' 1 2 ≠ 0 ∨ A' 2 2 ≠ 0 := by
  sorry
  -- ヒント：行基本変形は階数を保存する。
  -- `simp [A]` で具体的に計算。

/-! ---
## チャレンジ（応用1問）
- 階数・退化次数定理（rank-nullity theorem）：
  m×n行列 A に対して、rank(A) + nullity(A) = n を証明せよ。
  具体例として、2×3行列 C で rank(C) = 2, nullity(C) = 1 を確認する。
--- -/

theorem Challenge :
  -- 行列 C（2×3）について、rank + nullity = 3 を確認
  -- rank(C) = 2（Q2より第1,2列が独立で最大）
  -- したがって nullity(C) = 3 - 2 = 1
  let rank_C := 2  -- 仮定：適切に定義された階数
  let nullity_C := 1  -- 退化次数
  rank_C + nullity_C = 3 := by
  sorry
  /- ヒント：
     - 一般の証明：解空間の次元 = n - rank（線形写像の基本定理）
     - C の場合：2つの独立列 → 階数2 → 退化次数 = 3-2 = 1
     - 解空間の基底ベクトルを具体的に構成することも可能
  -/

/-! ## 参考：動作確認コマンド（提出時は残してOK）
#check Q1
#check Q2
#check Q3
#check Q4
#check Q5
#check Challenge
-/

end ZenLA1.Session08