/-
file: HW_S2.lean
ZEN大学「線形代数1」（MTH-1-C1-1030-004, 2025, オンデマンド）
提出用 Lean ファイル雛形（S2：空間ベクトル—平面・直線／内積・射影／線形変換／体積）

使い方：
- 各定理 `S2_P01`〜`S2_P05` と `S2_CH` の `sorry` を証明に置き換えてください。
- 依存：Lean 4 + mathlib4（`import Mathlib` 等でビルド可）
- 既定の 3D ベクトルは `(ℝ × ℝ × ℝ)` を用います（成分は `u.1, u.2.1, u.2.2`）。

採点目安（参考）：
- 基礎 P01..P05 各10点（正しさ6・明快さ2・Lean記法2）
- チャレンジ CH 15点（正しさ9・構造的洞察6）
-/

import Mathlib

namespace HW_S2

open Matrix
open scoped BigOperators

/-- (補助) 3次元のドット積（成分定義） -/
def dot3 (u v : ℝ × ℝ × ℝ) : ℝ :=
  u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

/-- (補助) 3次元ベクトルのスカラー倍（成分定義） -/
def smul3 (a : ℝ) (u : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (a * u.1, a * u.2.1, a * u.2.2)

/-- (補助) 2点 P,Q とパラメータ t による直線の点 -/
def lineParam (P Q : ℝ × ℝ × ℝ) (t : ℝ) : ℝ × ℝ × ℝ :=
  ( P.1     + t * (Q.1     - P.1)
  , P.2.1   + t * (Q.2.1   - P.2.1)
  , P.2.2   + t * (Q.2.2   - P.2.2) )

/-- (補助) 単位ベクトル `u` への射影（ベクトル）
`projUnit3 u v = ⟨⟪v,u⟫ u⟩` を座標定義で与える（ここでは `dot3` を使用）。 -/
def projUnit3 (u v : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let s := dot3 v u
  (s * u.1, s * u.2.1, s * u.2.2)

/-- (補助) 3つのベクトルを**行**に並べた 3×3 行列 -/
def matRowsOf (u v w : ℝ × ℝ × ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![u.1, u.2.1, u.2.2],
    ![v.1, v.2.1, v.2.2],
    ![w.1, w.2.1, w.2.2]]

/-! ## S2_P01
(1) タイトル：平面 `Ax+By+Cz=D` 上の点の構成
(2) 学習目標：平面方程式への代入検証（除算の扱い）
(3) 課題文：`C ≠ 0` とする。任意の `x y : ℝ` で
    `P = (x, y, (D - A*x - B*y)/C)` は `A*x + B*y + C*z = D` を満たす。
(4) Lean目標：`A*x + B*y + C*((D - A*x - B*y)/C) = D`
(5) ヒント：`field_simp [hC]` → `ring`
-/
theorem S2_P01 (A B C D x y : ℝ) (hC : C ≠ 0) :
    A * x + B * y + C * ((D - A * x - B * y) / C) = D := by
  have hDiv : ((D - A * x - B * y) / C) * C = D - A * x - B * y := by
    field_simp [hC]
  have hDiv' : C * ((D - A * x - B * y) / C) = D - A * x - B * y := by
    simpa [mul_comm] using hDiv
  calc
    A * x + B * y + C * ((D - A * x - B * y) / C)
        = A * x + B * y + (D - A * x - B * y) := by simp [hDiv']
    _ = D := by ring


/-! ## S2_P02
(1) タイトル：2点を通る直線のパラメータ表示
(2) 学習目標：`lineParam P Q t` の端点一致 `t=0,1` の証明
(3) 課題文：任意の `P Q` で `lineParam P Q 0 = P ∧ lineParam P Q 1 = Q`
(4) Lean目標：`lineParam P Q 0 = P ∧ lineParam P Q 1 = Q`
(5) ヒント：`ext`→`simp [lineParam, sub_eq_add_neg]`→`ring`
-/
theorem S2_P02 (P Q : ℝ × ℝ × ℝ) :
    lineParam P Q 0 = P ∧ lineParam P Q 1 = Q := by
  constructor
  · ext <;> simp [lineParam]
  · ext <;> simp [lineParam, sub_eq_add_neg]


/-! ## S2_P03
(1) タイトル：3次元ドット積の加法性（第1引数）
(2) 学習目標：`dot3 (u+w) v = dot3 u v + dot3 w v`
(3) Lean目標：上記等式
(4) ヒント：`simp [dot3, add_mul]`→`ring`
-/
theorem S2_P03 (u v w : ℝ × ℝ × ℝ) :
    dot3 (u + w) v = dot3 u v + dot3 w v := by
  simp [dot3, add_mul]
  ring_nf


/-! ## S2_P04
(1) タイトル：3次元ドット積の斉次性（第1引数）
(2) 学習目標：`dot3 (a•u) v = a * dot3 u v`
(3) Lean目標：`dot3 (smul3 a u) v = a * dot3 u v`
(4) ヒント：`simp [dot3, smul3]`→`ring`
-/
theorem S2_P04 (a : ℝ) (u v : ℝ × ℝ × ℝ) :
    dot3 (smul3 a u) v = a * dot3 u v := by
  simp [dot3, smul3]
  ring_nf


/-! ## S2_P05
(1) タイトル：単位ベクトルへの射影の固定性（`v` が `u` に平行）
(2) 学習目標：`projUnit3` の定義と P04 を組み合わせる
(3) 課題文：`dot3 u u = 1` かつ `v = smul3 a u` なら `projUnit3 u v = v`
(4) Lean目標：`dot3 u u = 1 → v = smul3 a u → projUnit3 u v = v`
(5) ヒント：`have : dot3 v u = a := by ...` → `simp [projUnit3]`
-/
theorem S2_P05 (u v : ℝ × ℝ × ℝ) (a : ℝ) :
    dot3 u u = 1 → v = smul3 a u → projUnit3 u v = v := by
  intro hnorm hv
  subst hv
  have hdot : dot3 (smul3 a u) u = a := by
    simpa [hnorm] using (S2_P04 a u u)
  have hproj : projUnit3 u (smul3 a u) =
      (dot3 (smul3 a u) u * u.1,
        dot3 (smul3 a u) u * u.2.1,
        dot3 (smul3 a u) u * u.2.2) := rfl
  have htuple : (dot3 (smul3 a u) u * u.1,
        dot3 (smul3 a u) u * u.2.1,
        dot3 (smul3 a u) u * u.2.2) =
      (a * u.1, a * u.2.1, a * u.2.2) := by
    simp [hdot]
  have hsmul : smul3 a u = (a * u.1, a * u.2.1, a * u.2.2) := rfl
  exact hproj.trans (htuple.trans hsmul.symm)


/-! ## S2_CH（チャレンジ）
(1) タイトル：線形変換による体積の変化は `|det A|` 倍
(2) 学習目標：`Matrix.det_mul` と `abs_mul` を用いる
(3) 課題文：`A : Matrix (Fin 3) (Fin 3) ℝ` とし，`B = matRowsOf u v w`
    このとき `|det (A ⬝ B)| = |det A| * |det B|`
(4) Lean目標：`|Matrix.det (A ⬝ matRowsOf u v w)| = |Matrix.det A| * |Matrix.det (matRowsOf u v w)|`
(5) ヒント：`simpa [Matrix.det_mul, abs_mul]`
-/
theorem S2_CH (A : Matrix (Fin 3) (Fin 3) ℝ)
    (u v w : ℝ × ℝ × ℝ) :
    abs (Matrix.det (A * matRowsOf u v w)) =
      abs (Matrix.det A) * abs (Matrix.det (matRowsOf u v w)) := by
  simp [Matrix.det_mul, abs_mul]

end HW_S2
