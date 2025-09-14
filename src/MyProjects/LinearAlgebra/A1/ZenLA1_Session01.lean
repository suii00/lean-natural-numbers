/-
ZEN大学「線形代数1」(MTH-1-C1-1030-004, 2025, オンデマンド)
第1回：ガイダンス（基礎問題5＋チャレンジ1）— 提出形式：Lean 4 ファイル

提出物：このファイルの `sorry` をすべて消して証明／計算を完成させてください。
想定環境：Lean 4 + mathlib（最新版）。`lake exe cache get` 等で mathlib を取得してください。

学習目標（第1回）
- R^3 のベクトル演算（加法・スカラー倍）と「位置ベクトル／差ベクトル」の扱いに慣れる。
- 標準基底 e1,e2,e3 の役割を Lean 上で確認し、座標表示の正当性を形式化する。
- 自作の内積（dot）と二乗ノルム（normSq）を定義し、基本性質（対称性・分配則の一部）を示す。
- チャレンジ：平行四辺形法則（parallelogram law）の形式的証明。
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace ZenLA1.Session01

/-! ## 下準備：R^3・内積・基底 -/

/-- 実3次元ベクトルを単純に積型で表す（成分は (x, y, z) ）。 -/
abbrev R3 := ℝ × ℝ × ℝ

/-- 成分表示の内積。今回は自作定義を用いる（EuclideanSpace は使わない）。 -/
def dot (u v : R3) : ℝ :=
  u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

notation:70 "⟪" u "," v "⟫" => dot u v

/-- 二乗ノルム。`‖u‖^2` に相当。平方根は扱わず、まずは二乗までを用いる。 -/
def normSq (u : R3) : ℝ := dot u u

/-- 2点 A, B の差ベクトル（位置ベクトルとしての (x,y,z) を用いる）。 -/
def vec (A B : R3) : R3 := (B.1 - A.1, B.2.1 - A.2.1, B.2.2 - A.2.2)

/-- 標準基底 -/
def e1 : R3 := (1, 0, 0)
def e2 : R3 := (0, 1, 0)
def e3 : R3 := (0, 0, 1)

/-! ### 補助：簡単な `simp` 用の補題 -/

@[simp] lemma dot_def (u v : R3) :
  ⟪u, v⟫ = u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2 := rfl

@[simp] lemma vec_def (A B : R3) :
  vec A B = (B.1 - A.1, B.2.1 - A.2.1, B.2.2 - A.2.2) := rfl

@[simp] lemma normSq_def (u : R3) : normSq u = ⟪u, u⟫ := rfl

@[simp] lemma e1_def : e1 = (1,0,0) := rfl
@[simp] lemma e2_def : e2 = (0,1,0) := rfl
@[simp] lemma e3_def : e3 = (0,0,1) := rfl

/-! ## データ：この回で用いる具体ベクトル -/
def U : R3 := (2, -1, 0)
def V : R3 := (1, 3, 4)
def A : R3 := (1, -2, 3)
def B : R3 := (4,  2, -1)

/-! ## 提出ルール
- 各問題は `theorem` / `lemma` / `example` のいずれかを完成させてください。
- 「計算問題」は両辺が等しいことを `simp`, `ring`, `norm_num` などで示せます。
- 「性質の問題」は `simp [dot]`, `ext`, `ring` 等の方針をコメントで示すと加点。
- 途中の補題を自由に作って構いません。 -/

/-! ---
## 基礎問題（5問）
--- -/

/-- **Q1(a)** 2点 A(1,-2,3), B(4,2,-1) に対し、差ベクトル `→AB` を求めよ。 -/
theorem Q1a : vec A B = (3, 4, -4) := by
  sorry
  -- ヒント：`simp [vec, A, B]` または `rfl` 展開 → 各成分を算術簡約。
  -- `norm_num` が整数計算に便利。

/-- **Q1(b)** `|→AB|^2 = 41` を示せ（平方根は使わず二乗ノルムで確認）。 -/
theorem Q1b : normSq (vec A B) = 41 := by
  sorry
  -- ヒント：`simp [normSq, dot, vec, A, B]` の後に `norm_num` または `ring`。

/-- **Q2** `U=(2,-1,0), V=(1,3,4)` に対し、`2U - 3V` を計算せよ。 -/
theorem Q2 : (2 : ℝ) • U - (3 : ℝ) • V = (1, -11, -12) := by
  sorry
  -- ヒント：`simp [U, V]` で各成分のスカラー倍→加減算に還元。

/-- **Q3** 加法可換律 `u + v = v + u` を R^3 で示せ（全称命題）。 -/
theorem Q3 (u v : R3) : u + v = v + u := by
  sorry
  -- ヒント：`simpa using add_comm u v`。

/-- **Q4** 任意の `(x,y,z)` は標準基底で分解できることを示せ。 -/
theorem Q4 (x y z : ℝ) :
    (x, y, z) = x • e1 + y • e2 + z • e3 := by
  sorry
  -- ヒント：`simp [e1, e2, e3]`。

/-- **Q5** 標準基底との内積：`⟪(x,y,z), e1⟫ = x` を示せ。 -/
theorem Q5 (x y z : ℝ) :
    ⟪(x, y, z), e1⟫ = x := by
  sorry
  -- ヒント：`simp [dot, e1]`。`mul_one`, `mul_zero`, `zero_add` などが自動で効く。

/-! ---
## チャレンジ（応用1問）
- 平行四辺形法則（Parallelogram Law）を **自作内積 `dot`** の定義から
  直接展開して証明せよ。
- ポイント：成分ごとに展開→`ring` で整理。`sub_eq_add_neg` を使うと楽。

\[ ⟪u+v, u+v⟫ + ⟪u-v, u-v⟫ = 2 * ⟪u, u⟫ + 2 * ⟪v, v⟫ \]
--- -/

theorem Challenge
  (u v : R3) :
  ⟪u + v, u + v⟫ + ⟪u - v, u - v⟫
    = 2 * ⟪u, u⟫ + 2 * ⟪v, v⟫ := by
  sorry
  /- ヒント例：
     simp [dot, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
           mul_add, add_mul]   -- 成分展開
     ring                      -- 多項式整理
  -/

/-! ## 参考：動作確認コマンド（提出時は残してOK）
#check Q1a
#check Q1b
#check Q2
#check Q3
#check Q4
#check Q5
#check Challenge
-/

end ZenLA1.Session01
