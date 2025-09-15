/-
ZEN大学「線形代数1」(MTH-1-C1-1030-004, 2025, オンデマンド)
第2回：空間ベクトル（基礎問題5＋チャレンジ1）— 提出形式：Lean 4 ファイル

提出物：このファイルの `sorry` をすべて消して証明／計算を完成させてください。
想定環境：Lean 4 + mathlib（最新版）。`lake exe cache get` 等で mathlib を取得してください。

学習目標（第2回）
- 空間ベクトルの外積（ベクトル積）の定義と基本性質を理解する。
- スカラー三重積の幾何学的意味（平行六面体の体積）を形式化する。
- ベクトルの線形独立性と平行・直交の判定を行う。
- 平面の法線ベクトルと点までの距離を計算する。
- チャレンジ：Jacobi恒等式（ベクトル三重積の循環性）の形式的証明。
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace ZenLA1.Session02

/-! ## 下準備：R^3・内積・外積 -/

/-- 実3次元ベクトルを単純に積型で表す（成分は (x, y, z) ）。 -/
abbrev R3 := ℝ × ℝ × ℝ

/-- 成分表示の内積（第1回から継承）。 -/
def dot (u v : R3) : ℝ :=
  u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

notation:70 "⟪" u "," v "⟫" => dot u v

/-- 外積（ベクトル積）の定義。 -/
def cross (u v : R3) : R3 :=
  (u.2.1 * v.2.2 - u.2.2 * v.2.1,
   u.2.2 * v.1 - u.1 * v.2.2,
   u.1 * v.2.1 - u.2.1 * v.1)

-- 注: Lean の型レベル直積 `α × β` と衝突しやすいため、
-- 以降は関数形 `cross u v` を主に用いる（演算子は定義しない）。

/-- スカラー三重積 u · (v × w) の定義。 -/
def scalar_triple (u v w : R3) : ℝ :=
  dot u (cross v w)

-- 注: `[...]` は `List` リテラルと衝突するため、
-- 三重積も `scalar_triple u v w` を用いる。

/-- 二乗ノルム（第1回から継承）。 -/
def normSq (u : R3) : ℝ := dot u u

/-! ### 補助：簡単な `simp` 用の補題 -/

@[simp] lemma dot_def (u v : R3) :
  ⟪u, v⟫ = u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2 := rfl

@[simp] lemma cross_def (u v : R3) :
  cross u v = (u.2.1 * v.2.2 - u.2.2 * v.2.1,
               u.2.2 * v.1 - u.1 * v.2.2,
               u.1 * v.2.1 - u.2.1 * v.1) := rfl

@[simp] lemma scalar_triple_def (u v w : R3) :
  scalar_triple u v w = ⟪u, cross v w⟫ := rfl

@[simp] lemma normSq_def (u : R3) : normSq u = ⟪u, u⟫ := rfl

/-! ## データ：この回で用いる具体ベクトル -/
def a : R3 := (1, 2, 3)
def b : R3 := (2, -1, 1)
def c : R3 := (0, 1, 2)
def P : R3 := (1, 1, 1)  -- 平面上の点
def n : R3 := (2, -1, 3) -- 平面の法線ベクトル

/-! ## 提出ルール
- 各問題は `theorem` / `lemma` / `example` のいずれかを完成させてください。
- 「計算問題」は両辺が等しいことを `simp`, `ring`, `norm_num` などで示せます。
- 「性質の問題」は `simp [dot, cross]`, `ext`, `ring` 等の方針をコメントで示すと加点。
- 途中の補題を自由に作って構いません。 -/

/-! ---
## 基礎問題（5問）
--- -/

/-- **Q1** ベクトル `a=(1,2,3)` と `b=(2,-1,1)` の外積 `a × b` を計算せよ。 -/
theorem Q1 : cross a b = (5, 5, -5) := by
  -- 成分に分解して数値計算
  ext <;> norm_num [cross, a, b]
  -- ヒント：`simp [cross, a, b]` の後に `norm_num` または直接展開。

/-- **Q2** 外積の反交換性：`u × v = -(v × u)` を示せ。 -/
theorem Q2 (u v : R3) : cross u v = - (cross v u) := by
  -- 成分ごとに反対称性を示す
  ext <;> simp [cross] <;> ring
  -- ヒント：`ext` で成分ごとに示し、`simp [cross]` → `ring`。

/-- **Q3** `u` と `u × v` が直交することを示せ：`⟪u, u × v⟫ = 0`。 -/
theorem Q3 (u v : R3) : ⟪u, cross u v⟫ = 0 := by
  -- 定義を展開して多項式恒等式に帰着
  simp [dot, cross]
  ring
  -- ヒント：成分を展開（`rcases` または直接 `simp [dot, cross]`）→ `ring`。

/-- **Q4** スカラー三重積 `[a, b, c]` を計算せよ（`a=(1,2,3)`, `b=(2,-1,1)`, `c=(0,1,2)`）。 -/
theorem Q4 : scalar_triple a b c = -5 := by
  -- `[a,b,c] = ⟪a, b × c⟫` を展開して数値計算
  norm_num [scalar_triple, dot, cross, a, b, c]
  -- ヒント：`simp [scalar_triple, dot, cross, a, b, c]` → `norm_num`。

/-- **Q5** 点 `Q=(3,2,1)` から平面 `2x - y + 3z = 6`（法線 `n=(2,-1,3)`, 点 `P=(1,1,1)` を通る）
までの距離の二乗に `‖n‖^2 = 14` を掛けた値を求めよ。
距離公式：`d = |⟪Q - P, n⟫| / ‖n‖` より、`d^2 * ‖n‖^2 = ⟪Q - P, n⟫^2`。 -/
theorem Q5 : let Q : R3 := (3, 2, 1)
            (⟪Q - P, n⟫)^2 = 9 := by
  -- `Q=(3,2,1), P=(1,1,1), n=(2,-1,3)` を代入して内積を計算
  intro Q
  -- 内積を評価し二乗
  have hDot : ⟪Q - P, n⟫ = 3 := by
    -- 成分に展開して即値化（数値は `norm_num` で処理）
    norm_num [dot, Q, P, n]
  -- `simp` が `dot` を展開しないように `only` を付けて書き換える
  simpa only [hDot] using (by norm_num : (3:ℝ)^2 = 9)
  -- ヒント：`simp [dot, P, n]` で内積を計算し、`norm_num` で二乗を評価。

/-! ---
## チャレンジ（応用1問）
- Jacobi恒等式：ベクトル三重積について以下の循環的な恒等式を証明せよ。
- これは外積がLie代数の構造を持つことを示す重要な性質。

\[ u × (v × w) + v × (w × u) + w × (u × v) = 0 \]
--- -/

theorem Challenge (u v w : R3) :
  cross u (cross v w) + cross v (cross w u) + cross w (cross u v) = 0 := by
  -- 成分に分解し、定義展開して多項式同値に帰着
  rcases u with ⟨ux, uy, uz⟩
  rcases v with ⟨vx, vy, vz⟩
  rcases w with ⟨wx, wy, wz⟩
  -- 単純展開のみ（結合法則・交換法則は使わず）→ `ring` で整理
  ext <;> simp [cross] <;> ring
  /- ヒント：
     - 成分で展開：`rcases u with ⟨ux, uy, uz⟩` などで3つとも分解
     - `simp [cross]` で外積を全て展開
     - `ext` で各成分が0になることを示す
     - 各成分で `ring` を使って整理
  -/

/-! ## 参考：動作確認コマンド（提出時は残してOK）
#check Q1
#check Q2
#check Q3
#check Q4
#check Q5
#check Challenge
-/

end ZenLA1.Session02
