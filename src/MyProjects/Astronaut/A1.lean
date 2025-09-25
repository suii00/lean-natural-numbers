/-
A* Optimality Skeleton (提出用)
Author: ChatGPT-5 Thinking
Course: ZEN 大学 解析学/アルゴリズム演習（題材1：A* 最適性）

この雛形は、A* の最適性を形式化するための最小コアです。
- 状態空間 α（有限/可算は今は抽象）
- 近傍関数 neighbors と非負エッジコスト w
- 「真の目標距離」 distToGoal を抽象的に与え、その満たすべき公理を Problem に含める
- ヒューリスティック h の admissible / consistent を定義
- A* の正しさに現れる代表的な補題を TODO 付きで声明

実装方針
1. distToGoal は真の最短費用を表す抽象的関数として導入。
   Problem 側に「境界条件」と「Bellman 風の最適性不等式」を公理化しておき、
   後で具体的なグラフ定義や最短路構成を与えれば置換可能。
2. A* のヒューリスティック h は
   - admissible: h ≤ distToGoal
   - consistent (a.k.a. monotone): h(x) ≤ w(x,y) + h(y) for all neighbor y
   を満たすことを形式化。
3. 定理雛形:
   - zero_heuristic_consistent : 0 は常に consistent
   - consistent_of_lipschitz_like : （任意の）h が consistent なら、A* の f=g+h が「下に凸な界」を持つ方向の補題（TODO）
   - admissible_of_consistent_and_goalZero : 目標で h=0 かつ consistent ⇒ admissible（今回補強済）
   - a_star_optimality_spec : admissible & consistent ⇒ A* は最適解を返す（仕様レベルの定理、TODO）

注意:
- ここでは A* の「アルゴリズムそのもの」はまだ書きません。まず仕様定理の骨組みと仮定関係を固めます。
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace SpaceAStar

/-- コストは非負実数を想定（証明では `0 ≤` を明示） -/
abbrev Cost := ℝ

/-- neighbors を沿う有限長パス -/
inductive Path {α : Type*} (neighbors : α → Finset α) : α → α → Type _ where
  | nil (x : α) : Path neighbors x x
  | cons {x y z : α} (hxy : y ∈ neighbors x) (rest : Path neighbors y z) :
      Path neighbors x z

namespace Path

variable {α : Type*} {neighbors : α → Finset α}

/-- パスの総コスト -/
noncomputable def cost (w : α → α → Cost) : ∀ {x y : α}, Path neighbors x y → Cost :=
  Path.rec (motive := fun {x y} _ => Cost)
    (fun _ => 0)
    (fun {x y _} _ _ cost_rest => w x y + cost_rest)

@[simp] lemma cost_nil (w : α → α → Cost) (x : α) :
    cost (neighbors:=neighbors) w (Path.nil (neighbors:=neighbors) x) = 0 := rfl

@[simp] lemma cost_cons (w : α → α → Cost)
    {x y z : α} (hxy : y ∈ neighbors x) (rest : Path neighbors y z) :
    cost (neighbors:=neighbors) w (Path.cons hxy rest) =
      w x y + cost (neighbors:=neighbors) w rest := rfl

end Path

/-- 問題クラス：目標述語・近傍・エッジコスト・真の目標距離（抽象） -/
structure Problem (α : Type*) where
  (start : α)
  (isGoal : α → Prop)
  (neighbors : α → Finset α)
  (w : α → α → Cost)
  -- 基本仮定：コストの非負性
  (w_nonneg : ∀ x y, 0 ≤ w x y)
  -- 抽象的な「真の目標距離」：各状態から最も安い目標到達費用
  (distToGoal : α → Cost)
  -- 目標での境界条件：goal なら 0
  (dist_goal_zero : ∀ {g}, isGoal g → distToGoal g = 0)
  -- Bellman 風の最適性不等式：任意の遷移で dist(x) ≤ w(x,y) + dist(y)
  (dist_bellman : ∀ x y, y ∈ neighbors x → distToGoal x ≤ w x y + distToGoal y)
  -- dist の非負性
  (dist_nonneg : ∀ x, 0 ≤ distToGoal x)
  -- 目標到達可能性（有限長パス）
  (goal_reachable : ∀ x, ∃ g, isGoal g ∧ Nonempty (Path neighbors x g))
  -- ε-最適パスの存在：distToGoal は最短路コストの Inf に一致
  (approx_goal :
    ∀ x ε, 0 < ε →
      ∃ g, isGoal g ∧ ∃ p : Path neighbors x g,
        Path.cost (neighbors:=neighbors) w p ≤ distToGoal x + ε)

namespace Problem

variable {α : Type*} (P : Problem α)

/-- エッジ関係（近傍に含まれるとき） -/
def Edge (x y : α) : Prop := y ∈ P.neighbors x

@[simp] lemma edge_iff {x y} : P.Edge x y ↔ y ∈ P.neighbors x := Iff.rfl

lemma w_nonneg' (x y : α) : 0 ≤ P.w x y := P.w_nonneg x y

lemma dist_bellman' {x y : α} (hxy : P.Edge x y) :
  P.distToGoal x ≤ P.w x y + P.distToGoal y :=
P.dist_bellman x y (by simpa [Edge] using hxy)

lemma dist_goal_zero' {g : α} (hg : P.isGoal g) :
  P.distToGoal g = 0 := P.dist_goal_zero hg

lemma dist_nonneg' (x : α) : 0 ≤ P.distToGoal x := P.dist_nonneg x

/-- パスの総コストを Problem に束縛した版 -/
noncomputable def pathCost : ∀ {x y : α}, Path P.neighbors x y → Cost :=
  Path.cost (neighbors:=P.neighbors) P.w

@[simp] lemma pathCost_nil (x : α) :
    Problem.pathCost (P := P) (Path.nil (neighbors:=P.neighbors) x) = 0 := rfl

@[simp] lemma pathCost_cons {x y z : α} (hxy : y ∈ P.neighbors x)
    (rest : Path P.neighbors y z) :
    Problem.pathCost (P := P) (Path.cons hxy rest) =
      P.w x y + Problem.pathCost (P := P) rest := rfl

end Problem

/-- A* におけるヒューリスティックの性質：admissible（真の距離の下界） -/
def admissible {α} (P : Problem α) (h : α → Cost) : Prop :=
  ∀ x, h x ≤ P.distToGoal x

/-- A* におけるヒューリスティックの性質：consistent（辺に沿って減りすぎない） -/
def consistent {α} (P : Problem α) (h : α → Cost) : Prop :=
  ∀ ⦃x y⦄, P.Edge x y → h x ≤ P.w x y + h y

section BasicLemmas

variable {α : Type*} (P : Problem α)

/-- 0-ヒューリスティックは常に consistent -/
theorem zero_heuristic_consistent : consistent P (fun _ => 0) := by
  intro x y hxy
  have := P.w_nonneg' x y
  -- 0 ≤ w ⇒ 0 ≤ w + 0
  simpa using this

/-- 0-ヒューリスティックは always admissible（dist は非負だから） -/
theorem zero_heuristic_admissible : admissible P (fun _ => 0) := by
  intro x; simpa using P.dist_nonneg' x

/-- consistent だと、「1ステップ進むたびに h は多くとも w だけしか減らない」型の不等式 -/
theorem consistent_step {h : α → Cost}
    (hc : consistent P h) {x y : α} (hxy : P.Edge x y) :
    h x - h y ≤ P.w x y := by
  have hx : h x ≤ P.w x y + h y := hc hxy
  have : h x - h y ≤ P.w x y + h y - h y := sub_le_sub_right hx _
  simpa using this

/-- consistent をパス全体へ伝播 -/
theorem consistent_path {h : α → Cost}
    (hc : consistent P h) :
    ∀ {x y : α} (p : Path P.neighbors x y),
      h x ≤ Problem.pathCost (P := P) p + h y :=
  Path.rec (motive := fun {x y} p =>
      h x ≤ Problem.pathCost (P := P) p + h y)
    (by intro x; simp [Problem.pathCost])
    (by
      intro x y z hxy rest ih
      calc
        h x ≤ P.w x y + h y :=
          hc (by simpa [Problem.Edge] using hxy)
        _ ≤ P.w x y + (Problem.pathCost (P := P) rest + h z) :=
          add_le_add_left ih _
        _ = Problem.pathCost (P := P) (Path.cons hxy rest) + h z := by
          simp [Problem.pathCost, add_comm, add_assoc])

end BasicLemmas

/-- 「目標では h = 0」を満たすヒューリスティック -/
def goalZero {α} (P : Problem α) (h : α → Cost) : Prop :=
  ∀ {g}, P.isGoal g → h g = 0

section MainStatements

variable {α : Type*} (P : Problem α)

/-- (定理雛形)
consistent かつ 目標点で h=0 なら、h は admissible（真の距離を過小評価しない）
参考直観：目標からのパスに沿って consistency をたどると、h(x) ≤ 累積 w + h(goal) = 累積 w。
Bellman の不等式から最良の累積 w は distToGoal(x) に一致/以下。
-/
theorem admissible_of_consistent_and_goalZero
    {h : α → Cost}
    (hc : consistent P h)
    (hz : goalZero P h) :
    admissible P h := by
  intro x
  classical
  by_contra hxle
  have hxgt : P.distToGoal x < h x := lt_of_not_ge hxle
  set ε := (h x - P.distToGoal x) / 2 with hεdef
  have hεpos : 0 < ε := by
    have : 0 < h x - P.distToGoal x := sub_pos.mpr hxgt
    simpa [hεdef] using half_pos this
  obtain ⟨g, hg, ⟨p, hp⟩⟩ := P.approx_goal x ε hεpos
  have hpath : h x ≤ Problem.pathCost (P := P) p + h g :=
    consistent_path (P := P) hc p
  have hgoal : h g = 0 := hz hg
  have hx_le_path : h x ≤ Problem.pathCost (P := P) p := by
    simpa [Problem.pathCost, hgoal] using hpath
  have hx_le : h x ≤ P.distToGoal x + ε :=
    le_trans hx_le_path (by simpa [Problem.pathCost] using hp)
  have diff_pos : 0 < h x - P.distToGoal x := sub_pos.mpr hxgt
  have hεlt : ε < h x - P.distToGoal x := by
    simpa [hεdef] using half_lt_self diff_pos
  have hx_lt : P.distToGoal x + ε < h x := by
    have := add_lt_add_left hεlt (P.distToGoal x)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  exact (lt_irrefl (h x)) (lt_of_le_of_lt hx_le hx_lt)

/-- (定理雛形・仕様レベル)
A* 最適性：ヒューリスティックが admissible（十分条件として consistent + goalZero でも可）なら、
A* は最初に目標を取り出した時点で最短経路コストを確定できる（f=g+h の単調性）。
この雛形では「A* 実装」を与えず、仕様的に述べる（後で実装と接続）。
-/
theorem a_star_optimality_spec
    {h : α → Cost}
    (_hadm : admissible P h) :
    True := by
  /- TODO:
     - オープン集合/クローズド集合/スコア f := g + h の単調性（tree/path 上での非減少性）
     - hadm から導かれる「ゴール取り出し時の g が真の最短」の主張
     - この雛形定理は仕様上のアンカー：後で A* 実装を定義し、命題を強化・接続する
  -/
  trivial

end MainStatements

/- ==========================================
   提出時のガイド
   1) small-step で進めるときは、まず
      admissible_of_consistent_and_goalZero を埋める
   2) つぎに a_star_optimality_spec を、
      「オープン集合・クローズド集合・f=g+h」の定義を追加して強化
   3) distToGoal を具体的なグラフ上の最短距離に差し替えるなら、
      Bellman 風不等式の証明を別 Lemma 群として実装
   ========================================== -/

/-- 定義が期待通り動くかの簡単な例 -/
def trivialProblem : Problem Unit :=
{ start := ()
, isGoal := fun _ => True
, neighbors := fun _ => (∅ : Finset Unit)
, w := fun _ _ => 0
, w_nonneg := by intro x y; simp
, distToGoal := fun _ => 0
, dist_goal_zero := by intro g hg; simp
, dist_bellman := by intro x y hy; simp
, dist_nonneg := by intro x; simp
, goal_reachable := by
    intro x
    cases x
    refine ⟨(), trivial, ?_⟩
    exact ⟨Path.nil (neighbors:=fun _ => (∅ : Finset Unit)) ()⟩
, approx_goal := by
    intro x ε hε
    cases x
    refine ⟨(), trivial, ⟨Path.nil (neighbors:=fun _ => (∅ : Finset Unit)) (), ?_⟩⟩
    have : 0 ≤ ε := le_of_lt hε
    simpa [Path.cost, zero_add] using this
}

example :
    admissible trivialProblem (fun _ : Unit => (0 : Cost)) := by
  have hc := zero_heuristic_consistent trivialProblem
  have hz : goalZero trivialProblem (fun _ : Unit => (0 : Cost)) := by
    intro g hg; rfl
  exact admissible_of_consistent_and_goalZero trivialProblem hc hz

end SpaceAStar







