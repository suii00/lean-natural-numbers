import MyProjects.ST.Decidable.P1.DecidableEvents
import MyProjects.ST.Decidable.P2.DecidableAlgebra
import MyProjects.ST.Decidable.P3.DecidableFiltration

open Classical Prob

/-!
# Computable Stopping Times on Discrete Filtrations

このファイルは、離散版フィルトレーション `DecidableFiltration` の上での
**計算可能な停止時間 (computable stopping time)** を定義する。

## 位置づけ

本ファイルは、以下の階層構造の第 4 層に対応する：

DecidableEvents.lean ← 有限標本空間と decidable events
↓
DecidableAlgebra.lean ← 有限代数（Boolean 演算で閉じた事象族）
↓
DecidableFiltration.lean ← 離散版フィルトレーション（構造塔のインスタンス）
↓
ComputableStoppingTime.lean ← 停止時間（情報＋時刻の構造）
↓
AlgorithmicMartingale.lean ← マルチンゲールと Optional Stopping Theorem


ここではまだ「確率測度」や「期待値」は導入せず，
**情報（filtration）＋時刻（ℕ）** という構造にのみ集中する。

- 有限標本空間 `Ω : Prob.FiniteSampleSpace`
- 離散フィルトレーション `ℱ : DecidableFiltration Ω`
- 停止時間 `τ : Ω.carrier → ℕ`
- 条件：各時刻 `t` について `{ω | τ ω ≤ t}` が `ℱ` の `observableAt t` に属する

有限標本空間と有限代数の上で作業するため，
- 事象の membership 判定は `DecidableEvents` / `DecidableAlgebra` により decidable
- フィルトレーションは `DecidableFiltration` で離散的な構造塔として実装済み

この層の目的は，
後続の `AlgorithmicMartingale.lean` での「有限和としての期待値」や
「有限停止時間版 OST」の土台となる「停止時間の構造」を与えることである。
-/

/--
`ℱ : DecidableFiltration Ω` に関する **計算可能な停止時間**。

数学的には，有限標本空間 `Ω` と離散フィルトレーション `ℱ` に対して，
写像 `time : Ω → ℕ` が次を満たすとき停止時間と呼ぶ：

* 各時刻 `t` について，事象 `{ω | time ω ≤ t}` が `ℱ` の時刻 `t` の代数に属する

ここでは標本空間 `Ω` を `Prob.FiniteSampleSpace` とし，
標本点の型を `Ω.carrier` とする。
-/
structure ComputableStoppingTime {Ω : Prob.FiniteSampleSpace}
    (ℱ : DecidableFiltration Ω) where
  /-- 停止時間としてのランダム時刻 `τ(ω)`。 -/
  time : Ω.carrier → ℕ
  /-- 停止時間条件：各時刻 `t` で `{ω | τ ω ≤ t}` が `ℱ` の時刻 `t` の代数に属する。 -/
  adapted :
    ∀ (t : ℕ) (ht : t ≤ ℱ.timeHorizon),
      {ω : Ω.carrier | time ω ≤ t} ∈ (ℱ.observableAt t ht).events

namespace ComputableStoppingTime

variable {Ω : Prob.FiniteSampleSpace} {ℱ : DecidableFiltration Ω}

/-!
## 1. 点ごとの順序と基本的な構造

停止時間同士は「各標本点での値の大小」によって順序付けできる。
-/

/-- 停止時間の点ごとの順序。 -/
instance : LE (ComputableStoppingTime ℱ) where
  le τ₁ τ₂ := ∀ ω, τ₁.time ω ≤ τ₂.time ω

lemma le_def {τ₁ τ₂ : ComputableStoppingTime ℱ} :
    τ₁ ≤ τ₂ ↔ ∀ ω, τ₁.time ω ≤ τ₂.time ω := Iff.rfl

/-!
## 2. 定数停止時間

`τ(ω) ≡ c` という定数停止時間は，`c ≤ timeHorizon` のとき停止時間条件を満たす：

- `t < c` なら `{τ ≤ t}` は空集合
- `t ≥ c` なら `{τ ≤ t}` は全体集合

どちらも有限代数上の事象である。
-/

/-- 定数停止時間 `c`（`c` が終端時刻以下）。 -/
def const (ℱ : DecidableFiltration Ω) (c : ℕ) (hc : c ≤ ℱ.timeHorizon) :
    ComputableStoppingTime ℱ where
  time := fun _ => c
  adapted := by
    intro t ht
    -- {ω | τ(ω) ≤ t} = {ω | c ≤ t} は ω に依らないので，
    -- t ≥ c なら全体集合，t < c なら空集合になる。
    by_cases hct : c ≤ t
    · -- t ≥ c の場合：{τ ≤ t} = Ω
      have hset : {ω : Ω.carrier | c ≤ t} = (Set.univ : Set Ω.carrier) := by
        ext ω; simp [hct]
      have h := Prob.FiniteAlgebra.has_univ (ℱ.observableAt t ht)
      simpa [hset] using h
    · -- t < c の場合：{τ ≤ t} = ∅
      have hset : {ω : Ω.carrier | c ≤ t} = (∅ : Set Ω.carrier) := by
        ext ω; simp [hct]
      have h := (ℱ.observableAt t ht).has_empty
      have h' : (∅ : Set Ω.carrier) ∈ (ℱ.observableAt t ht).events := by
        simpa [Prob.Event.empty] using h
      simpa [hset] using h'

/-- 停止時間が上から `N` で抑えられること。 -/
def isBounded (τ : ComputableStoppingTime ℱ) (N : ℕ) : Prop :=
  ∀ ω, τ.time ω ≤ N

/-- 定数停止時間はその値で自明に有界。 -/
lemma const_isBounded (ℱ : DecidableFiltration Ω) (c : ℕ)
    (hc : c ≤ ℱ.timeHorizon) :
    isBounded (const ℱ c hc) c := by
  intro ω
  simp [const]

/-!
## 3. min・max による停止時間演算

2 つの停止時間 `τ₁, τ₂` に対し，

* `min τ₁ τ₂` : それぞれの標本点での最小値
* `max τ₁ τ₂` : それぞれの標本点での最大値

も停止時間になる。

- `{min(τ₁, τ₂) ≤ t} = {τ₁ ≤ t} ∪ {τ₂ ≤ t}`（有限和で閉じているので可観測）
- `{max(τ₁, τ₂) ≤ t} = {τ₁ ≤ t} ∩ {τ₂ ≤ t}`（有限積で閉じているので可観測）
-/

/-- 2 つの停止時間の `min`。 -/
def min (τ₁ τ₂ : ComputableStoppingTime ℱ) :
    ComputableStoppingTime ℱ where
  time := fun ω => Nat.min (τ₁.time ω) (τ₂.time ω)
  adapted := by
    intro t ht
    have h1 :
        {ω : Ω.carrier | τ₁.time ω ≤ t} ∈ (ℱ.observableAt t ht).events :=
      τ₁.adapted t ht
    have h2 :
        {ω : Ω.carrier | τ₂.time ω ≤ t} ∈ (ℱ.observableAt t ht).events :=
      τ₂.adapted t ht
    -- 右辺 {τ₁ ≤ t} ∪ {τ₂ ≤ t} が代数で閉じていることを使う
    have hUnion := (ℱ.observableAt t ht).closed_union h1 h2
    classical
    -- 集合レベルの等式：
    -- {min(τ₁, τ₂) ≤ t} = {τ₁ ≤ t} ∪ {τ₂ ≤ t}
    have hset :
        {ω : Ω.carrier | Nat.min (τ₁.time ω) (τ₂.time ω) ≤ t} =
          ({ω | τ₁.time ω ≤ t} ∪ {ω | τ₂.time ω ≤ t}) := by
      ext ω; constructor
      · intro hmin_le_t
        -- min ≤ t ならどちらか一方が t 以下
        have hle : τ₁.time ω ≤ τ₂.time ω ∨ τ₂.time ω ≤ τ₁.time ω :=
          le_total _ _
        cases hle with
        | inl hle =>
            have hmin : Nat.min (τ₁.time ω) (τ₂.time ω) = τ₁.time ω :=
              Nat.min_eq_left hle
            have hineq : τ₁.time ω ≤ t := by
              have h' : Nat.min (τ₁.time ω) (τ₂.time ω) ≤ t := hmin_le_t
              -- min の具体的な場合分けを書き換えで吸収する
              simpa [hmin] using h'
            exact Or.inl hineq
        | inr hle =>
            have hmin : Nat.min (τ₁.time ω) (τ₂.time ω) = τ₂.time ω :=
              Nat.min_eq_right hle
            have hineq : τ₂.time ω ≤ t := by
              have h' : Nat.min (τ₁.time ω) (τ₂.time ω) ≤ t := hmin_le_t
              simpa [hmin] using h'
            exact Or.inr hineq
      · intro hdisj
        rcases hdisj with h₁ | h₂
        · exact le_trans (Nat.min_le_left _ _) h₁
        · exact le_trans (Nat.min_le_right _ _) h₂
    simpa [hset, Prob.Event.union] using hUnion

/-- 2 つの停止時間の `max`。 -/
def max (τ₁ τ₂ : ComputableStoppingTime ℱ) :
    ComputableStoppingTime ℱ where
  time := fun ω => Nat.max (τ₁.time ω) (τ₂.time ω)
  adapted := by
    intro t ht
    have h1 :
        {ω : Ω.carrier | τ₁.time ω ≤ t} ∈ (ℱ.observableAt t ht).events :=
      τ₁.adapted t ht
    have h2 :
        {ω : Ω.carrier | τ₂.time ω ≤ t} ∈ (ℱ.observableAt t ht).events :=
      τ₂.adapted t ht
    -- 右辺 {τ₁ ≤ t} ∩ {τ₂ ≤ t} が代数で閉じていることを使う
    have hInter :=
      Prob.FiniteAlgebra.closed_intersection
        (ℱ := ℱ.observableAt t ht) h1 h2
    classical
    -- {max(τ₁, τ₂) ≤ t} = {τ₁ ≤ t ∧ τ₂ ≤ t}
    have hset :
        {ω : Ω.carrier | Nat.max (τ₁.time ω) (τ₂.time ω) ≤ t} =
          {ω : Ω.carrier | τ₁.time ω ≤ t ∧ τ₂.time ω ≤ t} := by
      ext ω; constructor
      · intro h
        exact
          ⟨le_trans (Nat.le_max_left _ _) h,
           le_trans (Nat.le_max_right _ _) h⟩
      · intro h; rcases h with ⟨h1ω, h2ω⟩
        exact (max_le_iff).2 ⟨h1ω, h2ω⟩
    -- {τ₁ ≤ t ∧ τ₂ ≤ t} = {τ₁ ≤ t} ∩ {τ₂ ≤ t}
    have hset' :
        {ω : Ω.carrier | τ₁.time ω ≤ t ∧ τ₂.time ω ≤ t} =
          ({ω | τ₁.time ω ≤ t} ∩ {ω | τ₂.time ω ≤ t}) := by
      ext ω; simp
    simpa [hset, hset', Prob.Event.intersection] using hInter

/-- `min` はそれぞれの停止時間以下。 -/
lemma min_le_left (τ₁ τ₂ : ComputableStoppingTime ℱ) :
    min τ₁ τ₂ ≤ τ₁ := by
  intro ω
  simp [min, Nat.min_le_left]

/-- `min` はそれぞれの停止時間以下。 -/
lemma min_le_right (τ₁ τ₂ : ComputableStoppingTime ℱ) :
    min τ₁ τ₂ ≤ τ₂ := by
  intro ω
  simp [min, Nat.min_le_right]

/-- 各点で `τ₁ ≤ max τ₁ τ₂`。 -/
lemma le_max_left (τ₁ τ₂ : ComputableStoppingTime ℱ) :
    τ₁ ≤ max τ₁ τ₂ := by
  intro ω
  simp [max, Nat.le_max_left]

/-- 各点で `τ₂ ≤ max τ₁ τ₂`。 -/
lemma le_max_right (τ₁ τ₂ : ComputableStoppingTime ℱ) :
    τ₂ ≤ max τ₁ τ₂ := by
  intro ω
  simp [max, Nat.le_max_right]

/-- 有界な停止時間同士の `min` も有界。 -/
lemma min_isBounded
    (τ₁ τ₂ : ComputableStoppingTime ℱ) (N₁ N₂ : ℕ)
    (h1 : isBounded τ₁ N₁) (h2 : isBounded τ₂ N₂) :
    isBounded (min τ₁ τ₂) (Nat.min N₁ N₂) := by
  intro ω
  have h1ω := h1 ω
  have h2ω := h2 ω
  have h_le1 : Nat.min (τ₁.time ω) (τ₂.time ω) ≤ N₁ :=
    le_trans (Nat.min_le_left _ _) h1ω
  have h_le2 : Nat.min (τ₁.time ω) (τ₂.time ω) ≤ N₂ :=
    le_trans (Nat.min_le_right _ _) h2ω
  exact le_min h_le1 h_le2

/-- 有界な停止時間同士の `max` も有界。 -/
lemma max_isBounded
    (τ₁ τ₂ : ComputableStoppingTime ℱ) (N₁ N₂ : ℕ)
    (h1 : isBounded τ₁ N₁) (h2 : isBounded τ₂ N₂) :
    isBounded (max τ₁ τ₂) (Nat.max N₁ N₂) := by
  intro ω
  have h1ω := h1 ω
  have h2ω := h2 ω
  have h1bound : τ₁.time ω ≤ Nat.max N₁ N₂ :=
    le_trans h1ω (Nat.le_max_left _ _)
  have h2bound : τ₂.time ω ≤ Nat.max N₁ N₂ :=
    le_trans h2ω (Nat.le_max_right _ _)
  exact (max_le_iff).mpr ⟨h1bound, h2bound⟩

end ComputableStoppingTime

/-!
## 4. 簡単な計算例（#eval）

ここでは，1 回のコイン投げ（`Bool`）を標本空間とした最も単純な例を示す。

- 標本空間：`Ω = {true, false}`（`true = 表`, `false = 裏`）
- 代数：全ての部分集合（`powerSet`）
- フィルトレーション：全時刻で同じ代数を返す定数フィルトレーション
- 停止時間の例：
  * `τ_const(ω) ≡ 1`
  * `τ_ht(ω) = 0` if `ω = true`, `1` if `ω = false`
- `min`, `max` による新しい停止時間の構成と `#eval` による値の確認
-/

section Examples

open ComputableStoppingTime

/-- 1 回のコイン投げ（Bool）を標本空間とする有限標本空間。 -/
def coinSpace : Prob.FiniteSampleSpace where
  carrier := Bool
  fintype := inferInstance
  decidableEq := inferInstance

/-- コイン標本空間上の「全ての部分集合」からなる有限代数。 -/
def coinFullAlgebra : Prob.FiniteAlgebra coinSpace.carrier :=
  Prob.FiniteAlgebra.powerSet

/--
全時刻で同じ代数を返す定数フィルトレーション。

ここでは time horizon = 3 とし，
すべての時刻で完全な情報（全ての事象）が可観測である状況を表す。
-/
def coinFullFiltration : DecidableFiltration coinSpace :=
  constFiltration coinSpace coinFullAlgebra 3

/-- 定数停止時間 τ(ω) ≡ 1。 -/
def coinConst1 : ComputableStoppingTime coinFullFiltration :=
  const coinFullFiltration 1 (by decide)

/--
非自明な停止時間の例：

- 表 (`true`) のとき時刻 0 で即座に停止
- 裏 (`false`) のとき時刻 1 で停止

フィルトレーションが常に `powerSet` なので，
どの事象も可観測であることを使って停止時間条件を証明する。
-/
def coinHeadTail : ComputableStoppingTime coinFullFiltration where
  time := fun b => if b then 0 else 1
  adapted := by
    intro t ht
    -- {ω | τ(ω) ≤ t} は Bool 上の任意の部分集合なので，
    -- powerSet の events（= 全集合）に自動的に属する。
    have :
        {ω : coinSpace.carrier | (if ω then 0 else 1) ≤ t} ∈
          (Prob.FiniteAlgebra.powerSet :
            Prob.FiniteAlgebra coinSpace.carrier).events := by
      simp [Prob.FiniteAlgebra.powerSet]
    simpa [coinFullFiltration, coinFullAlgebra, constFiltration] using this

/-- `min` と `max` を使った合成停止時間。 -/
def coinMin : ComputableStoppingTime coinFullFiltration :=
  min coinConst1 coinHeadTail

def coinMax : ComputableStoppingTime coinFullFiltration :=
  max coinConst1 coinHeadTail

/-
実際に停止時間を具体的な標本点で評価してみる。
Lean の `#eval` は有限標本空間上の停止時間を「関数」として計算してくれる。
-/

-- 定数停止時間：常に 1
#eval coinConst1.time true   -- 1
#eval coinConst1.time false  -- 1

-- 非自明な停止時間：表なら 0，裏なら 1
#eval coinHeadTail.time true   -- 0
#eval coinHeadTail.time false  -- 1

-- min：表では min(1,0) = 0，裏では min(1,1) = 1
#eval coinMin.time true    -- 0
#eval coinMin.time false   -- 1

-- max：表では max(1,0) = 1，裏では max(1,1) = 1
#eval coinMax.time true    -- 1
#eval coinMax.time false   -- 1

end Examples

