import MyProjects.ST.Decidable.P1.DecidableEvents
import MyProjects.ST.Decidable.P2.DecidableAlgebra
import MyProjects.ST.Decidable.P3.DecidableFiltration

open Prob

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
  /-- 停止時間条件：各時刻 `t`（終端時刻以下）で `{ω | τ ω ≤ t}` が `ℱ` の時刻 `t` の代数に属する。 -/
  isStopping :
    ∀ (t : ℕ) (ht : t ≤ ℱ.timeHorizon),
      {ω : Ω.carrier | time ω ≤ t} ∈ (ℱ.observableAt t ht).events
  /-- 上界性：`τ(ω)` は常に `timeHorizon` 以下。 -/
  time_le_horizon : ∀ ω, time ω ≤ ℱ.timeHorizon

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

/-- 事象 `{τ ≤ t}` を表す補助定義。 -/
def eventLe (τ : ComputableStoppingTime ℱ) (t : ℕ) : Prob.Event Ω.carrier :=
  {ω | τ.time ω ≤ t}

lemma eventLe_mem_observable
    (τ : ComputableStoppingTime ℱ) (t : ℕ) (ht : t ≤ ℱ.timeHorizon) :
    eventLe τ t ∈ (ℱ.observableAt t ht).events := by
  simpa [eventLe] using τ.isStopping t ht

/-- 事象 `{τ = n}`。 -/
def eventEq (τ : ComputableStoppingTime ℱ) (n : ℕ) : Prob.Event Ω.carrier :=
  {ω | τ.time ω = n}

lemma eventEq_mem_observable
    (τ : ComputableStoppingTime ℱ) (n : ℕ) (hn : n ≤ ℱ.timeHorizon) :
    eventEq τ n ∈ (ℱ.observableAt n hn).events := by
  classical
  cases n with
  | zero =>
      -- {τ = 0} は {τ ≤ 0} と同じ
      simpa [eventEq, eventLe] using eventLe_mem_observable (τ := τ) 0 hn
  | succ n' =>
      -- {τ = n'+1} = {τ ≤ n'+1} ∩ ({τ ≤ n'} )ᶜ
      have hset :
          eventEq (τ := τ) (n' + 1) =
            eventLe (τ := τ) (n' + 1) ∩ Prob.Event.complement (eventLe (τ := τ) n') := by
        ext ω; constructor
        · intro h; dsimp [eventEq] at h
          constructor
          · -- τ.time ω = n'+1 ⇒ τ.time ω ≤ n'+1
            have : τ.time ω = n' + 1 := h
            simp [eventLe, this]
          · -- かつ τ.time ω ≤ n' ではない
            have : τ.time ω = n' + 1 := h
            have hnot : ¬ τ.time ω ≤ n' := by
              -- n' < n'+1 = τ.time ω
              have : n' < τ.time ω := by simpa [this] using Nat.lt_succ_self n'
              exact Nat.not_le_of_gt this
            -- 補集合への所属は `¬ τ.time ω ≤ n'` と同値
            have : ω ∈ Prob.Event.complement (eventLe (τ := τ) n') := by
              simp [Prob.Event.complement, eventLe, hnot]
            exact this
        · intro h; rcases h with ⟨hle, hnot⟩
          -- hle : τ.time ω ≤ n'+1, hnot : ¬ τ.time ω ≤ n'
          have hgt : n' < τ.time ω := Nat.lt_of_not_ge hnot
          have hge : n' + 1 ≤ τ.time ω := Nat.succ_le_of_lt hgt
          have heq : τ.time ω = n' + 1 := le_antisymm hle hge
          exact heq
      -- 可観測性
      have h_le_n   : eventLe (τ := τ) (n' + 1) ∈ (ℱ.observableAt (n' + 1) hn).events :=
        eventLe_mem_observable (τ := τ) (n' + 1) hn
      have h_le_pred :
          eventLe (τ := τ) n' ∈ (ℱ.observableAt (n' + 1) hn).events := by
        -- monotonicity from n' to n'+1
        have hs : n' ≤ ℱ.timeHorizon := Nat.le_trans (Nat.le_succ _) hn
        have hmono := ℱ.monotone (s := n') (t := n' + 1)
            (hs := hs) (ht := hn) (Nat.le_succ _)
        have hpred := eventLe_mem_observable (τ := τ) n' hs
        exact hmono hpred
      have hcomp :
          Prob.Event.complement (eventLe (τ := τ) n')
            ∈ (ℱ.observableAt (n' + 1) hn).events :=
        (ℱ.observableAt (n' + 1) hn).closed_complement h_le_pred
      have hinter :=
        Prob.FiniteAlgebra.closed_intersection
          (ℱ := ℱ.observableAt (n' + 1) hn) h_le_n hcomp
      simpa [hset, Prob.Event.intersection, Prob.Event.complement] using hinter

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
  isStopping := by
    intro t ht
    by_cases hct : c ≤ t
    · have hset : {ω : Ω.carrier | c ≤ t} = (Set.univ : Set Ω.carrier) := by
        ext ω; simp [hct]
      have h := Prob.FiniteAlgebra.has_univ (ℱ.observableAt t ht)
      simpa [hset] using h
    · have hset : {ω : Ω.carrier | c ≤ t} = (∅ : Set Ω.carrier) := by
        ext ω; simp [hct]
      have h := (ℱ.observableAt t ht).has_empty
      have h' : (∅ : Set Ω.carrier) ∈ (ℱ.observableAt t ht).events := by
        simpa [Prob.Event.empty] using h
      simpa [hset] using h'
  time_le_horizon := by
    intro ω; simpa using hc

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
-/

/-- 2 つの停止時間の `min`。 -/
def min (τ₁ τ₂ : ComputableStoppingTime ℱ) :
    ComputableStoppingTime ℱ where
  time := fun ω => Nat.min (τ₁.time ω) (τ₂.time ω)
  isStopping := by
    intro t ht
    have h1 :
        {ω : Ω.carrier | τ₁.time ω ≤ t} ∈ (ℱ.observableAt t ht).events :=
      τ₁.isStopping t ht
    have h2 :
        {ω : Ω.carrier | τ₂.time ω ≤ t} ∈ (ℱ.observableAt t ht).events :=
      τ₂.isStopping t ht
    -- 和でも閉じているので利用する
    have hUnion := (ℱ.observableAt t ht).closed_union h1 h2
    classical
    have hset :
        {ω : Ω.carrier | Nat.min (τ₁.time ω) (τ₂.time ω) ≤ t} =
          ({ω : Ω.carrier | τ₁.time ω ≤ t} ∪ {ω : Ω.carrier | τ₂.time ω ≤ t}) := by
      ext ω; constructor
      · intro hmin
        have hmin' : Nat.min (τ₁.time ω) (τ₂.time ω) ≤ t := hmin
        have hle : τ₁.time ω ≤ τ₂.time ω ∨ τ₂.time ω ≤ τ₁.time ω := le_total _ _
        cases hle with
        | inl hle' =>
            have hminEq : Nat.min (τ₁.time ω) (τ₂.time ω) = τ₁.time ω :=
              Nat.min_eq_left hle'
            have hineq : τ₁.time ω ≤ t := by simpa [hminEq] using hmin'
            exact Or.inl hineq
        | inr hle' =>
            have hminEq : Nat.min (τ₁.time ω) (τ₂.time ω) = τ₂.time ω :=
              Nat.min_eq_right hle'
            have hineq : τ₂.time ω ≤ t := by simpa [hminEq] using hmin'
            exact Or.inr hineq
      · intro hdisj
        rcases hdisj with h₁ | h₂
        · exact le_trans (Nat.min_le_left _ _) h₁
        · exact le_trans (Nat.min_le_right _ _) h₂
    simpa [hset, Prob.Event.union] using hUnion
  time_le_horizon := by
    intro ω
    -- min ≤ τ₁.time ω ≤ timeHorizon
    exact le_trans (Nat.min_le_left _ _) (τ₁.time_le_horizon ω)

/-- 2 つの停止時間の `max`。 -/
def max (τ₁ τ₂ : ComputableStoppingTime ℱ) :
    ComputableStoppingTime ℱ where
  time := fun ω => Nat.max (τ₁.time ω) (τ₂.time ω)
  isStopping := by
    intro t ht
    have h1 :
        {ω : Ω.carrier | τ₁.time ω ≤ t} ∈ (ℱ.observableAt t ht).events :=
      τ₁.isStopping t ht
    have h2 :
        {ω : Ω.carrier | τ₂.time ω ≤ t} ∈ (ℱ.observableAt t ht).events :=
      τ₂.isStopping t ht
    have hInter :=
      Prob.FiniteAlgebra.closed_intersection
        (ℱ := ℱ.observableAt t ht) h1 h2
    classical
    have hset :
        {ω : Ω.carrier | Nat.max (τ₁.time ω) (τ₂.time ω) ≤ t} =
          {ω : Ω.carrier | τ₁.time ω ≤ t ∧ τ₂.time ω ≤ t} := by
      ext ω; constructor
      · intro h
        exact ⟨le_trans (Nat.le_max_left _ _) h,
              le_trans (Nat.le_max_right _ _) h⟩
      · intro h; rcases h with ⟨h1ω, h2ω⟩
        exact (max_le_iff).2 ⟨h1ω, h2ω⟩
    have hset' :
        {ω : Ω.carrier | τ₁.time ω ≤ t ∧ τ₂.time ω ≤ t} =
          ({ω : Ω.carrier | τ₁.time ω ≤ t} ∩ {ω : Ω.carrier | τ₂.time ω ≤ t}) := by
      rfl
    simpa [hset, hset', Prob.Event.intersection] using hInter
  time_le_horizon := by
    intro ω
    have h1 := τ₁.time_le_horizon ω
    have h2 := τ₂.time_le_horizon ω
    exact max_le_iff.mpr ⟨h1, h2⟩

@[simp] lemma min_le_left (τ₁ τ₂ : ComputableStoppingTime ℱ) :
    min τ₁ τ₂ ≤ τ₁ := by
  intro ω
  simp [min]

@[simp] lemma min_le_right (τ₁ τ₂ : ComputableStoppingTime ℱ) :
    min τ₁ τ₂ ≤ τ₂ := by
  intro ω
  simp [min]

@[simp] lemma le_max_left (τ₁ τ₂ : ComputableStoppingTime ℱ) :
    τ₁ ≤ max τ₁ τ₂ := by
  intro ω
  simp [max]

@[simp] lemma le_max_right (τ₁ τ₂ : ComputableStoppingTime ℱ) :
    τ₂ ≤ max τ₁ τ₂ := by
  intro ω
  simp [max]

/-- 上界付きの停止時間から、より小さい停止時間も同じ上界で抑えられる。 -/
lemma isBounded_of_le
    {τ₁ τ₂ : ComputableStoppingTime ℱ} {N : ℕ}
    (h : τ₁ ≤ τ₂) (hB : isBounded τ₂ N) :
    isBounded τ₁ N := by
  intro ω
  exact le_trans (h ω) (hB ω)

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
-/

section Examples

open ComputableStoppingTime

-- 以下は理論本体には依存しない教育用サンプル集。
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
  time := fun b => match b with | true => 0 | false => 1
  isStopping := by
    intro t ht
    -- powerSet 上では任意の部分集合が可観測
    simp [coinFullFiltration, coinFullAlgebra, constFiltration,
      Prob.FiniteAlgebra.powerSet]
  time_le_horizon := by
    intro b; cases b <;> decide

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
