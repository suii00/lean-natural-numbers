import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Probability.Process.Adapted
import MyProjects.ST.CAT2_revised

/-
# Structure Tower の応用例5: 測度論・確率論

## 1. 濾過 (Filtration) - 最も重要な応用！

確率論における濾過は Structure Tower の典型例
-/

-- 確率空間上の濾過
-- (Ω, ℱ, P) 上の σ-代数の増大列
structure Filtration (Ω : Type*) where
  /-- 時刻 t における情報 -/
  σalgebra : ℝ → MeasurableSpace Ω
  /-- 単調性: 時間が進むと情報が増える -/
  monotone : ∀ s t, s ≤ t → σalgebra s ≤ σalgebra t

-- これは Structure Tower そのもの！
-- minLayer = 「最初に情報が得られる時刻」

/-
## 2. マルチンゲール (Martingale)

濾過に適応した確率過程
-/

-- 濾過に適応した過程
-- Xₜ は ℱₜ-可測
-- def Adapted (X : ℝ → Ω → ℝ) (F : Filtration Ω) : Prop :=
--   ∀ t, Measurable (X t) -- with respect to F.σalgebra t

/-
## 3. 停止時刻 (Stopping Time)

濾過に適応した確率時刻
-/

-- τ : Ω → ℝ が停止時刻
-- ⟺ {τ ≤ t} ∈ ℱₜ for all t

-- これも構造塔の概念で定式化できる

/-
## 4. 条件付き期待値

σ-代数の族による階層
-/

-- E[X | ℱₜ] は ℱₜ-可測
-- ℱₛ ⊆ ℱₜ ならば E[E[X | ℱₜ] | ℱₛ] = E[X | ℱₛ]

-- これは「射影」の一種

/-
## 5. 具体例: 情報の蓄積

コイン投げの列での情報の増加
-/

-- コイン投げの濾過
inductive CoinFlip | Heads | Tails
  deriving DecidableEq, Fintype

instance : MeasurableSpace CoinFlip := ⊤

private def coinEval (n : ℕ) : (ℕ → CoinFlip) → CoinFlip :=
  fun ω => ω n

-- σ-代数: n 回目までの結果で生成される可測構造（離散時間濾過）
def coinFiltration : ℕ → MeasurableSpace (ℕ → CoinFlip)
  | 0 => MeasurableSpace.comap (coinEval 0) inferInstance
  | n + 1 =>
      coinFiltration n ⊔ MeasurableSpace.comap (coinEval (n + 1)) inferInstance

@[simp]
lemma coinFiltration_succ (n : ℕ) :
    coinFiltration (n + 1)
      = coinFiltration n ⊔ MeasurableSpace.comap (coinEval (n + 1)) inferInstance :=
  rfl

@[simp]
lemma coinFiltration_zero :
    coinFiltration 0 = MeasurableSpace.comap (coinEval 0) inferInstance :=
  rfl

private lemma coinFiltration_le_succ (n : ℕ) :
    coinFiltration n ≤ coinFiltration (n + 1) := by
  simpa [coinFiltration_succ] using le_sup_left

-- 離散ブラウン運動風濾過は単調である
lemma coinFiltration_monotone : Monotone coinFiltration := by
  classical
  have aux :
      ∀ m, ∀ ⦃k⦄, k ≤ m → coinFiltration k ≤ coinFiltration m :=
    Nat.rec
      (fun k hk => by
        cases k with
        | zero =>
            simpa using (le_rfl : coinFiltration 0 ≤ coinFiltration 0)
        | succ k =>
            exact (Nat.not_succ_le_zero _ hk).elim)
      (fun m ih k hk => by
        have hcases := Nat.lt_or_eq_of_le hk
        cases hcases with
        | inl hlt =>
            have hkm : k ≤ m := Nat.lt_succ_iff.mp hlt
            exact (ih hkm).trans (coinFiltration_le_succ m)
        | inr hEq =>
            simpa [hEq])
  intro n m hnm
  exact aux m hnm

-- これは離散時間の濾過
-- Structure Tower として実装可能

/-
## 6. 確率過程の濾過

ブラウン運動、Poisson過程など
-/

-- Brownian filtration: ℱₜ = σ(Bₛ : s ≤ t)
-- 時刻 t までのブラウン運動で生成される σ-代数

/-
## 実装の詳細

### 連続時間 vs 離散時間
- 離散: ℕ で添字 → 実装が簡単
- 連続: ℝ で添字 → より一般的

### minLayer の意味
確率論では「最初の情報取得時刻」
= 確率変数が可測になる最小時刻

### 右連続性
多くの場合、濾過は右連続であることを要求
ℱₜ = ⋂_{s>t} ℱₛ

これは Structure Tower の追加条件
-/

/-
## 簡単な実装例
-/

-- 離散時間の濾過
def discreteFiltration (Ω : Type*) (F : ℕ → MeasurableSpace Ω)
    (_hmono : Monotone F) : StructureTowerWithMin :=
  StructureTowerWithMin.mk
    (carrier := Σ n : ℕ, {E : Set Ω // (F n).MeasurableSet' E})
    (Index := ℕ)
    (indexPreorder := inferInstanceAs (Preorder ℕ))
    (layer := fun n x => x.1 ≤ n)
    (covering := by
      intro x
      refine ⟨x.1, ?_⟩
      change x.1 ≤ x.1
      exact le_rfl)
    (monotone := by
      intro i j hij x hx
      exact hx.trans hij)
    (minLayer := fun x => x.1)
    (minLayer_mem := by
      intro x
      change x.1 ≤ x.1
      exact le_rfl)
    (minLayer_minimal := by
      intro x i hx
      exact hx)

@[simp]
lemma mem_discreteFiltration_layer {Ω : Type*} {F : ℕ → MeasurableSpace Ω}
    {hmono : Monotone F} {n : ℕ} {x : Σ k : ℕ, {E : Set Ω // (F k).MeasurableSet' E}} :
    x ∈ (discreteFiltration Ω F hmono).layer n ↔ x.1 ≤ n :=
  Iff.rfl

lemma measurable_at_discrete_layer {Ω : Type*} {F : ℕ → MeasurableSpace Ω}
    {hmono : Monotone F} {n : ℕ}
    {x : Σ k : ℕ, {E : Set Ω // (F k).MeasurableSet' E}}
    (hx : x ∈ (discreteFiltration Ω F hmono).layer n) :
    (F n).MeasurableSet' x.2.1 := by
  have hxle : x.1 ≤ n := hx
  have H := hmono hxle
  exact H x.2.1 x.2.2
-- コイン投げフィルトレーションに対応する構造塔
def coinTower : StructureTowerWithMin :=
  discreteFiltration (ℕ → CoinFlip) coinFiltration coinFiltration_monotone

private def coinTower_headsAtZero :
    Σ n : ℕ, {E : Set (ℕ → CoinFlip) //
        (coinFiltration n).MeasurableSet' E} :=
  by
    classical
    refine ⟨0, ⟨{ω : (ℕ → CoinFlip) | ω 0 = CoinFlip.Heads}, ?_⟩⟩
    refine ⟨{a : CoinFlip | a = CoinFlip.Heads}, ?_, rfl⟩
    simpa using (show {a : CoinFlip | a = CoinFlip.Heads} ∈ (⊤ : MeasurableSpace CoinFlip).MeasurableSet' from trivial)

lemma coinTower_headsAtZero_mem :
    coinTower_headsAtZero ∈ coinTower.layer (0 : ℕ) := by
  simp [coinTower, coinTower_headsAtZero]

example :
    coinTower.minLayer coinTower_headsAtZero = (0 : ℕ) := rfl

/-
## 学習価値
- 確率論の基本概念
- 濾過の重要性の理解
- マルチンゲール理論への橋渡し
-/

/-
## 推奨文献
- Williams "Probability with Martingales"
- Karatzas & Shreve "Brownian Motion and Stochastic Calculus"
-/

/-
## なぜこの分野が重要か

1. **実用性**: 金融数学、統計学で直接使用
2. **概念的明確さ**: 濾過は Structure Tower の動機付けとして最適
3. **Mathlib 統合**: 確率論ライブラリとの連携
4. **研究価値**: 現代的な確率論の形式化
-/
