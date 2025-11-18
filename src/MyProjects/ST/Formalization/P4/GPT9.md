いまの状況整理と原因分析、かなり正確に押さえられています。

> ・詰まっている場所
> 　- `{τ = k}` / `{τ > n}` の可測性
> 　- `StronglyMeasurable` / `Integrable` の最後の「型合わせ」
> 　- `stopped_indicator_split` / `stopped_indicator_sum_of_bdd` をゴールにきれいに噛ませる部分 

ここを潰すために、やることを「3 ブロック × 超具体的」に絞ります。

---

## 1. `{τ = k}` と `{τ > n}` 可測性の補題を先に切る

MeasureBridge セクションの最初に、**純粋に集合の形をいじる lemma** を 2 本用意しておくと、後がかなり楽になります。

### 1-1. `{τ = k}` を `{τ ≤ k} \ {τ ≤ k-1}` で書く

```lean
lemma stoppingSet_eq_level
    (τ : StoppingTime ℱ) (k : ℕ) :
  {ω | τ ω = k} =
    {ω | τ ω ≤ k} \ {ω | τ ω ≤ k - 1} := by
  ext ω; constructor <;> intro h
  · -- → 方向
    refine And.intro ?h_le ?h_not_le
    · -- τ ω ≤ k
      exact le_of_eq h
    · -- ¬ τ ω ≤ k-1
      have hk : k - 1 < τ ω := by
        -- Nat の基本補題 (`Nat.lt_of_lt_of_le` など) から
        --「k-1 < k = τ ω」を作る
        have : k - 1 < k := Nat.pred_lt (Nat.pos_of_eq_succ ?_) -- ここはお好みで
        -- 最終的には `simp [h]` で `k = τ ω` に書き換えるイメージ
        sorry
      exact not_le_of_gt hk
  · -- ← 方向
    rcases h with ⟨h_le, h_not_le⟩
    -- τ ω ≤ k かつ ¬ τ ω ≤ k-1 から τ ω = k
    have hk : τ ω ≥ k := by
      -- `Nat.le_of_lt_succ` や `lt_of_not_ge` などと
      -- `Nat.lt_succ_iff` を組み合わせて作る
      sorry
    exact le_antisymm h_le hk
```

このあと、

```lean
lemma measurableSet_stoppingSet_eq
    (τ : StoppingTime ℱ) (k : ℕ) :
  MeasurableSet[ℱ k] {ω | τ ω = k} := by
  -- τ の定義から {τ ≤ k}, {τ ≤ k-1} が ℱ k-可測
  have h_le_k   : MeasurableSet[ℱ k] {ω | τ ω ≤ k}   := τ.measurable_le k
  have h_le_k₁  : MeasurableSet[ℱ k] {ω | τ ω ≤ k-1} := by
    -- k=0 の場合を分けて書くか、`Nat.succ` で書き換える
    sorry
  simpa [stoppingSet_eq_level τ k] using h_le_k.diff h_le_k₁
```

みたいな形で、「**k ごとの停止集合は ℱ k-可測**」を先に押さえます。

ℱ n 側が欲しいときは `Filtration.mono` で引き上げる：

```lean
lemma measurableSet_stoppingSet_eq_in_Fn
    (τ : StoppingTime ℱ) {k n : ℕ} (hk : k ≤ n) :
  MeasurableSet[ℱ n] {ω | τ ω = k} := by
  have := measurableSet_stoppingSet_eq (τ := τ) k
  exact this.mono (ℱ.mono hk)
```

### 1-2. `{τ > n}` を `{τ ≤ n}ᶜ` で書く

```lean
lemma measurableSet_stoppingSet_gt
    (τ : StoppingTime ℱ) (n : ℕ) :
  MeasurableSet[ℱ n] {ω | τ ω > n} := by
  have h_le : MeasurableSet[ℱ n] {ω | τ ω ≤ n} := τ.measurable_le n
  have h_eq :
      {ω | τ ω > n} = {ω | τ ω ≤ n}ᶜ := by
    ext ω; simp [not_le]  -- `simp` で {τ>n} <-> ¬(τ≤n) にする
  simpa [h_eq] using h_le.compl
```

これで、MeasureBridge セクションの中からは

* `{τ = k}` の ℱ n 可測性
* `{τ > n}` の ℱ n 可測性

を「名前だけ」で取って来れるようになります。

---

## 2. `stopped_stronglyMeasurable_of_stoppingSets` の整理

やりたいことは：

1. `stopped_indicator_split` で `stopped X τ n` を
   「`{τ>n}` 部分 + `{τ=k}` の有限和」に書き換える。
2. 各項が StronglyMeasurable であることを示す。
3. 有限和の StronglyMeasurable を `StronglyMeasurable.finset_sum` で取る。
4. 最後に `funext` で `stopped X τ n` に戻す。

典型的な書き方はこんなイメージです（変数名・型は手元に合わせて直してください）：

```lean
lemma stopped_stronglyMeasurable_of_stoppingSets
    (X : Process Ω) (τ : StoppingTime ℱ)
    (hX : ∀ n, StronglyMeasurable (X n) (ℱ n)) :
  ∀ n, StronglyMeasurable (stopped X τ n) (ℱ n) := by
  intro n
  -- 1. 分解
  have h_split :=
    stopped_indicator_split (X := X) (τ := τ) (n := n)
  -- h_split :
  --   stopped X τ n =
  --     Set.indicator {ω | τ ω > n} (X n) +
  --     ∑ k in Finset.range (n+1),
  --       Set.indicator {ω | τ ω = k} (X k)

  -- 2. 各項 StronglyMeasurable

  -- 2-1) {τ > n} 部分
  have hXn : StronglyMeasurable (X n) (ℱ n) := hX n
  have hB  : MeasurableSet[ℱ n] {ω | τ ω > n} :=
    measurableSet_stoppingSet_gt (τ := τ) n
  have h_B :
      StronglyMeasurable
        (fun ω => Set.indicator {ω | τ ω > n} (X n) ω)
        (ℱ n) :=
    hXn.indicator hB

  -- 2-2) {τ = k} 部分
  have h_Ak :
    ∀ k ∈ Finset.range (n+1),
      StronglyMeasurable
        (fun ω =>
          Set.indicator {ω | τ ω = k} (X k) ω)
        (ℱ n) := by
    intro k hk
    have hk_le : k ≤ n :=
      Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hXk' : StronglyMeasurable (X k) (ℱ n) :=
      (hX k).mono (ℱ.mono hk_le)
    have hAk : MeasurableSet[ℱ n] {ω | τ ω = k} :=
      measurableSet_stoppingSet_eq_in_Fn (τ := τ) hk_le
    exact hXk'.indicator hAk

  have h_sum :
      StronglyMeasurable
        (fun ω =>
          ∑ k in Finset.range (n+1),
            Set.indicator {ω | τ ω = k} (X k) ω)
        (ℱ n) := by
    -- finset_sum 版の StronglyMeasurable を使う
    refine StronglyMeasurable.finset_sum _ ?_
    intro k hk
    exact h_Ak k hk

  have h_total :
      StronglyMeasurable
        (fun ω =>
          Set.indicator {ω | τ ω > n} (X n) ω +
          ∑ k in Finset.range (n+1),
            Set.indicator {ω | τ ω = k} (X k) ω)
        (ℱ n) :=
    h_B.add h_sum

  -- 3. stopped X τ n に戻す
  have h_split_fun :
      (fun ω => stopped X τ n ω) =
      (fun ω =>
        Set.indicator {ω | τ ω > n} (X n) ω +
        ∑ k in Finset.range (n+1),
          Set.indicator {ω | τ ω = k} (X k) ω) := by
    funext ω
    -- stopped_indicator_split は関数としての等式なので、
    -- `congrArg (fun f => f ω)` で pointwise に落とす
    exact congrArg (fun f => f ω) h_split

  simpa [h_split_fun]
    using h_total
```

ポイントは、

* `simp [stopped_indicator_split]` 一発にこだわらず、
  **`funext`＋`congrArg` で「関数同値 → pointwise 等式」に落とす** こと。
* `{τ>n}` / `{τ=k}` の `MeasurableSet` は、先に単独 lemma として切り出す（上記 1-1 / 1-2）。

---

## 3. `stopped_integrable_of_bdd` の整理

ここも StronglyMeasurable 版とほぼ同じ構造です。違いは：

* 分解に使うのが `stopped_indicator_sum_of_bdd`（range が `K+1`）。
* 各項で使うのが `Integrable.indicator` と `Integrable.finset_sum`。

イメージとしては：

```lean
lemma stopped_integrable_of_bdd
    (X : Process Ω) (τ : StoppingTime ℱ)
    (hX : ∀ n, Integrable (X n) μ)
    (hτ_bdd : ∃ K, ∀ ω, τ ω ≤ K) :
  ∀ n, Integrable (stopped X τ n) μ := by
  intro n
  obtain ⟨K, hK⟩ := hτ_bdd

  -- 1. 有限和分解
  have h_split :=
    stopped_indicator_sum_of_bdd
      (X := X) (τ := τ) (n := n) (K := K) hK
  -- stopped X τ n =
  --   ∑ k in Finset.range (K+1),
  --     Set.indicator {ω | τ ω = k} (X (min k n)) ω

  -- 2. 各項 Integrable
  have h_term :
    ∀ k ∈ Finset.range (K+1),
      Integrable
        (fun ω =>
          Set.indicator {ω | τ ω = k} (X (Nat.min k n)) ω) μ := by
    intro k hk
    have hX_min : Integrable (X (Nat.min k n)) μ :=
      hX (Nat.min k n)
    have hk_le : k ≤ K :=
      Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hAk : MeasurableSet {ω | τ ω = k} :=
      (measurableSet_stoppingSet_eq (τ := τ) k).measure_mono ?_  -- ここは実際の型に合わせて
    -- `Integrable.indicator` を使う
    exact hX_min.indicator hAk

  have h_sum :
      Integrable
        (fun ω =>
          ∑ k in Finset.range (K+1),
            Set.indicator {ω | τ ω = k} (X (Nat.min k n)) ω) μ := by
    refine Integrable.finset_sum _ ?_
    intro k hk; exact h_term k hk

  -- 3. stopped X τ n に戻す
  have h_split_fun :
      (fun ω => stopped X τ n ω) =
      (fun ω =>
        ∑ k in Finset.range (K+1),
          Set.indicator {ω | τ ω = k} (X (Nat.min k n)) ω) := by
    funext ω
    exact congrArg (fun f => f ω) (h_split n)

  simpa [h_split_fun] using h_sum
```

ここも同じく、

* **有限和への書き換えは `funext`＋`congrArg` で行う**
  （`simp` で一発を狙うと型が微妙にずれて失敗しやすい）
* 各項の Integrable は `Integrable.indicator` に落とすために、
  `{τ = k}` の `MeasurableSet` lemma を素直に使う

という形にしておくと、`Integrable.finset_sum` まで含めてゴールが閉じやすくなります。

---

## 4. ここまでやったあとに確認すること

1. MeasureBridge セクションの先頭に

   * `stoppingSet_eq_level`
   * `measurableSet_stoppingSet_eq`
   * `measurableSet_stoppingSet_eq_in_Fn`
   * `measurableSet_stoppingSet_gt`

   のような「集合レベルの補題」を先に置く。

2. `stopped_stronglyMeasurable_of_stoppingSets` / `stopped_integrable_of_bdd` の最後は
   `simp` よりも **`funext`＋`congrArg`＋`simpa`** で決める。

3. それでも `lake build ...` で残る goal があれば、
   「`stopped_indicator_split` が本当に関数等式になっているか」
   「Finset.range の `k ≤ n` / `k ≤ K` をしっかり取り出せているか」
   を一点ずつ確認する。

---

いまのログを見る限り、設計自体は完全に正しい方向に乗っているので、
この「可測性の小 lemma」と「funext での書き換え」を丁寧に入れていけば、
StoppingTime_MinLayer 側のビルドは十分通せる範囲にあります。

もし次に `lake build` を回したときに、まだ 1–2 個だけ具体的なゴールが残るようなら、そのゴールと直前の `have` / `simp` 部分をそのまま貼ってもらえれば、そこだけ Lean コードレベルに落として一緒に潰します。
