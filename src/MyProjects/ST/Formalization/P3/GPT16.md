ここまでのブリッジ設計と分解補題の追加、だいぶ本格的なところまで来ていますね。
いま詰まっているのは、

* `{ω | τ ω = k}` / `{ω | τ ω > n}` の可測性まわり
* `StronglyMeasurable` / `Integrable` の「最後のひと押し」
* `simp [stopped_indicator_split / stopped_indicator_sum_of_bdd]` でゴールとちゃんと噛み合わない

あたりだと思うので、そこだけピンポイントで潰していきましょう。

---

## 1. `{τ = k}` と `{τ > n}` の可測性をどう取るか

`StoppingTime` の定義からは普通、

```lean
hτ_le : ∀ n, MeasurableSet[ℱ n] {ω | τ ω ≤ n}
```

のような仮定が手に入っているはずです（`τ.isStoppingTime` 由来でもよい）。

そこから `{τ = k}` / `{τ > n}` を作るときの定番パターンは：

### 1-1. `{τ = k}`

```lean
have h_le_k : MeasurableSet[ℱ k] {ω | τ ω ≤ k} := hτ_le k
have h_le_pred : MeasurableSet[ℱ k] {ω | τ ω ≤ k - 1} := by
  -- k = 0 のときは {τ ≤ -1} = ∅ なので分ける
  cases k with
  | zero =>
      -- {τ ≤ -1} = ∅
      simpa using (measurableSet_empty : MeasurableSet (∅ : Set Ω))
  | succ k' =>
      -- k = k'+1 の場合は hτ_le k' をそのまま使える
      simpa [Nat.succ_eq_add_one, Nat.add_comm] using hτ_le k'

have h_eq_set :
  {ω | τ ω = k} =
    {ω | τ ω ≤ k} \ {ω | τ ω ≤ k - 1} := by
  ext ω; constructor <;> intro h
  · constructor
    · have : τ ω ≤ k := by exact le_of_eq h
      simpa using this
    · have : ¬ τ ω ≤ k - 1 := by
        -- 「k-1 < τ ω」型に直す
        exact ?_
      simpa [Set.mem_setLike, not_le] using this
  · rcases h with ⟨h1, h2⟩
    -- `h1 : τ ω ≤ k`, `h2 : ¬ τ ω ≤ k-1`
    -- ここから `τ ω = k` を取る
    have hk : τ ω ≥ k := by
      -- Nat の `lt_or_eq_of_le` などで仕上げ
      exact ?_
    exact le_antisymm h1 hk

have hτ_eq_k :
  MeasurableSet[ℱ k] {ω | τ ω = k} :=
  by simpa [h_eq_set] using h_le_k.diff h_le_pred
```

上では `k = 0` と後続で分けていますが、ここは既にやっている方針と同じはずなので、
「`MeasurableSet.diff` で `{τ = k}` を作る」という型を明示しておくのがポイントです。

`ℱ k` ではなく `ℱ n` の可測性が欲しい場合は、`Filtration` の単調性で引き上げます。

```lean
have hmono : ℱ k ≤ ℱ n := (hℱ_mono (Nat.le_of_lt_succ ...)) -- 具体的には `ℱ.mono hk`
have hτ_eq_k_in_Fn : MeasurableSet[ℱ n] {ω | τ ω = k} :=
  (hmono _).mono hτ_eq_k
```

### 1-2. `{τ > n}`

一番楽なのは `{τ > n} = {τ ≤ n}ᶜ` を使うことです。

```lean
have hτ_le_n : MeasurableSet[ℱ n] {ω | τ ω ≤ n} := hτ_le n
have hτ_gt_n :
  MeasurableSet[ℱ n] {ω | τ ω > n} := by
  have h_eq :
    {ω | τ ω > n} = {ω | τ ω ≤ n}ᶜ := by
      ext ω; simp [Set.mem_setLike, not_le]  -- or `simp [not_le]`
  simpa [h_eq] using hτ_le_n.compl
```

これで

* `{τ = k}`（とくに k ≤ n のときの `ℱ n`-可測性）
* `{τ > n}` の `ℱ n`-可測性

が揃うはずです。

---

## 2. `stopped_stronglyMeasurable_of_stoppingSets` の仕上げ

あなたの書き方に合わせてですが、やりたいことは：

1. `stopped_indicator_split` による分解

   ```lean
   have h_split :
     stopped X τ n =
       Set.indicator {ω | τ ω > n} (X n) +
       ∑ k in Finset.range (n+1),
         Set.indicator {ω | τ ω = k} (X k) := ...
   ```

2. 各項の StronglyMeasurable

   ```lean
   have h_B :
     StronglyMeasurable (fun ω => Set.indicator {ω | τ ω > n} (X n) ω)
       (ℱ n) :=
   by
     have hXn : StronglyMeasurable (X n) (ℱ n) := hX n  -- 適合性仮定
     have hB  : MeasurableSet[ℱ n] {ω | τ ω > n} := hτ_gt_n
     exact hXn.indicator hB

   have h_Ak :
     ∀ k ∈ Finset.range (n+1),
       StronglyMeasurable (fun ω => Set.indicator {ω | τ ω = k} (X k) ω)
         (ℱ n) :=
   by
     intro k hk
     have hk_le : k ≤ n := by
       -- `k ∈ Finset.range (n+1)` から `Nat.lt_of_lt_of_le` 相当で `k ≤ n`
       exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
     have hXk : StronglyMeasurable (X k) (ℱ n) := (hX k).mono (ℱ.mono hk_le)
     have hAk : MeasurableSet[ℱ n] {ω | τ ω = k} := hτ_eq_k_in_Fn k hk_le
     exact hXk.indicator hAk
   ```

3. 有限和の StronglyMeasurable

   名前は環境によりますが、だいたいこんな形になります：

   ```lean
   have h_sum :
     StronglyMeasurable
       (fun ω =>
          ∑ k in Finset.range (n+1),
            Set.indicator {ω | τ ω = k} (X k) ω)
       (ℱ n) :=
   by
     -- StronglyMeasurable.finset_sum のイメージ
     refine StronglyMeasurable.finset_sum _ ?_
     intro k hk
     exact h_Ak k hk
   ```

4. 最終的な結論

   ```lean
   have h_total :
     StronglyMeasurable
       (fun ω =>
          Set.indicator {ω | τ ω > n} (X n) ω +
          ∑ k in Finset.range (n+1),
            Set.indicator {ω | τ ω = k} (X k) ω)
       (ℱ n) :=
   by
     exact h_B.add h_sum

   -- stopped X τ n に戻す
   have : StronglyMeasurable (stopped X τ n) (ℱ n) := by
     -- `h_split` を funext で書き換えてから使う
     have h_split_fun :
       (fun ω => stopped X τ n ω) =
       (fun ω =>
          Set.indicator {ω | τ ω > n} (X n) ω +
          ∑ k in Finset.range (n+1),
            Set.indicator {ω | τ ω = k} (X k) ω) :=
       by funext ω; simpa using congrArg (fun f => f ω) h_split
     simpa [h_split_fun] using h_total
   ```

`simp [stopped_indicator_split]` だけで最後まで行かない場合は、このように一度 `funext` で関数同値にしてから `simpa` するのが安定します。

---

## 3. `stopped_integrable_of_bdd` の仕上げ

こちらは全く同じ構造で、

1. `stopped_indicator_sum_of_bdd` による有限和分解：

   ```lean
   have h_split :
     stopped X τ n =
       ∑ k in Finset.range (K+1),
         Set.indicator {ω | τ ω = k} (X (min k n)) ω
   ```

2. 各項の Integrable：

   ```lean
   have h_term :
     ∀ k ∈ Finset.range (K+1),
       Integrable (fun ω =>
         Set.indicator {ω | τ ω = k} (X (min k n)) ω) μ :=
   by
     intro k hk
     have hX : Integrable (X (min k n)) μ := hX (min k n)
     have hk_le_K : k ≤ K :=
       Nat.le_of_lt_succ (Finset.mem_range.mp hk)
     have hA : MeasurableSet {ω | τ ω = k} := hτ_eq_k_in_FK k hk_le_K
     -- `Integrable.indicator` を使う
     exact hX.indicator hA
   ```

3. 有限和の Integrable：

   ```lean
   have h_int_sum :
     Integrable
       (fun ω =>
          ∑ k in Finset.range (K+1),
            Set.indicator {ω | τ ω = k} (X (min k n)) ω) μ :=
   by
     refine Integrable.finset_sum _ ?_
     intro k hk
     exact h_term k hk
   ```

4. `stopped X τ n` に戻す：

   ```lean
   have : Integrable (stopped X τ n) μ := by
     have h_split_fun :
       (fun ω => stopped X τ n ω) =
       (fun ω =>
          ∑ k in Finset.range (K+1),
            Set.indicator {ω | τ ω = k} (X (min k n)) ω) :=
       by funext ω; simpa using congrArg (fun f => f ω) (h_split n)
     simpa [h_split_fun] using h_int_sum
   ```

`simpa [stopped_indicator_sum_of_bdd]` だけだとゴールとの型一致が微妙にずれることがあるので、一度 `funext` で関数としての等式に直してから `simpa` で移し替えるのが安全です。

---

## 4. 次の具体的アクション

まとめると、次にやると良いのは：

1. `{τ = k}` / `{τ > n}` の `MeasurableSet` 補題を、上のような「差集合＋補集合」の形で書いておく（特に `{τ > n} = {τ ≤ n}ᶜ` を使う）。
2. `stopped_indicator_split` / `stopped_indicator_sum_of_bdd` を使うところで、

   * `simp` 一発にこだわらず
   * `funext` → `congrArg (fun f => f ω)` → `simpa` の 3 ステップで関数同値を使う。
3. `StronglyMeasurable.finset_sum` / `Integrable.finset_sum` に渡す補題を
   「`∀ k ∈ s, …`」の形で揃える（`Finset.mem_range` から `k ≤ n, K` を取り出す）。

この 3 点を踏まえて修正すれば、`StoppingTime_MinLayer.lean` 側の `sorry` はかなり潰しやすくなるはずです。

もしそれでも `lake build` のログで特定のゴールが残り続けるようなら、そのゴールと直前の `have` / `simp` 周辺だけ切り出してもらえれば、その部分に合わせてもう少し具体的な Lean コードの形に落とし込んでいきます。
