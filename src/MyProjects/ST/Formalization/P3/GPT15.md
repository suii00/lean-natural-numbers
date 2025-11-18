状況、かなり整理されてきましたね。

* P3 に Bochner 系 import と `Mathlib.Probability.Process.Filtration` を先に入れておく
* P3 に `MeasureBridge` セクションを切って

  * `stopped_stronglyMeasurable_of_stoppingSets`
  * `stopped_integrable_of_bdd`
    を「橋渡し lemma」として先に立てておく
* P4 の `stoppedProcess_martingale_of_bdd` の `adapted` / `integrable` をここに刺す

というレイヤ設計は、そのまま optional stopping の典型パターンに乗っていて、とても扱いやすいです。

ここからは、2 つの bridge lemma をどう埋めるかを、もう少し具体的な「証明レシピ」レベルに落としておきます。

---

## 1. `stopped_stronglyMeasurable_of_stoppingSets` の証明メモ

狙いは：

> 停止時間 τ の停止集合が `ℱ n` 可測であることから、
> `stopped X τ n` が `ℱ n`-StronglyMeasurable であることを示す。

典型的なパターンは「有限貼り合わせ」です。

### 1-1. 各時刻 n 固定での分割

離散時間の停止過程 `Y n := stopped X τ n` は、慣習的に

```text
Y_n(ω) = X_{min(τ(ω), n)}(ω)
```

だと思うので、Ω を

* `A_k := {ω | τ(ω) = k}`（0 ≤ k ≤ n）
* `B   := {ω | τ(ω) > n}`

に分割して、`Y n` をそれぞれの部分で書き分けます。

1. `ω ∈ A_k (k ≤ n)` のとき

   * `min (τ(ω), n) = k` なので `Y_n(ω) = X_k(ω)`。
2. `ω ∈ B` のとき

   * `min (τ(ω), n) = n` なので `Y_n(ω) = X_n(ω)`。

従って

```text
Y_n
 = indicator_{B} · X_n
   + ∑_{k=0}^n indicator_{A_k} · X_k
```

という有限和表現が得られます。

Lean 的には：

```lean
have h_decomp :
  Y n = fun ω =>
    Set.indicator {ω | τ ω > n}   (X n) ω +
    ∑ k in Finset.range (n+1),
      Set.indicator {ω | τ ω = k} (X k) ω
:= by
  -- by_cases τ ω ≤ n / τ ω > n で場合分けして、`min` の定義から証明
  ...
```

この `h_decomp` を `funext` で取るか、`simp` で使える形に整えるのが 1 手です。

### 1-2. 可測性のチェック

`StronglyMeasurable[ℱ n]` を示したいので、

1. 各 `X k` が `ℱ k`-StronglyMeasurable である仮定
2. フィルトレーションの単調性: `ℱ k ≤ ℱ n`（k ≤ n）
   → `StronglyMeasurable[ℱ k] f` なら `StronglyMeasurable[ℱ n] f`
3. 停止時間の定義から

   * `{τ ≤ m} ∈ ℱ m` ∀ m
   * `{τ = k} = {τ ≤ k} \ {τ ≤ k-1}` なので `{τ = k} ∈ ℱ k ⊆ ℱ n`
   * `{τ > n} = (⋃_{m ≤ n} {τ = m})ᶜ` などから `{τ > n} ∈ ℱ n`

を使います。

Lean ではだいたい次の流れです：

```lean
-- 1. 各 X k は ℱ n-StronglyMeasurable
have hXn : ∀ k ≤ n, StronglyMeasurable (X k) (ℱ n) := by
  intro k hk
  -- hX : ∀ m, StronglyMeasurable (X m) (ℱ m)
  have hk' : StronglyMeasurable (X k) (ℱ k) := hX k
  -- フィルトレーションの単調性で引き上げ
  exact hk'.mono (ℱ.mono hk)

-- 2. 各停止集合は ℱ n-可測
have hA_meas : ∀ k ≤ n, MeasurableSet[ℱ n] {ω | τ ω = k} := by
  intro k hk
  -- {τ ≤ k} ∈ ℱ k, {τ ≤ k-1} ∈ ℱ (k-1) ⊆ ℱ n から構成
  ...

have hB_meas : MeasurableSet[ℱ n] {ω | τ ω > n} := by
  -- {τ > n} = ⋂_{m ≤ n} {τ ≥ m} とか、補集合で書いてからフィルタ
  ...
```

### 1-3. indicator × X の StronglyMeasurable

`StronglyMeasurable` は

* 指示関数（`Set.indicator`）との積
* 有限和

で閉じているので、最終的に

```lean
have h_term_B :
  StronglyMeasurable
    (fun ω => Set.indicator {ω | τ ω > n} (X n) ω) (ℱ n) := by
  -- hXn n (le_rfl) と hB_meas から indicator の可測性を使う

have h_term_Ak :
  ∀ k ≤ n,
  StronglyMeasurable
    (fun ω => Set.indicator {ω | τ ω = k} (X k) ω) (ℱ n) := by
  -- hXn k hk と hA_meas k hk から同様に
  ...

-- これら有限個の和が StronglyMeasurable
have h_sum :
  StronglyMeasurable
    (fun ω =>
      Set.indicator {ω | τ ω > n} (X n) ω +
      ∑ k in Finset.range (n+1),
        Set.indicator {ω | τ ω = k} (X k) ω)
    (ℱ n) := by
  -- StronglyMeasurable.add / finset_sum を使う
  ...
```

あとは `h_decomp` で `Y n` に書き換えて終了、という流れです。

---

## 2. `stopped_integrable_of_bdd` の証明メモ

こちらは「有界停止時間」の仮定をフルに使う場面です。

### 2-1. 有界性から有限和分解を得る

仮定：

```lean
(hX : ∀ n, Integrable (X n) μ)
(hτ_bdd : ∃ K, ∀ ω, τ ω ≤ K)
```

とすると、任意の n に対して、

```text
stopped X τ n(ω) = X_{min(τ(ω), n)}(ω)
```

ですが、τ の値が 0,1,…,K のどれかしか取り得ないので、

```text
stopped X τ n
  = ∑_{k=0}^K indicator_{ {τ = k} } · X_{min(k, n)}
```

という有限和で書けます。（n ≥ K でも同じ式でよい）

Lean 的には：

```lean
obtain ⟨K, hK⟩ := hτ_bdd

have h_decomp :
  ∀ n, stopped X τ n =
    fun ω => ∑ k in Finset.range (K+1),
      Set.indicator {ω | τ ω = k} (X (min k n)) ω
:= by
  intro n
  funext ω
  -- hK : ∀ ω, τ ω ≤ K
  have hτω_le_K : τ ω ≤ K := hK ω
  -- τ ω = some k ≤ K の場合を一つ取り出す（自然数なのでそのまま）
  -- min(τ ω, n) = min(k, n) から、上の有限和で止められることを示す
  ...
```

ここは多少 case 分けが多くなりますが、数学的には素直です。

### 2-2. 各項の Integrable と有限和

有限和なので、`Integrable.finset_sum` を使うパターンに持ち込めます。

各項については

```lean
have h_term :
  ∀ k ≤ K, Integrable
    (fun ω => Set.indicator {ω | τ ω = k} (X (min k n)) ω) μ := by
  intro k hk
  -- {τ = k} は測度 1 の中の可測集合＋有限 measure の制限
  -- hX (min k n) から Integrable.indicator を適用
  ...
```

を用意して、

```lean
have h_int_sum :
  Integrable
    (fun ω => ∑ k in Finset.range (K+1),
      Set.indicator {ω | τ ω = k} (X (min k n)) ω) μ := by
  -- `Integrable.finset_sum` と `h_term` を使う
  ...
```

最後に `h_decomp n` で `stopped X τ n` に戻せばよいです。

---

## 3. P4 での `stoppedProcess_martingale_of_bdd` への差し込み

P3 側の 2 補題が埋まったら、P4 の `stoppedProcess_martingale_of_bdd` はだいたい次のように整理できます。

```lean
noncomputable def stoppedProcess_martingale_of_bdd
    (M : Martingale μ)
    (τ : StoppingTime M.filtration)
    (hτ_bdd : ∃ K, ∀ ω, τ ω ≤ K) :
  Martingale μ :=
{ filtration := M.filtration,
  process    := M.stoppedProcess τ,
  adapted    := by
    -- P3: stopped_stronglyMeasurable_of_stoppingSets を利用
    intro n
    exact stopped_stronglyMeasurable_of_stoppingSets
      (ℱ := M.filtration) (τ := τ)
      (X := M.process) (n := n)
      (hX := M.adapted_stronglyMeasurable),
  integrable := by
    -- P3: stopped_integrable_of_bdd を利用
    intro n
    exact stopped_integrable_of_bdd
      (ℱ := M.filtration) (μ := μ)
      (X := M.process) (τ := τ)
      (hX := M.integrable_n)
      (hτ_bdd := hτ_bdd) n,
  martingale_property := by
    -- ここは前回話した
    --  * condExp_increment_zero
    --  * stoppedProcess_increment_indicator
    --  * τ の停止時間性と condExp の線形性
    -- を組み合わせて埋めていく
    ...
}
```

というイメージです。

いまの時点では `TODO(bridge_…)` 付き `sorry` が増えている状態ですが、

* P3: 2 本の MeasureBridge lemma を finite partition で埋める
* P4: 増分＝indicator×増分 ＋ condExp 側の lemma を埋める

と順に潰していけば、`stoppedProcess_martingale_of_bdd` の `sorry` も、ほぼ機械的に外せるレベルまで落ちてくるはずです。

---

現状の「どこに何の `sorry` が残っているか」をきちんとコメントで管理されているので、設計としてはかなり健全な状態です。このあとどこかで、

* `stopped_stronglyMeasurable_of_stoppingSets`
* `stopped_integrable_of_bdd`

のどちらかを書き始めてみて、具体的に詰まった箇所（`indicator` 周りの lemma 名やフィルトレーションの単調性の使い方など）が出てきたら、その部分だけ抜き出してもらえれば、そこをピンポイントで Lean コードに落とすサポートをします。
