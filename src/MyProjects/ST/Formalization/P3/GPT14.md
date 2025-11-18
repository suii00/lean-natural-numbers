いいですね、「有界停止時間で止めた過程もマルチンゲール」という optional stopping の芯の部分まで、構造体レベルで形が見えるところまで来ましたね。
`noncomputable def stoppedProcess_martingale_of_bdd` を `sorry + 理由付き TODO` で立てておくのも、設計を固める意味ではとてもよい進め方だと思います。

せっかく骨格ができたので、「3 つのフィールドをどう埋めていくか」をもう少し細かいレベルまで分解しておきます。

---

## 1. `adapted` フィールドの埋め方

ここは「P3 側に落とせる部分」と「P4 側でやるしかない部分」を分けると楽です。

### 方針

* 可能なら P3 (`StoppingTime_MinLayer.lean`) に

  ```lean
  lemma StoppedProcess.adapted
      (X : Process Ω)
      (hX : Adapted ℱ X)
      (τ : StoppingTime ℱ) :
    Adapted ℱ (stopped X τ)
  ```

  のような lemma を用意しておく。

* P4 では、

  ```lean
  adapted :=
    StoppedProcess.adapted (X := M.process)
      (hX := M.adapted) (τ := τ)
  ```

  という 1 行で済ませる。

もし P3 にまだ「stopped は adapted を保つ」という lemma がなければ、先にそちらを作るのがおすすめです。
証明自体は、あなたが既に入れている

* `stopped_eq_of_le` / `stopped_const_of_ge` / `stopped_eq_atStoppingTime`

の P3 版（`StoppedProcess.eq_before_stopping` 等）を使って、

* 各 `n` について `stopped X τ n` が
  「`{τ ≤ n}` と ` {τ > n}` の 2 つの可測集合上の貼り合わせ」で書ける
* それぞれの部分で `X` が `ℱ n` 可測

ことから `StronglyMeasurable[ℱ n]` を示す、という定型パターンになります。

---

## 2. `integrable` フィールドの埋め方

ここは「有界停止時間」の仮定をがっつり使う箇所です。

### 方針（P3 レイヤに押し込む）

P3 側に、マルチンゲールを意識しない純粋な lemma として：

```lean
lemma stopped_integrable_of_bdd
    (X : Process Ω)
    (hX : ∀ n, Integrable (X n) μ)
    (τ : StoppingTime ℱ)
    (hτ_bdd : ∃ K, ∀ ω, τ ω ≤ K) :
  ∀ n, Integrable (stopped X τ n) μ
```

のような形を用意しておきます。

証明の典型パターン：

1. 有界性から `τ ω ≤ K` を取る。

2. `stopped X τ n` を

   ```lean
   stopped X τ n =
     ∑ k in Finset.range (K+1),
       Set.indicator {ω | τ ω = k} (X (min k n)) ω
   ```

   のような有限和で書く（実際の形はあなたの `stopped` 定義に合わせて調整）。

3. 各項は `Integrable`（`hX` と indicator の積）なので、
   `Integrable.finset_sum` から有限和も `Integrable`。

これで P3 に「有界停止時間のもとで停止過程は integrable」という結果が落ちます。

P4 の `stoppedProcess_martingale_of_bdd` では、単に

```lean
integrable := fun n =>
  stopped_integrable_of_bdd
    (X := M.process) (hX := M.integrable)
    (τ := τ) (hτ_bdd := hτ_bdd) n
```

と呼ぶだけで済みます。

---

## 3. `martingale_property` フィールドの埋め方

ここが optional stopping のコアです。すでに入れてある

* `stoppedProcess_eq_of_le`
* `stoppedProcess_const_of_ge`
* `stoppedProcess_eq_atStoppingTime`

を活かしつつ、次の 2–3 本の中間補題を作ると、だいぶ書きやすくなります。

### 3-1. 「元のマルチンゲールの増分」の condExp = 0

まず元のマルチンゲールについて、

```lean
lemma Martingale.condExp_increment_zero
    (M : Martingale μ) (n : ℕ) :
  condExp μ M.filtration n
      (fun ω => M.process (n+1) ω - M.process n ω)
    =ᵐ[μ] 0 :=
by
  -- condExp の線形性から
  -- condExp (M_{n+1} - M_n)
  --   = condExp M_{n+1} - condExp M_n
  --   = M_n - M_n
  sorry
```

を 1 本持っておきます。

ここでは `condExp_add` / `condExp_smul` 系の lemma と、あなたの `Martingale.condExp_next` を組み合わせるだけです。

### 3-2. 停止過程の増分＝indicator×増分

次に、先ほど少し具体的に書いたような

```lean
lemma Martingale.stoppedProcess_increment_indicator
    (M : Martingale μ) (τ : StoppingTime M.filtration) (n : ℕ) :
  ∀ ω,
    M.stoppedProcess τ (n+1) ω - M.stoppedProcess τ n ω =
      Set.indicator {ω | τ ω > n}
        (fun ω => M.process (n+1) ω - M.process n ω) ω :=
by
  intro ω
  by_cases h : τ ω ≤ n
  · -- ケース τ ω ≤ n：左辺も右辺も 0
    -- 左: `stoppedProcess_const_of_ge` から差が 0
    -- 右: `¬ τ ω > n` なので indicator が 0
    sorry
  · -- ケース τ ω > n：停止していないので両方とも元の増分
    -- 左: `stoppedProcess_eq_of_le` から
    -- 右: indicator = 1 倍
    sorry
```

を P4 に置きます。

### 3-3. condExp_next の埋め方

上記 2 本を使って、`stoppedProcess_martingale_of_bdd` の中で

```lean
martingale_property := by
  intro n
  -- Y := M.stoppedProcess τ
  -- 目標: condExp μ ℱ n Y_{n+1} =ᵐ Y_n
  -- これは condExp(ΔY_{n+1}) = 0 に帰着させると書きやすい
  --
  -- 1. 増分形に書き換え
  have hΔ :
    (fun ω => Y (n+1) ω - Y n ω)
      = fun ω =>
          Set.indicator {ω | τ ω > n}
            (fun ω => M.process (n+1) ω - M.process n ω) ω := by
    -- `stoppedProcess_increment_indicator` を使う
    funext ω; exact (M.stoppedProcess_increment_indicator τ n ω).symm
  -- 2. condExp(ΔY) = condExp(indicator * ΔM) を condExp の線形性で整理
  -- 3. `τ` の停止時間性から `{τ > n} ∈ ℱ n` を使い、
  --    「ℱ_n 可測な有界関数 × ΔM」の condExp が 0 になることを示す
  --
  -- 最終的に condExp Y_{n+1} =ᵐ Y_n を得る
  sorry
```

という流れです。

ここで必要なのは：

* `{ω | τ ω > n}` が `M.filtration n` に属する（停止時間の定義から）
* `Set.indicator` が `ℱ n`-可測かつ有界である（`Adapted`＋有界停止時間から導ける）
* `condExp` に対して「ℱ n 可測な有界関数 g と、`ΔM_{n+1}` の積」の条件付き期待値が 0 になる、という lemma

最後の部分は、mathlib にはだいたい

* `condexp_mul` / `condexp_smul`
* 「ℱ 可測な g と Y について condexp(g * Y) = g * condexp(Y)」型のもの

が用意されているので、`Martingale.condExp_increment_zero` と組み合わせれば

```lean
condExp μ ℱ n (indicator * ΔM)
  = indicator * condExp μ ℱ n (ΔM)
  = indicator * 0
  = 0
```

まで落とせるはずです。

---

## 4. いまの skeleton のままで大丈夫か

`noncomputable def stoppedProcess_martingale_of_bdd := { … adapted := sorry, … }`
という形であれば、`sorry` 付きの定義として一旦コンパイルされ、
`lake build` 上は「warning（sorry が残っています）」で止まっている状態だと思います。

設計としてはかなりきれいに切れているので、

1. P3 に「stopped の adapted/integrable」を落とす
2. P4 に「増分＝indicator×増分」「元の増分の condExp = 0」の 2 本を先に書く
3. それらを使って `martingale_property` を埋める

という順番で `sorry` を 1 つずつ潰していくのが、一番ストレスが少ないと思います。

もしこのどこかのステップで具体的に詰まった箇所（`Set.indicator` 周りの measurability や、`condexp_*` の lemma 名など）が出てきたら、その部分のコード断片ごと持ってきてもらえれば、そこだけピンポイントで Lean の書き方に落とすお手伝いをします。
