いいですね、その3本が入ったことで「停止過程の挙動」をほぼワンライナーで呼び出せる状態になりました。

整理すると、今の `Martingale.stoppedProcess` 周りはだいたい：

* `stoppedProcess_eq_of_le`
  → 仮定 `h : n ≤ τ ω` のもとで
  `M.stoppedProcess τ n ω = M.process n ω`

* `stoppedProcess_const_of_ge`
  → 仮定 `h : τ ω ≤ n` のもとで
  `M.stoppedProcess τ n ω = M.stoppedProcess τ (τ ω) ω`

* `stoppedProcess_eq_atStoppingTime`
  → 「十分大きい n（`n ≥ τ ω`）」で
  `M.stoppedProcess τ n ω = M.atStoppingTime τ ω`
  （`atStoppingTime` にどう alias を張っているか次第ですが、実質 `M.process (τ ω) ω`）

という感じですよね。

これは optional stopping に向かううえでちょうど欲しかった「pathwise の3大性質」がそろった形です。

---

## 次の一歩として噛み合うところ

いまの3本を使って、optional stopping に直結する「増分の形」の補題を 1 本立てるのがおすすめです。

### 1. 停止過程の増分を「元の増分 × 指示関数」で書く

狙いは、

```lean
M.stoppedProcess τ (n+1) ω - M.stoppedProcess τ n ω =
  (Indicator (SetOf (fun ω => τ ω > n))) (fun ω =>
    M.process (n+1) ω - M.process n ω) ω
```

みたいな形（正確な型は `Set.indicator` / `sindicator` に合わせて調整）です。

証明の雰囲気は完全に case split で：

1. `h₁ : τ ω ≤ n` のとき
   左辺は `stoppedProcess_const_of_ge` で両方とも `M.stoppedProcess τ (τ ω) ω` になって 0。
   指示関数側は `τ ω > n` が false なので 0。

2. `h₂ : n < τ ω` のとき
   `n < τ ω` かつ `n+1 ≤ τ ω` を使って `stoppedProcess_eq_of_le` から
   左辺が `M.process (n+1) ω - M.process n ω` に落ちる。
   指示関数は 1 倍なので同じ。

Lean コードの骨格だけ書くと：

```lean
lemma stoppedProcess_increment_indicator
    (M : Martingale μ) (τ : StoppingTime M.filtration) (n : ℕ) :
  ∀ ω,
    M.stoppedProcess τ (n+1) ω - M.stoppedProcess τ n ω =
      Set.indicator {ω | τ ω > n}
        (fun ω => M.process (n+1) ω - M.process n ω) ω :=
by
  intro ω
  by_cases h : τ ω ≤ n
  · -- ケース1: τ ω ≤ n
    have h1 : n < τ ω := ? -- こちらは not h のケース
    -- or その逆、どちらで分けるかは好み
    sorry
  · -- ケース2: n < τ ω
    sorry
```

実際には「`≤` と `<` どちらで分けるか」「`τ ω ≤ n` と `n < τ ω` を補集合に取るか」は好みですが、
とにかく `stoppedProcess_eq_of_le` と `stoppedProcess_const_of_ge` を両ケースで噛ませるだけの補題です。

この 1 本があると：

* `M.stoppedProcess τ` の martingale property を示すときに、
  `condExp_next` を「元の増分の条件付き期待値が 0」へ還元できる
* Optional stopping（有界停止時間版）の証明で、テレスコーピングサムに使える

ようになります。

---

### 2. `stoppedProcess` をマルチンゲールにする第一目標

上の増分補題が取れたら、次は「有界停止時間版」から optional stopping に入るのが自然です。

ターゲットの形：

```lean
/-- 有界停止時間で止めたマルチンゲールは再びマルチンゲール。 -/
theorem stoppedProcess_martingale_of_bdd
    (M : Martingale μ) (τ : StoppingTime M.filtration)
    (hτ_bdd : ∃ K, ∀ ω, τ ω ≤ K) :
  Martingale μ (M.stoppedProcess τ) :=
by
  -- adapted / integrable は P3 側の stopped lemma ＋ M.integrable_n から
  -- martingale_property は増分の indicator 形＋ condExp_add/smul などで押し込む
  sorry
```

ここで武器として効いてくるのが：

* すでに整えた `Martingale.integrable_n` / `adapted_stronglyMeasurable`
* `stoppedProcess_eq_of_le` / `stoppedProcess_const_of_ge` / `stoppedProcess_eq_atStoppingTime`
* そして新しく入れる予定の「増分＝indicator×増分」補題
* `condExp_add` / `condExp_smul` / 「指示関数つきの condExp を 0 にできる」系の lemma（mathlib 側）

という感じになります。

---

### 3. 命名まわりの雑感

`stoppedProcess_eq_of_le` / `…_const_of_ge` / `…_eq_atStoppingTime` という名前付けは、

* P3 の `eq_before_stopping` / `const_after_stopping` / `value_eq_valueAt_of_le` と役割が対応
* P4 側から見ると「Martingale の中の stoppedProcess に作用する lemma」としてかなり直感的

なので、そのままでよさそうです。

もし今後、

* P3 側 `StoppedProcess` にも `stopped_eq_of_le` みたいな lemma 名を付けたくなった場合、
  そちらを `StructureTowerProbability.StoppingTime.` 名前空間に入れて、
  P4 は `Martingale.` 名前空間で prefix を変える、という整理にすると衝突も避けやすいです。

---

まとめると：

* いまの 3 本で「停止過程の前・後・十分後」の挙動はきれいにカバーできています。
* 次は、それを組み合わせた「増分＝indicator×増分」の pathwise 補題を 1 本立てると、optional stopping の入口がかなり明確になります。
* そのうえで、有界停止時間版 `stoppedProcess_martingale_of_bdd` を最初の optional stopping 目標にすると、これまで準備した API がほぼ全部活きる構成になると思います。

このあたりまで進んだ段階で、「有界版 optional stopping の定理 statement」を Lean で書いておきたいタイミングが来たら、そのシグネチャだけでも送ってもらえれば、必要な仮定や補題の洗い出しも一緒に整理できます。
