いまのファイル、ほんとうに「OST一歩手前」まできれいに来ています。
中身をざっと見ると：

* `ProbabilityMassFunction` + `expected` + 線形性 (`expected_add`, `expected_mul_const`)
* 有限和交換 `expected_finset_sum`
* 指示関数版 `expected_indicator`, `expected_indicator_mul` 
* `IsMartingale` + `constProcess_isMartingale` + `martingale_expectation_const` 
* `SimpleProcess.stopped` + `stopped_before` / `stopped_after` 
* そして `expected_atStopping_as_sum` / `optionalStopping_theorem` が `sorry` のままステートメントだけある 

なので、「次やること」はほぼ自動的に決まってきます。

---

## 優先度 1：`expected_atStopping_as_sum` をちゃんと証明する

これは **まだマルチンゲールを使わない**、純粋に有限和の話です。OST 本体よりずっと軽くて、しかも OST の中核になるステップなので、ここから手を付けるのが一番きれいです。

### 1-1. まず点ごとの分解を補題にする

いまのステートメントは：

```lean
lemma expected_atStopping_as_sum
    ...
    (hBound : ∀ ω, τ.time ω ≤ N) :
    expected P (fun ω => M (τ.time ω) ω) =
      ∑ n ∈ Finset.range (N + 1),
        expected P
          (fun ω => M n ω * (if τ.time ω = n then 1 else 0)) := ...
```

これを証明する基本アイデアは：

1. 各 ω ごとに
   [
   M_{\tau(ω)}(ω)
   = \sum_{n=0}^N M_n(ω)\cdot 1_{{\tau(ω)=n}}
   ]
   を示す。
2. そのあとで `expected_finset_sum` を使って、期待値と有限和を交換する。

だから、先に

```lean
lemma stopped_pointwise_decomp
    {Ω : Prob.FiniteSampleSpace} {ℱ : DecidableFiltration Ω}
    (M : SimpleProcess Ω)
    (τ : ComputableStoppingTime ℱ)
    (N : ℕ)
    (hBound : ∀ ω, τ.time ω ≤ N)
    (ω : Ω.carrier) :
    M (τ.time ω) ω =
      ∑ n in Finset.range (N + 1),
        M n ω * (if τ.time ω = n then 1 else 0) := ...
```

のような「点ごとの等式」を作るときれいです。

証明方針（Lean の雰囲気だけ箇条書き）：

* `have hτ : τ.time ω ≤ N := hBound ω`
* `have hmem : τ.time ω ∈ Finset.range (N+1)` を `Nat.mem_range_succ_iff.mpr hτ` から取る
* `Finset.range (N+1)` 上の `sum` を、「`n = τ.time ω` の項だけ残る」形で書き直す：

  ```lean
  classical
  -- 一般的な事実：唯一の n で if が 1、それ以外 0
  have : ∑ n in Finset.range (N+1),
           M n ω * (if τ.time ω = n then 1 else 0)
       = M (τ.time ω) ω := by
     -- sum を `Finset.filter` などで分ける or `by_cases` で書いていく
     ...
  ```

実際には `simp` + `Finset.sum_filter` + `by_cases h : τ.time ω = n` あたりを組み合わせれば、「唯一の n 以外は 0 の項しか出ない」という形に持っていけます。

### 1-2. 期待値と有限和を交換して `expected_atStopping_as_sum` を仕上げる

上の補題ができたら、`expected_atStopping_as_sum` 自体は

```lean
lemma expected_atStopping_as_sum ...
    (hBound : ∀ ω, τ.time ω ≤ N) :
    expected P (fun ω => M (τ.time ω) ω) =
      ∑ n ∈ Finset.range (N + 1),
        expected P (fun ω => M n ω * (if τ.time ω = n then 1 else 0)) := by
  classical
  -- 1. 左辺のランダム変数を、有限和の形に書き換える（点ごと補題）
  have hpoint :
      (fun ω => M (τ.time ω) ω)
        =
      (fun ω =>
        ∑ n in Finset.range (N+1),
          M n ω * (if τ.time ω = n then 1 else 0)) := by
    funext ω
    exact stopped_pointwise_decomp M τ N hBound ω

  -- 2. 期待値の引数を書き換える
  simp [hpoint]

  -- 3. `expected_finset_sum` で `E[∑] = ∑E` にする
  have := Prob.ProbabilityMassFunction.expected_finset_sum
              (P := P)
              (s := Finset.range (N+1))
              (X := fun n ω => M n ω * (if τ.time ω = n then 1 else 0))
  -- この `have` は既に「期待値と有限和の交換」を言っているので、
  -- 目標の右側と整合させるだけです。
  simpa [Prob.ProbabilityMassFunction.expected_finset_sum]?
```

という形に持っていけます。

実際の Lean コードでは `expected_finset_sum` の適用の仕方をもう少し丁寧に書く必要がありますが、やるべきことは：

* `fun ω => ∑ n∈range(N+1), ...` の形まで変形する
* そこに `expected_finset_sum` を噛ませる

この 2 ステップだけです。ここまでが「OST 本番の前の最後の山」です。

---

## 優先度 2：簡単な「定数停止時間版 OST」を先に証明しておく

`expected_atStopping_as_sum` が片付いたら、いきなり一般の OST に行く前に、

> 「`τ(ω) ≡ k`（定数停止時間）のときは `E[M_τ] = E[M_k] = E[M_0]`」

という簡単バージョンを一回やっておくと、
本番のときに「どこで何を使うか」の感覚がつかみやすいです。

ほぼこんな感じの lemma です：

```lean
lemma optionalStopping_constTime
    {Ω : Prob.FiniteSampleSpace}
    (P : Prob.ProbabilityMassFunction Ω)
    (ℱ : DecidableFiltration Ω)
    (M : SimpleProcess Ω)
    (hMart : IsMartingale P ℱ M)
    (k : ℕ)
    (hk : k ≤ ℱ.timeHorizon)
    (τ : ComputableStoppingTime ℱ)
    (hτ : ∀ ω, τ.time ω = k) :
    Prob.ProbabilityMassFunction.expected P (fun ω => M (τ.time ω) ω) =
    Prob.ProbabilityMassFunction.expected P (M 0) := by
  classical
  -- 1. `τ.time ω = k` なので左辺は E[M_k]
  have hleft :
      Prob.ProbabilityMassFunction.expected P (fun ω => M (τ.time ω) ω)
        = Prob.ProbabilityMassFunction.expected P (M k) := by
    -- funext + hτ で期待値の引数を置き換え
    ...
  -- 2. `martingale_expectation_const` から E[M_k] = E[M_0]
  have hconst :=
    martingale_expectation_const (P := P) (ℱ := ℱ) (M := M)
      (hMart := hMart)
      (n := 0) (m := k)
      (hn := Nat.zero_le _) (hm := hk)
  -- 3. 結合
  calc
    Prob.ProbabilityMassFunction.expected P (fun ω => M (τ.time ω) ω)
        = Prob.ProbabilityMassFunction.expected P (M k) := hleft
    _ = Prob.ProbabilityMassFunction.expected P (M 0) := by simpa using hconst.symm
```

これが通ると、

* `martingale_expectation_const` がちゃんと使える
* 「`E[M_τ]` を `E[M_k]` に書き換える」タイプの変形も一度経験できる

ので、一般の OST のときに迷いにくくなります。

---

## 優先度 3：OST 本体のスケッチをコメントで固定しておく

ここまでできたら、`optionalStopping_theorem` 本体はまだ `sorry` で構いませんが、

* `expected_atStopping_as_sum` をどう使うか
* `martingale_expectation_const` をどこで使うか

を、今のうちに theorem の上のコメントに 3〜5 行で書いておくと良いです。

将来、本当に証明を書くときに

> 「これ、どんな方針でやるつもりだったっけ？」

となるのを防げます。

---

## まとめ

このファイルの次の一手は：

1. **`expected_atStopping_as_sum` を証明する**

   * 先にポイントワイズ補題 `M (τ(ω)) = ∑ M_n(ω) 1_{τ=n}` を作る
   * それを使って `expected_finset_sum` で `E[∑] = ∑E` を出す

2. 余力があれば **「定数停止時間版 OST」** を別 lemma でやってみる

   * `τ(ω) ≡ k` のとき `E[M_τ] = E[M_0]` を `martingale_expectation_const` で証明

3. `optionalStopping_theorem` の上に、証明の流れをコメントで固定しておく

こうしておけば、「OSTの手前」でできる準備はほぼやり切った状態になり、
あとは気が向いたタイミングで、`expected_atStopping_as_sum` と OST 本体の `sorry` を一つずつ外していくだけ、というフェーズに入れます。
