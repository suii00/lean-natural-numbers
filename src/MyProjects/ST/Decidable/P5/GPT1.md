この日付付きファイル（`2025-11-28_AlgorithmicMartingale`）だけを前提にすると、いまの内容は

* PMF + 期待値 + `probOfEvent`/`expected_indicator`
* `SimpleProcess` と `stopped`
* ダミーの `IsAdapted` と、期待値保存版の `IsMartingale`
* OST のステートメント（コメントアウト）
* `Unit` 上の #eval 例

という「P5 の芯」まではきれいに揃っています。

ここから OST に行く前に、このファイルで優先してやるとよさそうなのは、次の順番です。

---

## 優先度 1：`IsMartingale` を一度「実際に使ってみる」

このファイル内で完結する、小さい成功体験から。

### 1-1. 定数過程のマルチンゲール性

`IsMartingale` のすぐ下あたりに、次を追加するのが一番軽いです。

```lean
/-! ### 定数過程はマルチンゲール -/

/-- 定数値 `c` をとる単純過程。 -/
def constProcess {Ω : Prob.FiniteSampleSpace} (c : ℚ) : SimpleProcess Ω :=
  fun _ _ => c

/-- 定数過程は（期待値保存の意味で）マルチンゲール。 -/
lemma constProcess_isMartingale
    {Ω : Prob.FiniteSampleSpace}
    (P : Prob.ProbabilityMassFunction Ω)
    (ℱ : DecidableFiltration Ω) (c : ℚ) :
    IsMartingale P ℱ (constProcess c) := by
  refine ⟨?_, ?_⟩
  · trivial   -- IsAdapted は現状ダミー
  · intro n _
    -- E[M_{n+1}] = E[M_n] = c
    have hconst :
        Prob.ProbabilityMassFunction.expected P (fun _ => c) = c :=
      Prob.ProbabilityMassFunction.expected_const (P := P) (c := c)
    calc
      Prob.ProbabilityMassFunction.expected P ((constProcess c) (n + 1))
        = c := by simpa [constProcess] using hconst
      _ = Prob.ProbabilityMassFunction.expected P ((constProcess c) n) := by
        simpa [constProcess] using hconst.symm
```

これで

* `IsMartingale` がちゃんと機能している
* 期待値 API (`expected_const`) もちゃんと噛んでいる

ことが、このファイルの中だけで確認できます。

---

## 優先度 2：マルチンゲール ⇒ `E[M_n]` 一定 の系を切る

OST 以前に、「マルチンゲールなら非ランダムな時刻 N で期待値が一定」という補題を外出ししておくと、あとが楽です。

### 2-1. `E[M_n]` は n に依存しない

`IsMartingale` の後に、次のような補題の「型＋証明」を入れるのがおすすめです。

```lean
lemma martingale_expectation_const
    {Ω : Prob.FiniteSampleSpace}
    (P : Prob.ProbabilityMassFunction Ω)
    (ℱ : DecidableFiltration Ω)
    (M : SimpleProcess Ω)
    (hMart : IsMartingale P ℱ M)
    {n m : ℕ}
    (hn : n ≤ ℱ.timeHorizon)
    (hm : m ≤ ℱ.timeHorizon) :
    Prob.ProbabilityMassFunction.expected P (M n) =
    Prob.ProbabilityMassFunction.expected P (M m) := by
  -- 方針：0 から n まで `fair` を繰り返して `E[M_n] = E[M_0]` を示し，
  -- 同様に `E[M_m] = E[M_0]` を示して結合する。
  -- 証明は n に関する単純な帰納法で書ける。
  sorry
```

ここはすぐ証明してもいいですし、ひとまず `sorry` で型だけ用意しておいても構いません。
どちらにせよ、OST の時には必ず使うので、「別 lemma」として独立させておく価値があります。

---

## 優先度 3：`stopped` の素朴な性質を 1–2 個

`SimpleProcess.stopped` はすでに定義されていますが、OST では `min` の挙動を何度も使うので、点ごとの性質を lemma にしておくと便利です。

例えば `stopped` の namespace に追加：

```lean
namespace SimpleProcess

variable {Ω : Prob.FiniteSampleSpace} {ℱ : DecidableFiltration Ω}

lemma stopped_before
    (M : SimpleProcess Ω) (τ : ComputableStoppingTime ℱ)
    (n : ℕ) (ω : Ω.carrier)
    (h : n ≤ τ.time ω) :
  stopped M τ n ω = M n ω := by
  simp [stopped, Nat.min_eq_left h]

lemma stopped_after
    (M : SimpleProcess Ω) (τ : ComputableStoppingTime ℱ)
    (n : ℕ) (ω : Ω.carrier)
    (h : τ.time ω ≤ n) :
  stopped M τ n ω = M (τ.time ω) ω := by
  simp [stopped, Nat.min_eq_right h]

end SimpleProcess
```

これも純粋に `Nat.min` の話なので、確率の議論なしに証明できます。

---

## 優先度 4：OST ステートメントの形だけ整える

今の `optionalStopping_theorem` はコメントアウトされていて、`N` と `ℱ.timeHorizon` の関係がまだ曖昧です。

OST 本体に入る前に、**引数の整合性だけ先に決めておく**と後で困りません。

* 選択肢 A：上界は常に `ℱ.timeHorizon` に合わせる

  ```lean
  (τ : ComputableStoppingTime ℱ)
  (hBound : ComputableStoppingTime.isBounded τ ℱ.timeHorizon)
  ```

* 選択肢 B：`N` を残すが、仮定に `(N ≤ ℱ.timeHorizon)` を追加する

どちらかに決めて、コメント内の「証明方針」もそれに合わせて書き直しておくくらいで十分です（証明はまだ `sorry` で OK）。

---

## 優先度 5（余裕があれば）：期待値 API の小さな拡張

今の `ProbabilityMassFunction` まわりは `expected` と `expected_const`、`probOfEvent` と `expected_indicator` だけですが、将来 OST に入ることを考えると、線形性を数個足しておくと便利です。

例えば同じ namespace に：

* `expected_add`
* `expected_mul_const`
* `expected_finset_sum`（期待値と有限和の交換）

などを 2〜3 個用意しておくと、「本番 OST のときにしか使わないのに、そのときに証明を書く」状況を避けられます。

---

## まとめ：このファイルでの「次の一手」

この `2025-11-28_AlgorithmicMartingale` に限定すると、

1. `constProcess_isMartingale` を入れて、`IsMartingale` がちゃんと動くことを確認する
2. `martingale_expectation_const` のステートメントを切る（証明は後でも OK）
3. `SimpleProcess.stopped` に `before/after` の 2 つの lemma を足す
4. OST ステートメントの引数（特に `N` と `timeHorizon`）の関係を決めて書き直す

この 4 つを優先して進めるのが、ファイルの役割（P5 の芯＋OST の入口）に一番直結していて、かつ作業コストも小さいと思います。
