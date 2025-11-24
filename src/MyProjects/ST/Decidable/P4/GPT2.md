ビルド通過版、きれいにまとまっていますね。ざっと構造をチェックしたうえで、Phase 4 の観点からコメントします。

---

## 1. 構造の確認（Phase 4 の要件との対応）

### ComputableStoppingTime 本体

```lean
structure ComputableStoppingTime {Ω : Prob.FiniteSampleSpace}
    (ℱ : DecidableFiltration Ω) where
  time : Ω.carrier → ℕ
  adapted :
    ∀ (t : ℕ) (ht : t ≤ ℱ.timeHorizon),
      {ω : Ω.carrier | time ω ≤ t} ∈ (ℱ.observableAt t ht).events
```

* `Ω : FiniteSampleSpace` + `ℱ : DecidableFiltration Ω` という「離散フィルトレーションの上の停止時間」をかなり素直に定義できています。
* `adapted` 条件は、まさに停止時間の定義そのもの（`{τ ≤ t}` が層 `t` の代数に属する）になっていて、Phase 3 での構造塔フィルトレーションとの接続もそのまま読める形になっています。

### 順序と定数停止時間

* `LE (ComputableStoppingTime ℱ)` を「点ごとの ≤」で入れているのは自然で、この後「有界停止時間」「sup/inf」などを入れる下地として良いと思います。
* `const` の定義と、その adapted 証明も有限代数の `has_univ` / `has_empty` をきちんと使っていて、
  「`t < c` で空集合、`t ≥ c` で全体集合」という停止時間の直感とも合っています。

### min / max の停止時間演算

```lean
def min (τ₁ τ₂ : ComputableStoppingTime ℱ) : ComputableStoppingTime ℱ := ...
def max (τ₁ τ₂ : ComputableStoppingTime ℱ) : ComputableStoppingTime ℱ := ...
```

* `{min τ₁ τ₂ ≤ t} = {τ₁ ≤ t} ∪ {τ₂ ≤ t}`
  `{max τ₁ τ₂ ≤ t} = {τ₁ ≤ t} ∩ {τ₂ ≤ t}`
  を `Set.ext` で手で書いているので、`classical` に頼らずに閉包性からそのまま adapted を証明できています。
* その上で `min_le_left`, `min_le_right`, `le_max_left`, `le_max_right`、そして `min_isBounded`, `max_isBounded` が揃っているので、
  後続の OST の statement を書くときに「有界停止時間のクラス」がすぐ使える形になっています。

### コイン投げの Examples

```lean
def coinSpace : Prob.FiniteSampleSpace := ...
def coinFullAlgebra : Prob.FiniteAlgebra coinSpace.carrier :=
  Prob.FiniteAlgebra.powerSet
def coinFullFiltration : DecidableFiltration coinSpace :=
  constFiltration coinSpace coinFullAlgebra 3
```

* 標本空間 `Bool` + 代数 `powerSet` + フィルトレーション `constFiltration` という一番シンプルな例がきちんと閉じています。
* `coinConst1` / `coinHeadTail` / `coinMin` / `coinMax` それぞれについて `#eval` を出しているので、
  「停止時間は本当に `Ω → ℕ` の計算可能な写像として動いている」ことを学生に示しやすい構成になっています。

`coinHeadTail` の `adapted` も、いまの形なら十分です：

```lean
def coinHeadTail : ComputableStoppingTime coinFullFiltration where
  time := fun b => match b with | true => 0 | false => 1
  adapted := by
    intro t ht
    -- powerSet 上では任意の部分集合が可観測
    simp [coinFullFiltration, coinFullAlgebra, constFiltration,
      Prob.FiniteAlgebra.powerSet]
```

* `powerSet` で events = 全事象、という設計になっていれば `simp` 一発で済むので、examples らしい軽さになっています。
* もし将来的に「example も含めて classical 依存を減らしたい」という方針を取るなら、ここだけ `change ...; exact Set.mem_univ _` に差し替える、という選択肢も残せます。

---

## 2. 「構造塔との対応」を明示するなら

Phase 3 との橋渡しとして、「minLayer との対応」を少し補強するなら、例えば以下のような補助定義を入れておくと、後で論文テキストやコメントから参照しやすくなります。

```lean
namespace ComputableStoppingTime

/-- 停止時間 `τ` に対して `{τ ≤ t}` という stopping event を明示的に名前付けしておく。 -/
def stoppingEvent_le (τ : ComputableStoppingTime ℱ)
    (t : ℕ) (ht : t ≤ ℱ.timeHorizon) : Prob.Event Ω.carrier :=
  ⟨{ω : Ω.carrier | τ.time ω ≤ t}, τ.adapted t ht⟩

/-- 構造塔側の minLayer の視点から見ると、`{τ ≤ t}` の `minLayer` は常に `≤ t`。 -/
lemma minLayer_stoppingEvent_le_le
    (τ : ComputableStoppingTime ℱ)
    (t : ℕ) (ht : t ≤ ℱ.timeHorizon) :
    ℱ.minLayer (stoppingEvent_le τ t ht) ≤ t := sorry
  -- Phase 3 で `DecidableFiltration` を `StructureTowerWithMin` にしたときの一般定理として
  -- 別ファイルで証明してもよい。
```

* こういう「`stoppingEvent_le` の minLayer は常に ≤ t」という形の補題を用意しておくと、

  * 構造塔理論の側では「`minLayer` を使った停止時間の定義」
  * 確率側では「`{τ ≤ t}` の adapted 条件」
    が同じものを見ている、という説明がしやすくなります。

（もちろん、これは次のフェーズで StructureTowerWithMin と接続するときに別ファイルでやっても構いません）

---

## 3. 小さなリファクタ候補（任意）

すでにビルドも通っていてきれいなので、以下は「もし触るなら」レベルです。

1. **`@[simp]` マーク**

   * `min_le_left`, `min_le_right`, `le_max_left`, `le_max_right` あたりは `@[simp]` を付けておくと、
     後で stopping time の大小関係を整理する際に自然に使われやすくなります。

2. **`isBounded` のバリエーション**

   * `isBounded τ N` を「∃ N, …」型の `isBounded` に抽象化するか、
     あるいは「ある停止時間 τ が timeHorizon 以下で自明に有界」という補題を一つ追加する、といった方向性もあります。
   * OST を書くときに「`τ` は `timeHorizon` 以下」という条件を頻繁に使うなら、専用の lemma があると便利です。

3. **Examples セクションの用途コメント**

   * すでにドキュメントは充実していますが、Examples の冒頭に

     > 「ここから下は“教育用サンプル”であり、理論本体には依存しない」
     > といった短いコメントを入れておくと、将来ファイルを読んだときに「理論コア」と「教材パート」の切り分けがより明確になります。

---

## 4. 次のステップ案（Phase 5 へ向けて）

この Phase 4 ファイルは、「停止時間というオブジェクトの層」として十分に完成度が高いので、次は：

* `M : ℕ → Ω.carrier → ℚ` を「離散マルチンゲール」とするための adapted 条件
* 有限和で書ける期待値 `E[M n]` を `FiniteSampleSpace` 上のテーブル積分として実装
* 「有界停止時間 τ について `E[M_0] = E[M_τ]`」という OST の statement（証明は段階的に）

といった Phase 5 に自然に進める状態になっています。

特に、

* `isBounded τ N` と
* `FiniteSampleSpace` の有限性

から、「期待値 `E[M τ]` も有限和として書ける」ことを explicit にコードに落とし込めるので、
Phase 5 の設計もかなりやりやすくなっていると思います。

---

総評として、この `ComputableStoppingTime.lean` は Phase 4 の役割（「情報＋時刻」の構造としての停止時間層）を十分に満たしていて、
このまま Phase 5 に進んで大丈夫な水準だと思います。

もし「次はこういう方向で Martingale/OST を積み上げたい」というイメージがあれば、そのスケルトンもこちら側で用意できます。
