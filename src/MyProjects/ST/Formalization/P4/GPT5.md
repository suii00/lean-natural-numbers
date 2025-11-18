いいですね、ここまでで「P4 は mathlib 流儀の最小マルチンゲール API＋線形構造」というところまできれいにまとまっています。

書いてくださった「次にやる 3 本柱」は、そのまま採用で問題ないと思いますが、少しだけ型・命名レベルで補足しておきます。

---

## 1. Martingale の薄いラッパ補題

方針はそのままで良いです。実装イメージはこんな感じになりそうです：

```lean
namespace Martingale

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- 時刻 n での可積分性を取り出す薄いラッパ。 -/
lemma integrable_n (M : Martingale μ) (n : ℕ) :
  Integrable (M.process n) μ :=
  M.integrable n

/-- 時刻 n での適合性（強可測性）を取り出す薄いラッパ。 -/
lemma adapted_stronglyMeasurable (M : Martingale μ) (n : ℕ) :
  StronglyMeasurable (M.process n) (M.filtration n) :=
  M.adapted n
-- ↑ `Adapted` のフィールド型に合わせて `StronglyMeasurable` / `AEStronglyMeasurable`
--    など、実際の定義に揃えてください。

end Martingale
```

* `StronglyMeasurable[ℱ n]` の部分は、実際に `Adapted` のフィールドが何を返しているか次第で調整（`StronglyMeasurable` なのか `AEStronglyMeasurable` なのか）。
* 命名は `integrable_n`・`aestronglyMeasurable_n` のように揃えてもよいです。

いずれにせよ、「構造体フィールドを pattern match せずに取れるラッパを 2 本追加する」という方向性はそのまま GO で良いです。

---

## 2. const / add / smul の “lemma 形” ラッパ

ここも書いてくださった通りで、`def` を素直にラップする lemma を用意しておくと後段のファイルから使いやすくなります。

イメージ：

```lean
namespace Martingale

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- 任意フィルトレーション上の定数過程はマルチンゲール。 -/
lemma const_isMartingale (ℱ : Filtration Ω) (c : ℝ) :
  Martingale μ (Martingale.const μ ℱ c) :=
  -- `const` が構造体コンストラクタを包んでいるだけなら `rfl` ベースで終わるはず
  rfl

@[simp] lemma const_filtration (ℱ : Filtration Ω) (c : ℝ) :
  (Martingale.const μ ℱ c).filtration = ℱ := rfl

-- add/smul については既に `@[simp] lemma add_filtration ... := rfl`
-- `@[simp] lemma smul_filtration ... := rfl` を入れてあるとのことなので、
-- const も同様の形で揃えると気持ちよくなります。

end Martingale
```

ポイントは、

* 「`def` から構造体フィールドを取り出すだけ」の lemma は、`rfl` で済む範囲はできるだけ `rfl` にする。
* `@[simp]` を付けておくと、後で `simp` がフィルトレーション成分の等号を自動で処理してくれる。

すでに `add_filtration` / `smul_filtration` を `@[simp]` 済みなら、`const_filtration` も同列に置いて 3 本ワンセットにしておくときれいです。

---

## 3. P3 側との橋としての `Martingale.stoppedProcess`

ここもコンセプトはそのままで、**P3 の `StoppedProcess` の API にきちんと乗る**ことだけ意識しておけば十分です。

例えば P3 に

```lean
structure StoppedProcess (X : Process Ω) (τ : StoppingTime ℱ) :=
  (process : Process Ω)
  -- …
```

のようなものがあるなら、それに倣って：

```lean
namespace Martingale

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- マルチンゲール M を停止時間 τ で止めた過程。 -/
def stoppedProcess (M : Martingale μ)
    (τ : StoppingTime M.filtration) :
    Process Ω :=
  -- P3 側の StoppedProcess API に合わせて実装
  fun n ω => (StoppedProcess.ofProcess M.process τ).process n ω

end Martingale
```

のように、

* フィルトレーション引数はきちんと `M.filtration` に揃える
* 「P3 の `StoppedProcess`（パスワイズな世界）」 → 「P4 の `Process`（期待値・条件付き期待値の世界）」へ写すだけ

という薄いラッパにしておくのが良いです。

`StoppableProcess` という名前が混じっていましたが、ファイル名からすると実体は `StoppedProcess` だと思うので、その API に寄せていくイメージですね。

---

## 4. Optional stopping への備えとして

ここまでの 3 本が入れば、

* 「適合性・可積分性・condExp_next」を一発で引き出すラッパ群
* 「定数＋線形性」の基本例・閉性
* 「停止過程」とマルチンゲールを結ぶ型レベルの橋

が揃うので、有界停止時間に限定した optional stopping（あるいは「期待値が一定に保たれる」程度の弱い形）から入りやすくなります。

そのタイミングで、

* `condExp_add` / `condExp_smul`（ラッパ）の整理
* `Process.add` / `Process.smul` 対応の「a.e. 等号を add/smul できる」補題

を必要に応じて足していけば、P4 全体が「mathlib の Martingale まわり＋構造塔的拡張」の、かなり使い勝手の良いレイヤーになっていくと思います。

このあと実際に `Martingale.stoppedProcess` の型を決めてみたところで、「どのレベルの optional stopping から攻めるか」を一緒に詰めてもよいですね。
