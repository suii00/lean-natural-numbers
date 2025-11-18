いきなり「オプショナル停止」「ドゥーブの定理」まで全部やろうとすると確実にパンクするので、段階をかなり細かく切った方が楽です。
今アップロードされている 3 ファイルの状態から逆算すると、だいたい次の順番が筋が良いと思います。

---

## 0. 今どこまで来ているかの整理

ざっくり見ると：

* `SigmaAlgebraTower_Skeleton.lean`

  * σ-代数の構造塔（`StructureTower`）＋ `NatFiltration` 相当はほぼ完成。
  * 「どの時刻で初めて可測になるか」という `minLayer` 周りも揃っている。

* `StoppingTime_MinLayer.lean`

  * `Filtration` と `towerOf` の橋渡し。
  * `StoppingTime` / `StoppedSigmaAlgebra` / `stoppedFiltrationCore` / `StoppedProcess` など、
    「停止時間と停止過程」のパスワイズな API はかなり充実している。

* `Martingale_StructureTower.lean`

  * `SigmaAlgebraFiltration`，`ConditionalExpectationTower`，`Martingale` 構造体，
    オプショナル停止・ドゥーブの定理などが「構想レベル」で docstring と `sorry` になっている。
  * 特に `MeasureClass`／`MeasurableFunctionTower` 周りは設計が重くて、ここから埋めるのは負荷が高い。

つまり「フィルトレーションと停止時間の構造塔的な足場」はできていて、
「条件付き期待値とマーチンゲール」をどう Lean に落とすかで止まっている、という状態です。

---

## 1. 最初のターゲットをぐっと絞る

まずは scope をかなり狭く設定してしまうのがおすすめです。

**ターゲット（第 1 目標）**

* 離散時間（添字は ℕ）
* 実数値過程 `X : ℕ → Ω → ℝ`
* 固定された確率測度 `μ : Measure Ω`（`[IsProbabilityMeasure μ]`）
* フィルトレーション `ℱ : Filtration Ω`（あるいはあなたの `SigmaAlgebraFiltration`）

この設定で、

1. 「マーチンゲール」の定義を Lean 上で一度“正しく”書く
2. ごく基本的な例と閉性（定数過程、和・スカラー倍、有限線形結合など）を証明する

ここまでを **第 1 ゴール** にするのが現実的です。
オプショナル停止やドゥーブは、その次のフェーズに回してしまってよいです。

---

## 2. 条件付き期待値を自作しない方針に切り替える

`Martingale_StructureTower.lean` では

* `MeasureClass`
* `MeasurableFunctionTower`
* `ConditionalExpectationTower`

などを「構造塔としての条件付き期待値」から一気に設計しようとしていますが、
ここから埋めていくのはかなりしんどいです。

**方針転換案：**

* 条件付き期待値そのものは **mathlib の `condexp` / `condexpL1` を丸ごと借りる**。
* あなたの役目はそれを「構造塔の言葉で言い換えるラッパー」を書くところまでにする。

イメージとしては：

```lean
namespace StructureTowerProbability
open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω)

/-- ここでは Filtration は mathlib のものをそのまま使う方が楽。 -/
abbrev Filtration (Ω : Type*) :=
  MeasureTheory.Filtration Ω

/-- 離散時間実数値過程の別名。 -/
abbrev Process (Ω : Type*) :=
  ℕ → Ω → ℝ

/-- `condExp n f` を「𝓕 n による条件付き期待値」としてラップする。 -/
def condExp (ℱ : Filtration Ω) (n : ℕ) (f : Ω → ℝ) : Ω → ℝ :=
  -- 実際には `MeasureTheory.condexp μ (ℱ n) f` などの形になる
  sorry
```

型の細部は mathlib に合わせて調整が必要ですが、
**自分で条件付き期待値を定義・証明するのではなく、mathlib の API を “構造塔の言葉で包み直す”** という位置づけにするだけで、難易度がかなり下がります。

---

## 3. マーチンゲールの定義だけを先に固める

次に、「マーチンゲールとは何か」を Lean で一度きちんと書いてみるフェーズです。

今の `Martingale` は

```lean
structure Martingale where
  filtration : SigmaAlgebraFiltration (Ω := Ω)
  X : ℕ → Ω → ℝ
  adapted : ...
  integrable : ...
  martingale_property : ∀ n, True  -- TODO
```

となっていますが、ここを「ちょっと無理してでも数学的に正しい形」に寄せてしまうと、その後の設計がずっと楽になります。

例えばイメージとしては：

```lean
structure Martingale
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] where
  filtration : Filtration Ω
  X : ℕ → Ω → ℝ
  adapted :
    ∀ n, AEStronglyMeasurable (X n) (filtration.𝓕 n)
  integrable :
    ∀ n, Integrable (X n) μ
  martingale_property :
    ∀ n,
      condExp μ filtration n (X (n+1))
        =ᵐ[μ] X n
```

* ここでの `condExp μ filtration n` は、前項で用意したラッパー。
* `=ᵐ[μ]` は a.e. での等号。
* 実際の mathlib の API に合わせて多少書き換えが必要ですが、**狙いはこの形**です。

この「定義のために必要な最小限の lemma」（`condExp` が 𝓕ₙ 可測になる、積分が一致するなど）は全部 mathlib 側に既にあるので、それを `open MeasureTheory` して使うだけ、という形を目指します。

---

## 4. 既にある「停止過程 API」をマーチンゲールに繋げる

`StoppingTime_MinLayer.lean` では、

* `StoppedProcess`
* `stopped_eq_of_le`
* `eq_before_stopping`
* `const_after_stopping`

など、**純粋にパスワイズなレベル**の補題がかなり整っています。

マーチンゲールに進むための、次の具体的なステップは：

1. `Martingale` を使って
   「定数過程はマーチンゲール」「和・スカラー倍はマーチンゲール」を証明する。
2. その次に、`StoppedProcess` に測度・期待値の構造を載せて、

   * `M` がマーチンゲール
   * `τ` が有限停止時間
     のときに、`(ω ↦ M (τ ω) ω)` が「ある意味でよい性質を持つ」ことを示す準備をする
     （最初は optional stopping の主張まで行かなくてよいので、期待値の評価式の“途中まで”をいくつか lemma 化するレベルで十分です）。

ここで大切なのは、

* いきなり「オプショナル停止定理（bounded / general）」の最終形を証明しようとしない。
* 代わりに、「停止過程を定義したのだから、マーチンゲールと組み合わせると何が言えそうか」を小さな補題に分解していく。

という進め方です。

---

## 5. 当面の「やることリスト」

まとめると、今のファイル群から **マーチンゲールに進むときの具体的な順番**は：

1. `Martingale_StructureTower.lean` から

   * `MeasureClass` / `MeasurableFunctionTower` は一旦脇に置く（コメントアウトしてしまってもよい）。
   * `SigmaAlgebraFiltration` と `Martingale` の定義だけを残す（あるいは mathlib の `Filtration` に置き換える）。

2. mathlib の条件付き期待値をラップする

   * `condExp (ℱ : Filtration Ω) (n : ℕ) (f : Ω → ℝ)` を、`condexp μ (ℱ.𝓕 n) f` 的なものとして定義。
   * 「塔の性質」（`condExp m (condExp n f) = condExp m f`）など、本当に必要な性質だけを lemma としてまとめる。
     → これは `ConditionalExpectationTower` の最小バージョンとして実装する。

3. `Martingale` 構造体を「正しい」形に書き直す

   * `martingale_property : ∀ n, condExp μ ℱ n (X (n+1)) =ᵐ[μ] X n`
   * `adapted` と `integrable` も mathlib 風に整理する。

4. 基本例と閉性を証明する

   * 定数過程
   * 和
   * スカラー倍
   * 有限線形結合（余力があれば）

5. その上で、`StoppingTime_MinLayer.lean` の `StoppedProcess` を `Martingale` と接続する補題を少しずつ追加する
   （optional stopping 本体は「第 2 目標」として後回し）。

---

この順番で進めると、

* 「構造塔としての綺麗なストーリー」は壊さずに、
* 実際に動く `Martingale` の定義と小さな定理が 1 つのファイルにまとまる

ところまで、比較的ストレス少なめに到達できると思います。

必要であれば、次は「mathlib の `condexp` をどうラップすると良いか」を、もう少し型レベルまで踏み込んで一緒に設計できます。
