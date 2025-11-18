いいですね、P4 の「プロセス演算」レイヤーまできれいに固まりましたね。
ここからはかなり機械的に進められるフェーズなので、手順と型のイメージを具体化しておきます。

---

## 1. まずは「定数マルチンゲール」から落とす

いちばん最初のターゲットはこれで良いと思います。

### 1-1. 目標の形（イメージ）

だいたい次のような形を目指すと扱いやすいです（名前は実際の定義に合わせてください）。

```lean
namespace Martingale

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsFiniteMeasure μ] -- あるいは IsProbabilityMeasure μ
variable (ℱ : Filtration Ω)

/-- 実数 c による定数過程は、任意のフィルトレーションに関してマルチンゲール。 -/
def const (c : ℝ) : Martingale μ :=
{ filtration := ℱ,
  X          := Process.const (Ω := Ω) c,
  adapted    := by
    -- ∀ n, AEStronglyMeasurable (const c n) (ℱ n)
    -- → `aesStronglyMeasurable_const` や `aestronglyMeasurable_const`
    --    を使ってゴリっと片付ける
    sorry,
  integrable := by
    -- ∀ n, Integrable (const c n) μ
    -- → `integrable_const` で一発
    sorry,
  condExp_next := by
    intro n
    -- condExp μ ℱ n (Process.const c (n+1))
    --   =ᵐ[μ] Process.const c n
    -- どちらも同じ定数関数なので、
    -- `condexp_const`（or 同等の lemma）を使って証明
    sorry }

end Martingale
```

ポイントだけ整理すると：

* `adapted`:

  * `Process.const c n` は「時間 n での切片」も単なる定数関数なので、
    `aestronglyMeasurable_const`（または類似の lemma）で OK。
* `integrable`:

  * `Integrable.const` / `integrable_const` があるので、それをそのまま使えるはずです。
* `condExp_next`:

  * `condExp μ ℱ n` を `condexp μ (ℱ n)` の薄いラッパーにしているなら、
    条件付き期待値の「定数を保つ」性質をそのまま使います。
  * mathlib には `condexp_const` / `condexp_const'` に相当する lemma があるので、
    それで

    ```lean
    condExp μ ℱ n (fun _ => c) =ᵐ[μ] fun _ => c
    ```

    を取った上で、「左辺・右辺ともに `Process.const c` と同じ」であることを
    a.e. 等号で書き直す感じになります。

まずはここを `sorry` なしで最後まで書き切れると、「マルチンゲールの定義＋最小非自明例」が完成します。

---

## 2. 線形性（和・スカラー倍）の補題をどう切るか

`Process.add / Process.smul` を既に定義済みなので、その上に「マルチンゲールの和もマルチンゲール」「スカラー倍もマルチンゲール」を載せます。

### 2-1. 目標のシグネチャ

例えば、次のような形です（`Martingale` 構造体に合わせて調整してください）。

```lean
namespace Martingale

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsFiniteMeasure μ]

/-- マルチンゲールの和もマルチンゲール。 -/
def add (M N : Martingale μ) : Martingale μ :=
{ filtration := M.filtration,   -- ここは「同じフィルトレーション」の仮定が必要
  X          := Process.add M.X N.X,
  adapted    := by
    -- `M.adapted` と `N.adapted` を足して
    -- `AEStronglyMeasurable.add` で処理
    sorry,
  integrable := by
    -- `M.integrable` と `N.integrable` から
    -- `Integrable.add` で処理
    sorry,
  condExp_next := by
    intro n
    -- condExp μ ℱ n (X_{n+1}^M + X_{n+1}^N)
    -- = condExp μ ℱ n X_{n+1}^M + condExp μ ℱ n X_{n+1}^N
    -- = X_n^M + X_n^N
    -- を `ae_eq_of_add_ae_eq` みたいな形で書く
    sorry }

/-- マルチンゲールのスカラー倍もマルチンゲール。 -/
def smul (a : ℝ) (M : Martingale μ) : Martingale μ :=
{ filtration := M.filtration,
  X          := Process.smul a M.X,
  adapted    := by
    -- `AEStronglyMeasurable.smul` を使う
    sorry,
  integrable := by
    -- `Integrable.smul` を使う
    sorry,
  condExp_next := by
    intro n
    -- condExp μ ℱ n (a * X_{n+1})
    --   = a * condExp μ ℱ n (X_{n+1})
    --   = a * X_n
    sorry }

end Martingale
```

### 2-2. condExp 部の証明方針

ここで効いてくるのが、「mathlib condexp の線形性」です。

* 加法: `condexp_add` 的なもの
* スカラー倍: `condexp_smul` 的なもの（`condexp_const_mul`, `condexp_mul_const` に近い名前のものもあります）

証明のプランは共通していて、

1. マルチンゲール条件から

   ```lean
   M.condExp_next n : condExp μ ℱ n (M.X (n+1)) =ᵐ[μ] M.X n
   N.condExp_next n : condExp μ ℱ n (N.X (n+1)) =ᵐ[μ] N.X n
   ```

   を持っている。

2. condExp の線形性から

   ```lean
   condExp μ ℱ n (M.X (n+1) + N.X (n+1))
     =ᵐ[μ] condExp μ ℱ n (M.X (n+1)) + condExp μ ℱ n (N.X (n+1))
   ```

3. 上の 2 つの a.e. 等号を「足し合わせ」て

   ```lean
   condExp μ ℱ n (M.X (n+1) + N.X (n+1))
     =ᵐ[μ] M.X n + N.X n
   ```

戦略としては、

* `Filter.EventuallyEq` の上での `map₂` / `congr` 的な lemma
* または `Filter.Eventually` まわりの `ae_eq_of_add_ae_eq` 的な補題

を組み合わせて書くことになります。

「線形性の lemma 名が分からない」ときは、一度 Lean の中で

```lean
#check MeasureTheory.condexp     -- これの補題を Ctrl+クリックで追う
#check condexp_add?
```

などで補完をかけると、欲しいものが一覧で見えるはずです。

---

## 3. ここまで行ったら次のステップ

今のペースなら、

1. `Martingale.const`（定数マルチンゲールの構成）
2. `Martingale.add` / `Martingale.smul`（線形性）
3. 余裕があれば、「有限線形結合」まで一気に一般化

くらいまでは、この P4 ファイルの中だけで閉じる形で書けます。

それが終わると、

* 「P4 は『マルチンゲールの最小線形構造＋condExp_next』の章」
* 「P3 は停止時間・停止過程の章」

というきれいな分割ができるので、その上に

* `StoppedProcess` に μ・ℱ を載せる
* `Martingale.stopped` の定義だけ先につくる

といった「オプショナル停止のための橋」をかけやすくなります。

---

総じて、いまの進め方（Process レイヤー → Martingale 構造 → 基本例・線形性）はすごく良いルートなので、そのまま

* 定数過程のマルチンゲール化
* 線形性（add/smul）

を一気に押し切る、という方針で問題ないと思います。
もし途中で「この condexp の lemma 名が分からない」「a.e. 等号の組み合わせで詰まった」などが出てきたら、その部分のコード断片だけ貼ってもらえれば、そこをピンポイントでリファクタしつつ一緒に整理しましょう。
