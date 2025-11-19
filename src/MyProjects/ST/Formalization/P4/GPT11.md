「長すぎてムリ」は本当にそうで、あの一本の `def` に全部詰め込むのは人間のメモリにはつらいです…。
幸い、今 `kabe.txt` に書いてある実装は、きれいに「３つの役割」に分解できます。

やることはシンプルで：

1. `adapted` 用の補題
2. `integrable` 用の補題
3. `martingale`（condExp_next）用の補題

に切り出してから、最後の `noncomputable def` はそれらを組み合わせるだけにします。

以下、「ほぼそのままコピペで差し替えられる形」のリファクタリング案を書きます。

---

## 1. 適合性（adapted）の補題に切り出す

`kabe.txt` だと `h_stop_strong` を `have` で定義して、その場で `simpa` しています。
これをそのまま lemma に昇格させます。

```lean
namespace StructureTowerProbability
open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

namespace Martingale

/-- 停止集合 {τ ≤ n} が可測であれば、停止過程は各時刻で StronglyMeasurable。 -/
lemma stoppedProcess_stronglyMeasurable_of_stoppingSets
    (M : Martingale μ)
    (τ : Ω → ℕ)
    (hτ :
      ∀ n, @MeasurableSet Ω (M.filtration n) {ω : Ω | τ ω ≤ n}) :
  ∀ n,
    StronglyMeasurable[M.filtration n]
      (M.stoppedProcess τ n) := by
  classical
  -- P3 の bridge lemma そのまま利用
  have h_stop_strong :
    ∀ n,
      StronglyMeasurable[M.filtration n]
        (StructureTowerProbability.stopped M.process τ n) :=
    StructureTowerProbability.stopped_stronglyMeasurable_of_stoppingSets
      (ℱ := M.filtration) (X := M.process)
      (hX := M.adapted) (τ := τ) (hτ := hτ)
  intro n
  -- stoppedProcess が P3 の stopped のラッパであることを使って書き換え
  simpa [Martingale.stoppedProcess] using h_stop_strong n
```

これで `adapted` フィールドは

```lean
adapted := M.stoppedProcess_stronglyMeasurable_of_stoppingSets τ hτ
```

と一行で済みます。

---

## 2. 可積分性（integrable）の補題に切り出す

同じく `h_stop_int` を lemma にします。

```lean
/-- 有界停止時間のもとで、停止過程は各時刻で Integrable。 -/
lemma stoppedProcess_integrable_of_bdd
    (M : Martingale μ)
    (τ : Ω → ℕ)
    (hτ :
      ∀ n, @MeasurableSet Ω (M.filtration n) {ω : Ω | τ ω ≤ n})
    (hτ_bdd : ∃ K, ∀ ω, τ ω ≤ K) :
  ∀ n, Integrable (M.stoppedProcess τ n) μ := by
  classical
  have h_stop_int :
    ∀ n,
      Integrable
        (StructureTowerProbability.stopped M.process τ n) μ :=
    StructureTowerProbability.stopped_integrable_of_bdd
      (ℱ := M.filtration) (X := M.process)
      (hX := M.integrable) (τ := τ)
      (hτ := hτ) (hτ_bdd := hτ_bdd)
  intro n
  simpa [Martingale.stoppedProcess] using h_stop_int n
```

`integrable` フィールドは

```lean
integrable := M.stoppedProcess_integrable_of_bdd τ hτ hτ_bdd
```

で埋まります。

---

## 3. マルチンゲール性（condExp_next / martingale）の補題に切り出す

一番長い「optional stopping 本体」の部分も lemma に逃がします。

kabe.txt の `martingale := ?_` ブロックをほぼそのまま lemma に移植してしまって構いません：

```lean
/-- 有界停止時間で止めた過程がマルチンゲール性を満たすこと（本体）。 -/
lemma stoppedProcess_martingaleProperty_of_bdd
    (M : Martingale μ)
    (τ : Ω → ℕ)
    (hτ :
      ∀ n, @MeasurableSet Ω (M.filtration n) {ω : Ω | τ ω ≤ n})
    (hτ_bdd : ∃ K, ∀ ω, τ ω ≤ K) :
  ∀ n,
    condExp μ M.filtration n
      (M.stoppedProcess τ (n + 1)) =ᵐ[μ]
    M.stoppedProcess τ n := by
  classical
  -- ここに kabe.txt で `martingale := ?_` の中に書いていた証明を
  -- ほぼそのまま移植します。
  --
  -- 具体的には：
  --   * h_stop_strong, h_stop_int をこの lemma 内で `have` として再定義
  --   * 以降の `h_stop_int_n` 〜 `h_rhs` までの流れをそのまま貼る
  --
  intro n
  -- kabe.txt の該当部分を開始
  have h_stop_strong :
    ∀ m,
      StronglyMeasurable[M.filtration m]
        (M.stoppedProcess τ m) :=
    M.stoppedProcess_stronglyMeasurable_of_stoppingSets τ hτ
  have h_stop_int :
    ∀ m, Integrable (M.stoppedProcess τ m) μ :=
    M.stoppedProcess_integrable_of_bdd τ hτ hτ_bdd

  -- 以下、kabe.txt の `martingale :=` ブロックを、
  -- 外側の `intro n` に合わせて少し書き換えて埋めれば OK
  -- （ほぼコピペで通るはずです）
  classical
  have h_stop_int_n := h_stop_int n
  have h_stop_int_succ := h_stop_int (n + 1)
  have h_diff_int :
      Integrable
        (fun ω =>
          M.stoppedProcess τ (n + 1) ω - M.stoppedProcess τ n ω) μ :=
    h_stop_int_succ.sub h_stop_int_n
  ...
  -- 最後に `condExp μ ... (M.stoppedProcess τ (n+1)) =ᵐ M.stoppedProcess τ n`
  -- を `exact` するところまで、kabe.txt のコードを移植
  sorry  -- ← いまの kabe.txt の証明をここに貼れば `sorry` が消えます
```

ポイントは：

* 今まで `def` の中にあった長い証明を、この lemma にまるごと移す。
* その際、先ほど作った `stoppedProcess_stronglyMeasurable_of_stoppingSets` / `stoppedProcess_integrable_of_bdd` を `have` で再利用すれば、`h_stop_strong` / `h_stop_int` もすっきり書けます。

---

## 4. 最後の `noncomputable def` は「短いまとめ役」にする

ここまでできれば、`noncomputable def` 自体はとても短くできます：

```lean
/-- 有界停止時間で止めたマルチンゲールは再びマルチンゲールになる。 -/
noncomputable def stoppedProcess_martingale_of_bdd
    (M : Martingale μ)
    (τ : Ω → ℕ)
    (hτ :
      ∀ n, @MeasurableSet Ω (M.filtration n) {ω : Ω | τ ω ≤ n})
    (hτ_bdd : ∃ K, ∀ ω, τ ω ≤ K) :
  Martingale μ :=
by
  classical
  refine
    { filtration := M.filtration
      , process    := M.stoppedProcess τ
      , adapted    := M.stoppedProcess_stronglyMeasurable_of_stoppingSets τ hτ
      , integrable := M.stoppedProcess_integrable_of_bdd τ hτ hτ_bdd
      , martingale := M.stoppedProcess_martingaleProperty_of_bdd τ hτ hτ_bdd }
```

これなら `def` 本体はほぼ「配線」だけで、実装の難しい部分はすべて lemma 側に隔離されます。

---

## 5. どう進めるか

* まずは「adapted 用」「integrable 用」の 2 本だけ lemma 化して、`def` を短くする。
* そのあと、一番長い `martingale` 部分も `stoppedProcess_martingaleProperty_of_bdd` に切り出していく。
* 途中でエラーが出ても、その lemma 一本だけを相手にすればよいので、VSCode の InfoView がだいぶ読みやすくなります。

もし、`stoppedProcess_martingaleProperty_of_bdd` に kabe.txt の証明を貼る途中で具体的なエラーが出たら、その lemma 部分だけ貼ってくれれば、そこで一緒に「ここは `simp` で落とせる」「ここは補題を 1 行足したほうがいい」といった調整をします。
