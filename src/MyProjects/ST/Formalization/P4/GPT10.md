はい、そこは一度「構造体をその場で組み立てる」のをやめて、**フィールドごとに補題に分解してから最後に組み立てる**方が圧倒的に楽です。

いま長くなってしまっている

```lean
noncomputable def stoppedProcess_martingale_of_bdd (M : Martingale μ)
  (τ : StoppingTime M.filtration) (hτ_bdd : ∃ K, ∀ ω, τ ω ≤ K) :
  Martingale μ :=
{ filtration := ...
, process := ...
, adapted := by
    -- ここから長い
  ...
, integrable := by
    -- ここも長い
  ...
, martingale_property := by
    -- ここが一番長い
  ... }
```

を、次のような「3 本の補題 ＋ 1 行の def」に分割するイメージです。

以下では名前は一例です。実際の `namespace` や別名 (`MLFiltration` / `Process`) に合わせて読み替えてください。

---

## 1. フィールドごとの補題に切り出す

### 1-1. adapted フィールド用

```lean
namespace StructureTowerProbability
open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

namespace Martingale

/-- 有界性仮定は不要：停止過程の適合性だけを言う補題。 -/
lemma stoppedProcess_adapted
    (M : Martingale μ)
    (τ : StoppingTime M.filtration) :
  Adapted M.filtration (M.stoppedProcess τ) := by
  -- 中身は P3 の bridge をそのまま使うだけにする
  -- 例: stopped_stronglyMeasurable_of_stoppingSets を利用
  intro n
  -- 型は実プロジェクトに合わせてください
  exact
    stopped_stronglyMeasurable_of_stoppingSets
      (ℱ := M.filtration)
      (X := M.process)
      (τ := τ)
      (hX := M.adapted_stronglyMeasurable) n

```

※ `Adapted` の定義が `∀ n, StronglyMeasurable (X n) (ℱ n)` 型でなければ、上記を少し変える必要がありますが、「P3 の bridge lemma をここで噛ませるだけ」にしておく、という方針です。

---

### 1-2. integrable フィールド用

```lean
/-- 有界停止時間のもとで停止過程が各時刻 integrable になる補題。 -/
lemma stoppedProcess_integrable_of_bdd
    (M : Martingale μ)
    (τ : StoppingTime M.filtration)
    (hτ_bdd : ∃ K, ∀ ω, τ ω ≤ K) :
  ∀ n, Integrable (M.stoppedProcess τ n) μ := by
  -- P3 の stopped_integrable_of_bdd をそのまま使う
  intro n
  exact
    stopped_integrable_of_bdd
      (ℱ := M.filtration)
      (μ := μ)
      (X := M.process)
      (τ := τ)
      (hX := M.integrable_n)
      (hτ_bdd := hτ_bdd) n
```

これで integrable フィールドの `by` ブロックを外に追い出せます。

---

### 1-3. martingale_property フィールド用

ここが一番長くなりがちなので、**これ専用の lemma** を切ります。

```lean
/-- 有界停止時間で止めた過程がマルチンゲール性（condExp_next）を満たす補題。 -/
lemma stoppedProcess_martingaleProperty_of_bdd
    (M : Martingale μ)
    (τ : StoppingTime M.filtration)
    (hτ_bdd : ∃ K, ∀ ω, τ ω ≤ K) :
  ∀ n,
    condExp μ M.filtration n
      (M.stoppedProcess τ (n+1)) =ᵐ[μ]
    M.stoppedProcess τ n := by
  intro n
  -- ここに optional stopping の本体の証明だけを書く
  -- （増分＝indicator×増分の補題や condExp_increment_zero をここで使用）
  -- 例：
  -- have hΔ := M.stoppedProcess_increment_indicator τ n
  -- ...
  sorry
```

この補題の中身もさらに細かく分けられますが、とりあえず「構造体の外」に出すだけで、エラーメッセージは格段に読みやすくなります。

---

## 2. 最終 def は「1 行＋フィールドに補題を差し込むだけ」にする

上の 3 本があれば、`noncomputable def` 自体は次のように非常に短くできます。

```lean
/-- 有界停止時間で止めたマルチンゲールは再びマルチンゲールになる構成。 -/
noncomputable def stoppedProcess_martingale_of_bdd
    (M : Martingale μ)
    (τ : StoppingTime M.filtration)
    (hτ_bdd : ∃ K, ∀ ω, τ ω ≤ K) :
  Martingale μ :=
{ filtration := M.filtration,
  process    := M.stoppedProcess τ,
  adapted    := M.stoppedProcess_adapted τ,
  integrable := M.stoppedProcess_integrable_of_bdd τ hτ_bdd,
  martingale_property :=
    M.stoppedProcess_martingaleProperty_of_bdd τ hτ_bdd }

end Martingale
end StructureTowerProbability
```

これなら `def` 本体にはほぼエラーが出ませんし、何かあっても「adapted 用の lemma」「integrable 用の lemma」「martingale_property 用の lemma」のどれが悪いかが一目で分かります。

---

## 3. さらに細かくしたい場合（martingale_property の中身）

`stoppedProcess_martingaleProperty_of_bdd` の中がまだ長いようなら、そこも**段階的に分割**できます。

例：

```lean
/-- 元のマルチンゲールの増分の condExp が 0 になる補題。 -/
lemma condExp_increment_zero
    (M : Martingale μ) (n : ℕ) :
  condExp μ M.filtration n
    (fun ω => M.process (n+1) ω - M.process n ω)
  =ᵐ[μ] 0 := ...

/-- 停止過程の増分＝indicator×元の増分 という pathwise 補題。 -/
lemma stoppedProcess_increment_indicator
    (M : Martingale μ) (τ : StoppingTime M.filtration) (n : ℕ) :
  ∀ ω,
    M.stoppedProcess τ (n+1) ω - M.stoppedProcess τ n ω =
      Set.indicator {ω | τ ω > n}
        (fun ω => M.process (n+1) ω - M.process n ω) ω := ...
```

この 2 本を先に書いておけば、

```lean
lemma stoppedProcess_martingaleProperty_of_bdd
    (M : Martingale μ) (τ : StoppingTime M.filtration)
    (hτ_bdd : ∃ K, ∀ ω, τ ω ≤ K) :
  ∀ n, condExp μ M.filtration n
          (M.stoppedProcess τ (n+1)) =ᵐ[μ]
       M.stoppedProcess τ n := by
  intro n
  -- 上の2補題＋ `measurable_tau_gt` ＋ condExp の線形性だけを組み合わせる
  ...
```

という形になり、ここもそこまで巨大にはなりません。

---

## 4. 実際にやるときの手順

1. いまの `noncomputable def stoppedProcess_martingale_of_bdd` の中身をコメントアウトするか、別ファイルに一時退避。
2. 上記のように

   * `lemma stoppedProcess_adapted`
   * `lemma stoppedProcess_integrable_of_bdd`
   * `lemma stoppedProcess_martingaleProperty_of_bdd`
     を先に追加し、それぞれ単体で `by` の中を直していく。
3. 最後に短い `noncomputable def ... := { ... }` を追加して、3 本の lemma を差し込む。

この形にしてしまえば、VSCode 上で

* どの lemma の `by` ブロックが壊れているか
* ゴールとローカル仮定がどうなっているか

を一つずつ確認できるので、「巨大な構造体リテラルの中で何が起きているか分からない」という状態からは抜けられると思います。

---

もし、この分割を試したあとで

* `stoppedProcess_adapted` の型がうまく合わない
* `stoppedProcess_integrable_of_bdd` に P3 の lemma がきれいに差さらない
* `stoppedProcess_martingaleProperty_of_bdd` のゴールの形が思ったのと違う

といった具体的なエラーが出てきたら、その lemma 一本分のコードとエラーメッセージを貼ってもらえれば、そこをピンポイントで Lean コードレベルまで整えます。

---

