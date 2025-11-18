今のところまでで、P4 側の土台はかなり整っているので、ここから一段階だけ「定理の形」まで持っていく案を具体化しておきます。

あなたが書いてくれた 3 本

* `stoppedProcess_eq_of_le`
* `stoppedProcess_const_of_ge`
* `stoppedProcess_eq_atStoppingTime`

で「停止前／停止後／十分後」の振る舞いがそろったので、次の 2 ステップを狙うときれいに噛み合います。

---

## 1. 増分＝指示関数×増分 という補題の skeleton

まずは pathwise な形で、停止過程の増分を元の増分と `{τ > n}` の指示関数で表現する補題です。

名前・型のイメージはこんな感じでどうでしょう（細部は手元の定義に合わせて調整してください）:

```lean
namespace StructureTowerProbability

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- 停止過程の増分を、もとの増分と {τ > n} の指示関数で書き下す。 -/
lemma Martingale.stoppedProcess_increment_indicator
    (M : Martingale μ) (τ : StoppingTime M.filtration) (n : ℕ) :
  ∀ ω,
    M.stoppedProcess τ (n+1) ω - M.stoppedProcess τ n ω =
      Set.indicator {ω | τ ω > n}
        (fun ω => M.process (n+1) ω - M.process n ω) ω :=
by
  intro ω
  by_cases h : τ ω ≤ n
  · -- ケース1: τ ω ≤ n → すでに停止済み
    -- 左辺は `stoppedProcess_const_of_ge` から 0
    have h₁ : M.stoppedProcess τ (n+1) ω
              = M.stoppedProcess τ (τ ω) ω :=
      M.stoppedProcess_const_of_ge τ (n := n+1) ?_
    have h₂ : M.stoppedProcess τ n ω
              = M.stoppedProcess τ (τ ω) ω :=
      M.stoppedProcess_const_of_ge τ (n := n) h
    -- ここで h から `τ ω ≤ n` を使って n+1 側にも適用できるようにする
    -- 左辺は差が 0
    have : M.stoppedProcess τ (n+1) ω - M.stoppedProcess τ n ω = 0 := by
      -- h₁, h₂ を使って書き換え
      sorry
    -- 右辺は `τ ω > n` が false なので indicator が 0
    have : Set.indicator {ω | τ ω > n}
              (fun ω => M.process (n+1) ω - M.process n ω) ω = 0 := by
      have : ¬ τ ω > n := by exact not_lt_of_ge h
      -- `Set.indicator_of_not_mem` で 0 に落とす
      sorry
    -- 両辺 0 で一致
    sorry
  · -- ケース2: τ ω > n → まだ停止していない
    have hlt : n < τ ω := lt_of_not_ge h
    -- `n+1 ≤ τ ω` も必要なら `Nat.succ_le_of_lt hlt`
    have h₁ : M.stoppedProcess τ (n+1) ω = M.process (n+1) ω :=
      M.stoppedProcess_eq_of_le τ (n := n+1) ?_
    have h₂ : M.stoppedProcess τ n ω = M.process n ω :=
      M.stoppedProcess_eq_of_le τ (n := n) (le_of_lt hlt)
    -- 左辺を書き換える
    have : M.stoppedProcess τ (n+1) ω - M.stoppedProcess τ n ω =
           M.process (n+1) ω - M.process n ω := by
      simp [h₁, h₂]
    -- 右辺の indicator はこのケースでは 1 倍
    have : Set.indicator {ω | τ ω > n}
              (fun ω => M.process (n+1) ω - M.process n ω) ω =
           M.process (n+1) ω - M.process n ω := by
      -- `hlt : τ ω > n` から `ω ∈ {ω | τ ω > n}` が分かるので
      -- `Set.indicator_of_mem` を使う
      sorry
    -- まとめて等号
    sorry

end StructureTowerProbability
```

ここはあくまで「証明の骨組み」なので、実際には

* `stoppedProcess_const_of_ge` / `stoppedProcess_eq_of_le` の正確な引数順
* `Set.indicator_of_not_mem` / `Set.indicator_of_mem` まわりの名前

を手元の環境に合わせて埋めていく感じになります。

この補題は optional stopping のときに

* `condExp` の線形性 (`condExp_add` / `condExp_smul`)
* マルチンゲールの「増分の条件付き期待値が 0 になる」性質

を組み合わせる際の「橋」として効いてきます。

---

## 2. 有界停止時間版の「止めた過程もマルチンゲール」定理 skeleton

上の補題があると、最初の optional stopping に相当するターゲットを次のように切ることができます。

```lean
namespace StructureTowerProbability

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- 有界停止時間で止めたマルチンゲールは、再びマルチンゲールになる（骨格）。 -/
theorem Martingale.stoppedProcess_martingale_of_bdd
    (M : Martingale μ)
    (τ : StoppingTime M.filtration)
    (hτ_bdd : ∃ K, ∀ ω, τ ω ≤ K) :
  Martingale μ (M.stoppedProcess τ) :=
by
  -- `filtration` はそのまま `M.filtration` を使う
  refine
    { filtration := M.filtration
      , process := M.stoppedProcess τ
      , adapted := ?adapted
      , integrable := ?integrable
      , condExp_next := ?martingale_property }
  · -- `adapted`:
    -- P3 側に「停止過程はフィルトレーションに適合」という lemma があればそれを利用。
    -- なければ、`stoppedProcess_eq_of_le` を使いつつ、定義から証明。
    sorry
  · -- `integrable`:
    -- 有界性 `hτ_bdd` と `M.integrable_n` を使って、
    -- すべての n で `Integrable (M.stoppedProcess τ n) μ` を示す。
    --
    -- `τ ω ≤ K` を使うと「止まっていない区間」が有限になるので、
    -- 有界和の integrable 性から押し込む方針。
    sorry
  · -- `martingale_property`:
    intro n
    -- `stoppedProcess_increment_indicator` を使って増分を書き換え、
    -- `condExp` の線形性＋「指示関数つき増分の condExp = 0」から
    -- マルチンゲール性を示す。
    --
    -- 概ね：
    --   condExp (Δ stopped) = condExp( indicator * ΔM ) = 0
    -- → stopped の condExp_next を満たす
    sorry

end StructureTowerProbability
```

ここもまだ「骨格」ですが、

* `adapted` と `integrable` は P3 側の stopped 系 lemma と `M.integrable_n` を組み合わせればなんとかなる範囲
* `martingale_property` は、今回用意した `stoppedProcess_increment_indicator` ＋ `condExp` の線形性をメインで使う

という構図がはっきりしていれば、後は局所的な埋め作業になります。

---

もしこの方向で進めてみて、

* `stoppedProcess_increment_indicator` の case 分けで詰まった
* 有界停止時間を使った integrability の扱いで悩んだ
* `condExp` まわりの具体的な lemma 名が分からない

といったポイントが出てきたら、その部分のコード断片だけ貼ってもらえれば、そこをピンポイントで一緒に整理できます。

今のレイヤ構成（P3 停止時間 API + P4 mathlib マルチンゲール）はかなりきれいなので、この「増分補題 → 有界停止時間版 optional stopping」の流れで一段階上まで持っていくのが次の自然な一手だと思います。
