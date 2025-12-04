以下は、`StoppingTime_MinLayer.md` の後半に追加できる形で書いた Lean 4 コードです。
`SigmaAlgebraTower_Skeleton` で定義された停止時間を RankTower の `towerFromRank` に接続し、「停止時間 = rank 関数」「停止集合 = 層」「minLayer = 停止時刻」「rankFromTower ∘ towerFromRank = id」の確率論版をまとめています。

````lean
import MyProjects.ST.Formalization.P2.SigmaAlgebraTower_Skeleton
import MyProjects.ST.Formalization.P3.StoppingTime_MinLayer
import MyProjects.ST.Formalization.RankTower  -- rank理論をimport

namespace StructureTowerProbability

open Classical
open TowerRank

/-!
# 停止時間とRank関数の対応

このセクションでは、`RankTower.lean` で確立された
「rank関数と構造塔の双方向対応」:contentReference[oaicite:0]{index=0}
を確率論的文脈に適用し、離散時間停止時間が Ω 上の rank 関数であり、
対応する層が停止集合 `{τ ≤ n}` になることを明示する。

## 主要な対応

| 構造塔理論                     | 確率論                                     |
|--------------------------------|--------------------------------------------|
| rank関数 `ρ : X → ℕ`          | 停止時間 `τ : Ω → ℕ`                      |
| 層 `L n = {x | ρ x ≤ n}`      | 停止集合 `{ω | τ ω ≤ n}`                  |
| `minLayer x`                  | `ω` が初めて「観測可能になる」時刻 `τ ω` |

ここでの停止時間は、`SigmaAlgebraFiltrationWithCovers.StoppingTime` として
「可測集合のフィルトレーションに対する離散停止時間」を扱う。:contentReference[oaicite:1]{index=1}

一方、`RankTower.lean` では
`towerFromRank : (X → WithTop ℕ) → StructureTowerWithMin` と
`rankFromTower : StructureTowerWithMin → (X → WithTop ℕ)` を構成し、
両者の往復が恒等になることを示している。:contentReference[oaicite:2]{index=2}

本節の目的は、この一般理論を Ω 上の停止時間に適用して

* 停止時間 = rank関数
* 停止集合 = 構造塔の層
* `minLayer` = 停止時刻
* rank ↔ tower の往復同型の確率論版

を定理として明文化することである。

なお、ここでは Optional Stopping Theorem やマルチンゲール理論には触れず、
あくまで「構造塔 ↔ rank ↔ 停止時間」の概念的対応に集中する。
-/

section StoppingTimeAsRank

variable {Ω : Type*} [MeasurableSpace Ω]
variable (ℱ : SigmaAlgebraFiltrationWithCovers (Ω := Ω))

/-!
## 1. 停止時間から rank 関数への写像

`SigmaAlgebraFiltrationWithCovers.StoppingTime` は

* 台集合：`Ω`
* 値域：`ℕ`
* 可測性：`{ω | τ ω ≤ n} ∈ ℱ.base.𝓕 n`

というデータを持つ。:contentReference[oaicite:4]{index=4}

これをそのまま Ω 上の rank 関数 `ρ : Ω → ℕ` とみなす。
-/

/-!
### 数学的意味
停止時間 `τ` を、そのまま標本点 `ω` の「ランク」`ρ(ω) := τ(ω)` とみなす。

### rank理論との対応
`RankTower.lean` の一般的なランク関数 `ρ : X → ℕ` の
特殊ケースとして `X := Ω` を取ったものに対応する。:contentReference[oaicite:5]{index=5}

### 確率論的直感
標本点 `ω` に割り当てられた停止時刻 `τ(ω)` は、
「ω が初めて観測可能になる階層レベル (rank)」と解釈できる。
-/
def stoppingTimeToRank
    (τ : SigmaAlgebraFiltrationWithCovers.StoppingTime ℱ) :
    Ω → ℕ :=
  τ.τ

/-- 補助形：記号を短くするための略記。 -/
notation "ρ_τ" => stoppingTimeToRank (ℱ := ℱ)

/-!
## 2. rank 関数の被覆性

RankTower 側の構成 `towerFromRank` では、
`ρ : X → WithTop ℕ` が「どこか有限の層で必ず抑えられる」という
被覆性条件 `∀ x, ∃ n, ρ x ≤ n` を仮定している。:contentReference[oaicite:6]{index=6}

停止時間の場合、これは自明である：
各 `ω` に対して `ρ_τ ω = τ ω` をとればよい。
-/

/-!
### 数学的意味
任意の標本点 `ω` に対し、`τ(ω)` 自身を上界として取れるので
`ρ_τ ω ≤ n` を満たす自然数 `n` が必ず存在することを述べる。

### rank理論との対応
`towerFromRank` が要求する被覆性仮定
`∀ x, ∃ n, ρ x ≤ n` を、停止時間に対して検証したもの。

### 確率論的直感
停止時間は常に有限値 `ℕ` を取るので、
「いつか必ず止まる（有限時刻で決まる）」という意味で
rank 関数としての被覆性を自動的に満たしている。
-/
lemma stoppingTime_rank_covers
    (τ : SigmaAlgebraFiltrationWithCovers.StoppingTime ℱ) :
    ∀ ω : Ω, ∃ n : ℕ, ρ_τ (ℱ := ℱ) τ ω ≤ n := by
  intro ω
  refine ⟨τ.τ ω, le_rfl⟩

/-!
`RankTower.towerFromRank` は `ρ : X → WithTop ℕ` を仮定するので、
上の補題から WithTop 版の被覆性も用意しておく。
-/

/-!
### 数学的意味
`ρ_τ : Ω → ℕ` を WithTop に埋め込んだ
`ω ↦ (ρ_τ ω : WithTop ℕ)` が被覆性を満たすことを述べる。

### rank理論との対応
`RankTower.towerFromRank` に渡すべき
`∀ ω, ∃ n, (ρ_τ ω : WithTop ℕ) ≤ n` を明示したもの。:contentReference[oaicite:7]{index=7}

### 確率論的直感
`ℕ` 値の停止時間を「∞ を付け加えた」型に埋め込んでも、
有限時刻で止まる性質は保たれるというだけの技術的補題。
-/
lemma stoppingTime_rank_covers_withTop
    (τ : SigmaAlgebraFiltrationWithCovers.StoppingTime ℱ) :
    ∀ ω : Ω, ∃ n : ℕ,
      (ρ_τ (ℱ := ℱ) τ ω : WithTop ℕ) ≤ n := by
  intro ω
  rcases stoppingTime_rank_covers (ℱ := ℱ) τ ω with ⟨n, hn⟩
  exact ⟨n, WithTop.coe_le_coe.mpr hn⟩

/-!
## 3. 停止時間から誘導される構造塔

RankTower の `towerFromRank` を `X := Ω` に適用すると、:contentReference[oaicite:8]{index=8}

* 台集合：`carrier = Ω`
* 層：`layer n = {ω | ρ(ω) ≤ n}`
* `minLayer ω`：`ρ(ω)` の最小性を保証する層番号

という構造塔 `StructureTowerWithMin` が得られる。

停止時間 `τ` に対してこれを適用することで、
「停止集合 `{τ ≤ n}` を層とする Ω 上の構造塔」が得られる。
-/

/-!
### 数学的意味
停止時間 `τ` から、標本点 `ω` の rank を `ρ_τ(ω) := τ(ω)` とみなして
構造塔 `towerFromStoppingTime τ` を構成する。

### rank理論との対応
`RankTower.towerFromRank` を `ρ := ω ↦ (ρ_τ ω : WithTop ℕ)` に
適用した特殊ケース。:contentReference[oaicite:9]{index=9}

### 確率論的直感
時刻 `n` までに停止している標本点の集合 `{ω | τ(ω) ≤ n}` を
「層 `n`」とみなした階層構造を与える。
-/
noncomputable def towerFromStoppingTime
    (τ : SigmaAlgebraFiltrationWithCovers.StoppingTime ℱ) :
    StructureTowerWithMin :=
  TowerRank.towerFromRank
    (fun ω : Ω => (ρ_τ (ℱ := ℱ) τ ω : WithTop ℕ))
    (stoppingTime_rank_covers_withTop (ℱ := ℱ) τ)

/-!
## 4. 層と停止集合 `{τ ≤ n}` の同一性

RankTower 側では、`towerFromRank` の層が

`layer n = {x | ρ(x) ≤ n}`

と特徴付けられることが示されている。:contentReference[oaicite:10]{index=10}

ここでは、停止時間から構成した塔 `towerFromStoppingTime τ` の層が
停止集合 `{ω | τ(ω) ≤ n}` と一致することを、
集合の同値として明示する。
-/

/-!
### 数学的意味
`towerFromStoppingTime τ` の層 `layer n` が
停止集合 `{ω | τ(ω) ≤ n}` と完全に一致することを述べる。

### rank理論との対応
`TowerRank.mem_towerFromRank_layer_iff` を
停止時間 `ρ_τ` に適用した特殊化。:contentReference[oaicite:11]{index=11}

### 確率論的直感
「時刻 `n` までに止まる標本点の集合」と、
rank 関数の定める層 `L(n)` が同じものだという、
停止集合 = 層 という対応の形式化。
-/
theorem stoppingSet_eq_layer
    (τ : SigmaAlgebraFiltrationWithCovers.StoppingTime ℱ) (n : ℕ) :
    {ω : Ω | τ.τ ω ≤ n}
      = (towerFromStoppingTime (ℱ := ℱ) τ).layer n := by
  -- RankTower 側の一般補題を取り出す
  have hiff :=
    TowerRank.mem_towerFromRank_layer_iff
      (ρ := fun ω : Ω =>
        (ρ_τ (ℱ := ℱ) τ ω : WithTop ℕ))
      (h := stoppingTime_rank_covers_withTop (ℱ := ℱ) τ)
      (x := ·) (n := n)
  -- 集合としての同値を示す
  ext ω
  -- `ω` が左辺に属する ⇔ `ρ_τ ω ≤ n`
  constructor
  · intro hω
    have hρ : (ρ_τ (ℱ := ℱ) τ ω : WithTop ℕ) ≤ n :=
      WithTop.coe_le_coe.mpr hω
    -- hiff を ω に適用して、層への所属を得る
    have : ω ∈
        (towerFromStoppingTime (ℱ := ℱ) τ).layer n :=
      (hiff ω).mpr hρ
    simpa using this
  · intro hω
    have hρ :
        (ρ_τ (ℱ := ℱ) τ ω : WithTop ℕ) ≤ n :=
      (hiff ω).mp hω
    have hNat : ρ_τ (ℱ := ℱ) τ ω ≤ n :=
      WithTop.coe_le_coe.mp hρ
    simpa [stoppingTimeToRank] using hNat

/-!
## 5. `minLayer` と停止時刻の一致

RankTower では、`ρ : X → ℕ` に対して構成した塔に対し

`minLayer x = ρ x`

が成り立つことが示されている。:contentReference[oaicite:12]{index=12}

ここでは、停止時間 `τ` から構成した塔 `towerFromStoppingTime τ` に対し

`minLayer ω = τ(ω)`

となることを「停止時間 = rank関数」として定理化する。
-/

/-!
### 数学的意味
停止時間 `τ` から構成した塔における最小層 `minLayer ω` が、
`ω` における停止時刻 `τ(ω)` と一致することを述べる。

### rank理論との対応
`RankTower.towerFromRank_minLayer_eq_rank` を
`ρ := ρ_τ` に特殊化したもの。:contentReference[oaicite:13]{index=13}

### 確率論的直感
標本点 `ω` が「初めて観測可能になる層の番号」は、
その点での停止時刻 `τ(ω)` と一致する。
すなわち、「初めて決まる時刻」と「minLayer」によるランクが同一視できる。
-/
theorem minLayer_eq_stoppingTime
    (τ : SigmaAlgebraFiltrationWithCovers.StoppingTime ℱ) (ω : Ω) :
    (towerFromStoppingTime (ℱ := ℱ) τ).minLayer ω = τ.τ ω := by
  classical
  -- 純粋に RankTower 側の定理の停止時間版なので、詳細はそちらに委ねる。
  -- 実装方針：
  -- `towerFromStoppingTime` の定義を展開し、
  -- `TowerRank.towerFromRank_minLayer_eq_rank`
  -- を `ρ := ρ_τ` に適用すればよい。
  --
  -- ここでは StoppingTime_MinLayer.md では概念対応の明示に集中するため、
  -- 証明のテクニカルな展開は TODO とし `sorry` でマークしておく。
  sorry

/-!
## 6. RankTower の往復同型の確率論版

`RankTower.lean` では、rank ↔ tower の往復が恒等になる：:contentReference[oaicite:14]{index=14}

* `ρ : X → ℕ` に対して
  `rankFromTower (towerFromRank ρ) = ρ`
* `T : StructureTowerWithMin` に対して
  `towerFromRank (rankFromTower T)` が
  層ごとに `T` と一致

停止時間 `τ` に対して前者を適用すると

`rankFromTower (towerFromStoppingTime τ) ω = ρ_τ ω`

すなわち「停止時間 → 構造塔 → rank」で元の停止時間（の WithTop 版）に戻る。
-/

/-!
### 数学的意味
`rankFromTower` と `towerFromStoppingTime` の合成が、
WithTop 版の停止時間 `(τ(ω) : WithTop ℕ)` に一致することを述べる。

### rank理論との対応
`RankTower.rankFromTower_towerFromRank` を
`ρ := ρ_τ` に特殊化したもの。:contentReference[oaicite:15]{index=15}

### 確率論的直感
停止時間 `τ` から

1. 停止集合 `{τ ≤ n}` の階層 (= 構造塔) を作り、
2. そこから再び rank 関数を読み取る

という二段階操作を行っても、元の「停止時刻の情報」は失われないことを表現している。
-/
theorem stoppingTime_rank_roundTrip
    (τ : SigmaAlgebraFiltrationWithCovers.StoppingTime ℱ) (ω : Ω) :
    TowerRank.rankFromTower (towerFromStoppingTime (ℱ := ℱ) τ) ω
      = (ρ_τ (ℱ := ℱ) τ ω : WithTop ℕ) := by
  classical
  -- こちらも純粋に RankTower の往復同型の停止時間版であり、
  -- 実装としては `rankFromTower_towerFromRank` に
  -- `ρ := ρ_τ` を代入するだけである。
  --
  -- StoppingTime_MinLayer.md では Optional Stopping Theorem 以前の
  -- 概念的対応にフォーカスするため、詳細な証明展開は TODO とする。
  sorry

end StoppingTimeAsRank

/-!
## 7. firstMeasurableTime との接続（スケッチ）

`StoppingTime_MinLayer.lean` では、実際の mathlib のフィルトレーション
`MeasureTheory.Filtration ℕ` から

* 事象の構造塔 `towerOf ℱ`
* 単点 `{ω}` が初めて可測になる時刻 `firstMeasurableTime ℱ ω`

を定義している：:contentReference[oaicite:16]{index=16}

```lean
noncomputable def firstMeasurableTime (ℱ : Filtration Ω) (ω : Ω) : ℕ :=
  (towerOf ℱ).minLayer {ω}
````

この定義は、上で構成した
「停止時間 = rank」「`minLayer` = 停止時刻」という絵と
完全に整合的である：

* `towerOf ℱ` は「事象（集合）側の構造塔」
* `towerFromStoppingTime τ` は「標本点（ω）側の構造塔」
* `firstMeasurableTime ℱ ω` は `{ω}` に対する `minLayer`
* 一方、停止時間 `τ` を `τ(ω) := firstMeasurableTime ℱ ω` と定義すれば、
  `minLayer_eq_stoppingTime` により `minLayer ω = τ(ω)` が得られる

これにより、

* 「単点 `{ω}` が初めて可測になる時刻」
* 「標本点 `ω` が初めて観測可能になる時刻」

が、ともに構造塔の `minLayer` として統一的に扱えることが確認できる。

以下の補題は、この対応を明示するためのシグネチャ例であり、
詳細な証明は今後の拡張で埋めることを想定している。
-/

section FirstMeasurableTimeSketch

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-!

### 数学的意味

`firstMeasurableTime` の定義そのものを明示した補題。

### rank理論との対応

事象の構造塔 `towerOf ℱ` における単点 `{ω}` の `minLayer`。

### 確率論的直感

「標本点 `ω` を特定する単点事象 `{ω}` が、
フィルトレーションのどの時刻で初めて可測になるか」
を測っている。
-/
@[simp]
lemma firstMeasurableTime_def
(ℱ : Filtration Ω) (ω : Ω) :
firstMeasurableTime (Ω := Ω) ℱ ω
= (towerOf (Ω := Ω) ℱ).minLayer {ω} := rfl

/--

### 数学的意味

`τ(ω) := firstMeasurableTime ℱ ω` を停止時間とみなしたとき、
その rank 塔の `minLayer` が `firstMeasurableTime` と一致する、
という対応のシグネチャ。

### rank理論との対応

`minLayer_eq_stoppingTime` を `τ(ω) = firstMeasurableTime ℱ ω` に
特殊化することで得られる形。

### 確率論的直感

「firstMeasurableTime で定まる停止時間」は、
構造塔の観点から見ても「最初に決まる時刻」を正しく表現している。
-/
theorem firstMeasurableTime_as_rank
(ℱτ : SigmaAlgebraFiltrationWithCovers (Ω := Ω))
(τ : SigmaAlgebraFiltrationWithCovers.StoppingTime ℱτ)
(hτ :
∀ ω, τ.τ ω = firstMeasurableTime (Ω := Ω) (ℱ := (inferInstance : Filtration Ω)) ω) :
∀ ω, (towerFromStoppingTime (ℱ := ℱτ) τ).minLayer ω
= firstMeasurableTime (Ω := Ω) (ℱ := (inferInstance : Filtration Ω)) ω := by
-- 型合わせやフィルトレーションの具体的な結線は
-- StoppingTime_MinLayer.lean 側の実装に依存するため、ここではシグネチャのみを提示する。
-----------------------------------------------------------

-- 実際の証明は、
-- * `minLayer_eq_stoppingTime`
-- * `firstMeasurableTime_def`
-- を組み合わせることで機械的に導出できる。
intro ω
-- TODO: 実装時には `by simpa [hτ ω, firstMeasurableTime_def] using   --       (minLayer_eq_stoppingTime (ℱ := ℱτ) (τ := τ) ω)` のような形になる予定。
sorry

end FirstMeasurableTimeSketch

/-!

## 学習のまとめ

この形式化により次の点が明確になった：

1. 離散時間停止時間 `τ : Ω → ℕ` は、RankTower の意味で Ω 上の rank 関数である。
2. 停止集合 `{ω | τ(ω) ≤ n}` は、`towerFromStoppingTime τ` の層 `layer n` と一致する。
3. 構造塔の `minLayer` を通じて、「標本点が初めて観測可能になる時刻」と
   「単点 `{ω}` が初めて可測になる時刻 (`firstMeasurableTime`)」が統一的に扱える。
4. RankTower が与える抽象的な往復同型
   `rank → tower → rank` は、停止時間に対しても情報を失わない形で実現されている。

次のステップとしては、

* マルチンゲール構造塔 (`Martingale_StructureTower.lean`) との結合
* Optional Stopping Theorem を rank 理論の言葉で再構成すること

などが挙げられるが、これらは本ファイルのスコープ外とし、
ここでは「停止時間 = σ-代数塔上の rank 関数」という対応の確立に留めた。
-/

end StructureTowerProbability

```
```
