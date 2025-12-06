import MyProjects.ST.Formalization.P4.Martingale_StructureTower
import MyProjects.ST.Formalization.P3.StoppingTime_MinLayer
import MyProjects.ST.Rank.P3.RankTower
import MyProjects.ST.Rank.Prob.P1.StoppingTime_C

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

/-!
# 有限部分集合の構造塔：`Finset` と元数による rank

## 数学的背景

型 `α` 上の有限部分集合は `Finset α` で表される。
ここでは

* **元**: `Finset α`（有限部分集合）
* **rank**: 元数 `s.card : ℕ`
* **第 `n` 層**: 元数が `n` 以下の有限部分集合全体

という対応で、`StructureTowerWithMin` の具体例を構成する。

## 構造塔としての解釈

- 層 `layer n` は「高々 `n` 個の点を使って作られた部分集合」の全体。
- `minLayer s` は、その部分集合 `s` を作るのに必要な**最小の層番号**であり、
  この例では単に `s.card` になる。
- 被覆性：任意の有限部分集合 `s` について `s.card` という有限の層が存在するので、
  構造塔は全ての元を覆う。

これは線形包の例（ベクトル空間の次元）と良く似ているが、

- ベクトルではなく「点の集まり」
- 線形結合ではなく「単純な集合の包含」

という、より組合せ論的・幾何的な直感で同じパターンを見せる例になっている。

## 教育的意義

- **rank = 資源の個数** という解釈を最も素朴な形で体験できる。
- `towerFromRank` による「rank → 構造塔」構成を、停止時間以外の
  全く別の具体例で確認できる。
- 後でグラフ・単体複体・線形包などに一般化する際の、共通テンプレートとなる。
-/

namespace StructureTowerCombinatorics

open Classical
open TowerRank

section

variable (α : Type*) [DecidableEq α]

/-!
## 1. rank 関数の定義

有限部分集合 `s : Finset α` の rank を、そのまま元数 `s.card` と定義する。
これは「何個の点を使っているか」を測る量であり、構造塔の最小層と一致する。
-/

/-- 有限部分集合の rank（元数）。 -/
def finiteSubsetRank (s : Finset α) : ℕ :=
  s.card

/-- rank 関数の被覆性：各有限部分集合 `s` は自分自身の元数以下で抑えられる。 -/
lemma finiteSubsetRank_covers :
    ∀ s : Finset α, ∃ n : ℕ, finiteSubsetRank (α := α) s ≤ n := by
  intro s
  refine ⟨s.card, ?_⟩
  simp [finiteSubsetRank]

/-!
## 2. `towerFromRank` による構造塔の構成

`RankTower.lean` で定義された一般構成

* `towerFromRank : (X → WithTop ℕ) → (∀ x, ∃ n, ρ x ≤ n) → StructureTowerWithMin`

を用いて、有限部分集合の構造塔を定義する。
ここでは

* キャリア `carrier = Finset α`
* rank `ρ s = (finiteSubsetRank s : WithTop ℕ)` （自然数を `WithTop` に埋め込む）

とする。
-/

/-- 有限部分集合と元数から作る構造塔。 -/
noncomputable def finiteSubsetTower : StructureTowerWithMin :=
  TowerRank.towerFromRank
    (fun s : Finset α => (finiteSubsetRank (α := α) s : WithTop ℕ))
    (by
      intro s
      -- ρ(s) = s.card なので、`n = s.card` を取れば ρ(s) ≤ n が成り立つ
      refine ⟨s.card, ?_⟩
      simp [finiteSubsetRank])

/-!
この定義により、`finiteSubsetTower α` は次のように具体化される：

* `layer n = { s | finiteSubsetRank s ≤ n }`
* `minLayer s = finiteSubsetRank s = s.card`

これらは RankTower 側の一般定理から自動的に従う。
-/

/-!
## 3. 層の特徴付け

一般論 `towerFromRank` の定義から、層は

`L(n) = { x | ρ(x) ≤ n }`

として与えられている。
有限部分集合に対してこれを展開すると、
「元数が `n` 以下の有限部分集合の全体」という特徴付けになる。
-/

/-- 有限部分集合構造塔の第 `n` 層は、元数が `n` 以下の有限部分集合全体である。 -/
lemma finiteSubsetTower_layer_characterization (n : ℕ) :
    (finiteSubsetTower (α := α)).layer n =
      { s : Finset α | finiteSubsetRank (α := α) s ≤ n } := by
  -- `towerFromRank` の定義をそのまま展開するだけでよい
  ext s
  simp [finiteSubsetTower, finiteSubsetRank, TowerRank.towerFromRank]

/-!
## 4. `minLayer` と rank の一致

RankTower.lean の一般定理

* `towerFromRank_minLayer_eq_rank`

を適用すると、`towerFromRank` から作った構造塔の `minLayer` は
元の rank 関数と一致する。

この例では、`minLayer s = s.card` が機械的に導かれる。
-/

/-- 有限部分集合構造塔の `minLayer` は、元数 `card` に一致する。 -/
lemma finiteSubsetTower_minLayer_eq_card (s : Finset α) :
    (finiteSubsetTower (α := α)).minLayer s = s.card := by
  -- 一般定理を rank = `finiteSubsetRank` に適用
  have h :=
    TowerRank.towerFromRank_minLayer_eq_rank
      (ρ := finiteSubsetRank (α := α))
      (h := by
        intro t
        refine ⟨t.card, ?_⟩
        simp [finiteSubsetRank])
      (x := s)
  -- 定義を展開して「minLayer = card」に書き換える
  simpa [finiteSubsetTower, finiteSubsetRank] using h

/-- `minLayer` を rank 関数として見るためのシンプルな別表記。 -/
lemma finiteSubsetTower_minLayer_eq_rank (s : Finset α) :
    (finiteSubsetTower (α := α)).minLayer s =
      finiteSubsetRank (α := α) s := by
  simpa [finiteSubsetRank] using finiteSubsetTower_minLayer_eq_card (α := α) s

/-- 構造塔の被覆性は、rank の被覆性からただちに従うことの再確認。 -/
lemma finiteSubsetTower_covers (s : Finset α) :
    ∃ n : ℕ, s ∈ (finiteSubsetTower (α := α)).layer n := by
  -- `n = minLayer s` を取れば必ず層に属する
  refine ⟨(finiteSubsetTower (α := α)).minLayer s, ?_⟩
  exact (finiteSubsetTower (α := α)).minLayer_mem s

/-!
## 5. 具体的な計算例

以下では、抽象的な型 `α` に対する一般的な性質と、
具体的な `α = ℕ` の場合の挙動を確認する。
-/

/-- 例1：任意の有限部分集合について、`minLayer` は元数と一致する。 -/
example (s : Finset α) :
    (finiteSubsetTower (α := α)).minLayer s = s.card := by
  simpa using finiteSubsetTower_minLayer_eq_card (α := α) s

/-- 例2：元数が `n` 以下なら、第 `n` 層に属する。 -/
example (s : Finset α) (n : ℕ) (h : s.card ≤ n) :
    s ∈ (finiteSubsetTower (α := α)).layer n := by
  -- 層の特徴付けに書き換えてから、仮定を使う
  have h' : finiteSubsetRank (α := α) s ≤ n := by
    simpa [finiteSubsetRank] using h
  -- 目標を rank の不等式に書き換えてから `h'` を適用
  simpa [finiteSubsetTower_layer_characterization (α := α) n] using h'

/-- 例3（具体例）：`{1, 3}` は第2層には属するが、第1層には属さない（`α = ℕ`）。 -/
example : ({1, 3} : Finset ℕ) ∈ (finiteSubsetTower (α := ℕ)).layer 2 ∧
    ({1, 3} : Finset ℕ) ∉ (finiteSubsetTower (α := ℕ)).layer 1 := by
  -- `card {1,3} = 2` を計算
  have hcard : ({1, 3} : Finset ℕ).card = 2 := by
    decide
  constructor
  · -- 2層には属する
    have h : ({1, 3} : Finset ℕ).card ≤ 2 := by
      simpa [hcard]
    have h' : finiteSubsetRank (α := ℕ) ({1, 3} : Finset ℕ) ≤ 2 := by
      simpa [finiteSubsetRank] using h
    simpa [finiteSubsetTower_layer_characterization (α := ℕ) 2] using h'
  · -- 1層には属さない
    intro hmem
    have h' :
        finiteSubsetRank (α := ℕ) ({1, 3} : Finset ℕ) ≤ 1 := by
      -- 層の特徴付けから不等式に落とす
      simpa [finiteSubsetTower_layer_characterization (α := ℕ) 1] using hmem
    -- `card = 2` なので `2 ≤ 1` は不可能
    have : 2 ≤ 1 := by
      simpa [finiteSubsetRank, hcard] using h'
    exact Nat.not_succ_le_self 1 this

/-!
## この例のポイント（まとめ）

1. **rank = 元数**
   有限部分集合の「大きさ」を、そのまま rank 関数として扱えることを確認した。

2. **`towerFromRank` の具体的実装**
   `towerFromRank` に `ρ s = card s` を入れるだけで、
   「高々 n 個の点を持つ部分集合の層」という自然な構造塔が得られる。

3. **`minLayer = rank` の一般定理の再利用**
   `TowerRank.towerFromRank_minLayer_eq_rank` をそのまま適用することで、
   `minLayer s = card s` を一行で導出できた。
   これは停止時間の場合と全く同じパターンである。

4. **他分野への橋渡し**
   - 単体複体の `k`-骨格（`k` 次元以下の単体全体）
   - グラフにおける「頂点数で切った部分グラフの塔」
   - 線形包（次元による層）

   など、よりリッチな例へ発展させる際のテンプレートとして機能する。
-/

end

end StructureTowerCombinatorics
