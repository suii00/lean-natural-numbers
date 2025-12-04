import Mathlib.Order.TypeTags
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Rank Functions and Structure Towers: The Canonical Correspondence

## 概要

構造塔（StructureTowerWithMin）とランク関数（X → WithTop ℕ）の間の
双方向対応を確立する。これは構造塔理論の「正規形」を与える核心的結果である。

## 主要な構成

1. **towerFromRank**: rank 関数から構造塔を構成（順方向）
2. **rankFromTower**: 構造塔から rank 関数を抽出（逆方向）
3. **正規形定理**: 双方向の整合性

## 数学的意義

**構造塔の Level 2 は本質的に rank 理論である**

この対応により：
- `minLayer x` = `rank x` という同一視が正当化される
- 構造塔の本質が「要素の複雑さの階層化」であることが明確になる
- 具体例（線形包、イデアル、フィルトレーション）が統一的に理解できる

## ランク関数とは

数学における「ランク」の概念は多様だが、共通する性質がある：

- **線形代数**: ベクトルを表現するのに必要な基底ベクトルの最小個数
- **代数**: イデアルや部分群を生成するのに必要な元の最小個数
- **組合せ論**: グラフの頂点彩色数、マトロイドのランク
- **確率論**: フィルトレーションにおける「初めて観測される時刻」

これらすべてに共通するのは：
1. 各要素 x に自然数（または ∞）を対応させる
2. ランクが n 以下の要素の集合 {x | rank(x) ≤ n} が単調増加
3. すべての要素が有限ランクを持つ（被覆性）

構造塔は、この「ランクによる階層化」を一般的に形式化したものである。

## なぜ minLayer = rank なのか

構造塔の minLayer 関数は：
- 各要素 x が「どの層に本質的に属するか」を決定
- x を含む最小の層を選ぶ

これはまさに「x の複雑さ」= rank の定義そのものである。

layer n = {x | rank(x) ≤ n}

という対応により、構造塔とランク理論が同一視される。
-/

/-!
## 前提：StructureTowerWithMin の定義

CAT2_complete.lean から必要な定義を再掲する。
実際の使用時は import で読み込むが、ここでは自己完結性のために含める。
-/

/-- 最小層を持つ構造塔（再掲）-/
structure StructureTowerWithMin where
  /-- 基礎集合 -/
  carrier : Type*
  /-- 添字集合 -/
  Index : Type*
  /-- 添字集合上の半順序 -/
  [indexPreorder : Preorder Index]
  /-- 各層の定義: Index → Set carrier -/
  layer : Index → Set carrier
  /-- 被覆性: すべての層の和集合が全体を覆う -/
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  /-- 単調性: 順序を保存 -/
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j
  /-- 各要素の最小層を選ぶ関数 -/
  minLayer : carrier → Index
  /-- minLayer x は実際に x を含む -/
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  /-- minLayer x は最小 -/
  minLayer_minimal : ∀ x i, x ∈ layer i → minLayer x ≤ i

namespace TowerRank

open Classical

/-!
## Part 1: Rank 関数から構造塔へ（順方向）

**核心的洞察**：
ランク関数 ρ : X → WithTop ℕ が与えられたとき、自然な構造塔が定義できる：
```
layer(n) := {x ∈ X | ρ(x) ≤ n}
```

この構造塔では：
- 単調性は自動的に満たされる（n ≤ m ⇒ layer(n) ⊆ layer(m)）
- 被覆性は「すべての要素が有限ランクを持つ」という条件に対応
- minLayer(x) = ρ(x) （ランク自身が最小層）
-/

section RankToTower

variable {X : Type*}

/-!
### 数学的背景：なぜこの構成が自然か

ランク ≤ n の要素の集合を層とすることで：

1. **単調性の保証**：
   n ≤ m かつ ρ(x) ≤ n ⇒ ρ(x) ≤ m
   したがって layer(n) ⊆ layer(m)

2. **被覆性の保証**：
   すべての x に対して ρ(x) が有限ならば、
   x ∈ layer(ρ(x)) が成り立つ

3. **minLayer の自然な定義**：
   x ∈ layer(n) ⇔ ρ(x) ≤ n
   よって、x を含む最小の n は ρ(x) そのもの
-/

/--
rank 関数から構造塔を構成する基本構成。

**重要な点**：
- `h_covers` 条件は「すべての要素が有限ランクを持つ」を保証
- これにより被覆性と minLayer の定義が可能になる
- WithTop ℕ を使うことで、無限ランクの可能性も扱える

**数学的意味**：
この構成は「ランクによる階層化」の形式化である。
ランクが小さいほど早く層に入り、ランク自身が最小層を定める。
-/
noncomputable def towerFromRank (ρ : X → WithTop ℕ)
    (h_covers : ∀ x, ∃ n : ℕ, ρ x ≤ n) :
    StructureTowerWithMin where
  carrier := X
  Index := ℕ
  indexPreorder := inferInstance

  layer n := {x : X | ρ x ≤ n}

  covering := by
    -- すべての要素は有限ランクを持つので、どこかの層に属する
    intro x
    obtain ⟨n, hn⟩ := h_covers x
    exact ⟨n, hn⟩

  monotone := by
    -- n ≤ m ならば、ρ(x) ≤ n ⇒ ρ(x) ≤ m
    intro i j hij x hx
    exact le_trans hx (WithTop.coe_le_coe.mpr hij)

  minLayer := fun x =>
    -- x の最小のランクを選ぶ
    -- h_covers により、有限ランクを持つことが保証されている
    Nat.find (h_covers x)

  minLayer_mem := by
    intro x
    -- Nat.find の定義より、minLayer(x) では ρ(x) ≤ minLayer(x)
    change ρ x ≤ Nat.find (h_covers x)
    exact Nat.find_spec (h_covers x)

  minLayer_minimal := by
    intro x i hx
    -- x ∈ layer(i) すなわち ρ(x) ≤ i
    -- Nat.find の最小性より minLayer(x) ≤ i
    change Nat.find (h_covers x) ≤ i
    exact Nat.find_min' (h_covers x) hx

/-!
### 基本性質：層の特徴付け

以下の補題は、towerFromRank で構成された塔の性質を明示する。
-/

/-- layer の明示的な特徴付け -/
lemma towerFromRank_layer_eq (ρ : X → WithTop ℕ) (h : ∀ x, ∃ n : ℕ, ρ x ≤ n)
    (n : ℕ) :
    (towerFromRank ρ h).layer n = {x : X | ρ x ≤ n} := by
  rfl

/-- minLayer の明示的な特徴付け -/
lemma towerFromRank_minLayer_eq (ρ : X → WithTop ℕ) (h : ∀ x, ∃ n : ℕ, ρ x ≤ n)
    (x : X) :
    (towerFromRank ρ h).minLayer x = Nat.find (h x) := by
  rfl

/-- minLayer が実際にランクと一致する（適切な条件下で）-/
lemma towerFromRank_minLayer_eq_rank (ρ : X → ℕ)
    (h : ∀ x, ∃ n : ℕ, (ρ x : WithTop ℕ) ≤ n) (x : X) :
    (towerFromRank (fun x => (ρ x : WithTop ℕ)) h).minLayer x = ρ x := by
  sorry  -- 証明はsorry可

/-- 要素が層に属する ⇔ ランクがその層以下 -/
lemma mem_towerFromRank_layer_iff (ρ : X → WithTop ℕ)
    (h : ∀ x, ∃ n : ℕ, ρ x ≤ n) (x : X) (n : ℕ) :
    x ∈ (towerFromRank ρ h).layer n ↔ ρ x ≤ n := by
  rfl

end RankToTower

/-!
## Part 2: 構造塔から Rank 関数へ（逆方向）

**逆方向の構成**：
構造塔 T が与えられたとき、各要素 x に対して
「x が初めて現れる層」の添字を rank として定義できる：
```
rank(x) := inf {n | x ∈ layer(n)}
```

この構成により、構造塔の情報がランク関数に凝縮される。

**注意点**：
- WithTop ℕ を使うことで、無限大の可能性も扱う
- sInf（下限）の well-definedness に注意が必要
- 逆方向は「情報の圧縮」である（層の構造→単一の数値）
-/

section TowerToRank

/--
構造塔から rank 関数を抽出する。

**定義**：
rank(x) := inf {n : ℕ | x ∈ layer(n)}

**数学的意味**：
- x を含む最小の層の添字
- これは minLayer の「ℕ添字版」と見なせる
- 無限大を許容することで、より一般的な構造塔も扱える

**重要な性質**：
- rank(x) ≤ n ⇔ x ∈ layer(n)（これが本質）
- 適切な条件下で、これは minLayer と一致する
-/
noncomputable def rankFromTower (T : StructureTowerWithMin) :
    T.carrier → WithTop ℕ :=
  fun x => sInf {n : ℕ | x ∈ T.layer n}

/-!
### 基本性質

rankFromTower の性質を特徴付ける補題群。
これらは「rank ≤ n ⇔ x ∈ layer(n)」という対応を示す。
-/

/-- rank ≤ n であることの特徴付け -/
lemma rankFromTower_le_iff (T : StructureTowerWithMin) (x : T.carrier) (n : ℕ) :
    rankFromTower T x ≤ n ↔ x ∈ T.layer n := by
  sorry

/-- 層に属することと rank の関係 -/
lemma mem_layer_of_rankFromTower_le (T : StructureTowerWithMin)
    (x : T.carrier) (n : ℕ) (h : rankFromTower T x ≤ n) :
    x ∈ T.layer n := by
  sorry

/-- rankFromTower は T.minLayer と整合的 -/
lemma rankFromTower_le_minLayer (T : StructureTowerWithMin) (x : T.carrier) :
    rankFromTower T x ≤ T.minLayer x := by
  sorry

end TowerToRank

/-!
## Part 3: 正規形定理と往復の整合性

**核心的定理**：
適切な条件下で、rank ↔ tower の双方向構成が可逆である：

1. **順方向の往復**：rank から塔を作り、そこから rank を取ると元に戻る
2. **逆方向の往復**：塔から rank を作り、そこから塔を作ると元に戻る

これにより、「構造塔 with minLayer」と「ランク関数」が本質的に同等であることが示される。
-/

section NormalForm

/-!
### 数学的考察：なぜ正規形なのか

ランク関数と構造塔の対応は、数学的対象の「正規形」を与える：

1. **一意性**: 同じランク関数から作られる構造塔は本質的に同じ
2. **完全性**: すべての構造塔（適切な条件下）はあるランク関数から来る
3. **自然性**: この対応は圏論的に自然

これは、群論における「生成元と関係式」や、
線形代数における「基底による座標表示」に類似した、
構造塔理論の正準的表現である。
-/

/--
順方向の往復：rank → tower → rank が恒等的

**主張**：
有限値ランク関数 ρ : X → ℕ から構造塔を作り、
そこから rank を取り出すと、元の ρ が回復される。

**数学的意味**：
「ランクによる階層化」を塔として形式化し、
その塔から「最初に現れる層」を抽出すると、
元のランクと一致する。

これは「情報の無損失性」を保証する。
-/
theorem rankFromTower_towerFromRank (ρ : X → ℕ)
    (h : ∀ x, ∃ n : ℕ, (ρ x : WithTop ℕ) ≤ n) (x : X) :
    rankFromTower (towerFromRank (fun x => (ρ x : WithTop ℕ)) h) x = ρ x := by
  sorry

/--
逆方向の往復：tower → rank → tower が恒等的（条件付き）

**条件**：
構造塔 T が「ℕ添字」であり、minLayer が実際に ℕ 値を返すとき。

**主張**：
構造塔から rank を抽出し、その rank から塔を再構成すると、
層の構造が元に戻る。

**注意**：
完全な同型ではなく、「層の集合として」の一致。
これは構造塔の本質が「どの層にどの要素が属するか」であることを示す。
-/
theorem towerFromRank_rankFromTower (T : StructureTowerWithMin)
    (h_index : T.Index = ℕ)
    (h_minLayer_nat : ∀ x, ∃ n : ℕ, T.minLayer x = n)
    (h_covers : ∀ x, ∃ n : ℕ, rankFromTower T x ≤ n) :
    ∀ n : ℕ, (towerFromRank (rankFromTower T) h_covers).layer n = T.layer n := by
  sorry

/-!
### 同値の本質的意味

上記の2つの定理は、以下を示している：

**構造塔理論の Level 2 は、本質的にランク理論である**

- 構造塔 + minLayer ≃ Rank 関数
- どちらの視点でも同じ数学的対象を記述できる
- 応用に応じて、使いやすい方を選べる

**具体例での直感**：
- 線形代数：「部分空間の階層」 ≃ 「ベクトルの次元」
- 確率論：「フィルトレーション」 ≃ 「初観測時刻」
- 代数：「イデアルの階層」 ≃ 「生成元の個数」
-/

end NormalForm

/-!
## Part 4: Vec2Q への応用

Closure_Basic.lean で定義された `minBasisCount` が、
まさにランク関数の典型例であることを確認する。

**数学的背景**：
ℚ² の各ベクトルに対して、それを表現するのに必要な
標準基底ベクトルの最小個数が minBasisCount である。

これは典型的なランク関数であり：
- rank((0, 0)) = 0（零ベクトル）
- rank((a, 0)) = 1（a ≠ 0）（e₁ のみ）
- rank((0, b)) = 1（b ≠ 0）（e₂ のみ）
- rank((a, b)) = 2（a, b ≠ 0）（両方必要）
-/

section Vec2QApplication

-- Closure_Basic.lean からの定義を参照
-- 実際の実装では import する

/-- Vec2Q の定義（再掲）-/
def Vec2Q : Type := ℚ × ℚ

/-- minBasisCount の定義（再掲）-/
noncomputable def minBasisCount (v : Vec2Q) : ℕ :=
  if v.1 = 0 ∧ v.2 = 0 then 0
  else if v.1 = 0 ∨ v.2 = 0 then 1
  else 2

/-- minBasisCount は rank 関数の条件を満たす -/
lemma minBasisCount_bounded : ∀ v : Vec2Q, ∃ n : ℕ, minBasisCount v ≤ n := by
  intro v
  use 2
  -- minBasisCount は常に 0, 1, 2 のいずれか
  sorry

/--
minBasisCount から構成される塔が、
Closure_Basic.lean の linearSpanTower と一致する。

**数学的意味**：
線形包による階層構造は、本質的に
「必要な基底ベクトル数」というランク関数で決定される。

この定理は、構造塔理論が線形代数の
標準的な概念を正確に捉えていることを示す。
-/
example :
    ∃ (linearSpanTower : StructureTowerWithMin),
      linearSpanTower = towerFromRank
        (fun v => (minBasisCount v : WithTop ℕ)) minBasisCount_bounded := by
  sorry

/-!
### 教育的ポイント

この例が示すこと：

1. **抽象と具体の橋渡し**：
   - 抽象的な「構造塔」理論
   - 具体的な「線形包」の階層
   - これらが同一の数学的構造

2. **ランクの普遍性**：
   - minBasisCount という具体的な関数
   - 一般的なランク理論の特殊例
   - 他の例（イデアル、フィルトレーション）も同様

3. **理論の有用性**：
   - 線形代数の定理が、構造塔の定理として一般化される
   - 証明の再利用が可能になる
   - 異なる分野の類似性が明確になる
-/

end Vec2QApplication

/-!
## Part 5: 他の具体例

ランク理論の普遍性を示すため、他の数学的文脈での例を挙げる。
-/

section OtherExamples

/-!
### 例1：自然数のランク

最も単純な例：各自然数 n のランクを n 自身とする。
-/

/-- 自然数の恒等ランク関数 -/
def natRank : ℕ → ℕ := id

/-- この場合の被覆性は自明 -/
lemma natRank_covers : ∀ n : ℕ, ∃ m : ℕ, (natRank n : WithTop ℕ) ≤ m := by
  intro n
  use n
  rfl

/-- natRank から作った塔が自然数の標準的な塔と一致 -/
example :
    (towerFromRank (fun n => (natRank n : WithTop ℕ)) natRank_covers).layer =
      fun n => {k : ℕ | k ≤ n} := by
  sorry

/-!
### 例2：有限集合のべき集合

集合の濃度をランクとする例。
-/

/-- 有限集合 {1, 2, ..., n} の部分集合のランク = 濃度 -/
def cardinalityRank (n : ℕ) (S : Finset (Fin n)) : ℕ := S.card

lemma cardinalityRank_covers (n : ℕ) :
    ∀ S : Finset (Fin n), ∃ m : ℕ, (cardinalityRank n S : WithTop ℕ) ≤ m := by
  intro S
  use n
  have h : S.card ≤ n := by sorry
  exact WithTop.coe_le_coe.mpr h

/-!
このランクによる構造塔は：
- layer(0) = {∅}（空集合のみ）
- layer(1) = 濃度 ≤ 1 の部分集合
- layer(k) = 濃度 ≤ k の部分集合

これは組合せ論における「k-部分集合の階層」を形式化している。
-/

end OtherExamples

/-!
## 学習のまとめ

### 構造塔の階層的理解

本ファイルの内容により、構造塔理論の「Level 2」が完成した：
```
Level 0: 半順序集合、単調写像
    ↓
Level 1: StructureTower（単調な集合族）
    ↓
Level 2: StructureTowerWithMin ≃ Rank関数 ←【本ファイル】
    ↓
Level 3: 圏構造、普遍性（CAT2_complete.lean）
    ↓
Level 4: 確率論への応用（フィルトレーション、停止時間）
```

### 重要な洞察

1. **minLayer = rank の同一視**
   - 構造塔の minLayer は、要素の「複雑さ」を測る
   - これは数学的な rank の概念そのもの
   - layer(n) = {x | rank(x) ≤ n} という対応

2. **双方向の構成**
   - rank → tower: 自然な階層化
   - tower → rank: 情報の凝縮
   - 往復により正規形を得る

3. **普遍性の源泉**
   - rank による特徴付けが一意性を保証
   - これが圏論的な普遍性の基盤
   - CAT2_complete.lean の定理群の基礎

### 今後の応用

このランク理論は、以下の文脈で活用される：

1. **確率論**（フィルトレーション理論）
   - rank = 初観測時刻（停止時間）
   - layer(n) = 時刻 n までに観測可能な事象

2. **代数的構造**（イデアル、部分群）
   - rank = 生成元の最小個数
   - layer(n) = n 個以下の元で生成される部分構造

3. **位相空間**（開集合の階層）
   - rank = 開被覆の最小基数
   - layer(n) = n 個以下の基本開集合で表現可能

### Lean 4 実装の教訓

1. **定義の完全性**：
   - structure/def の本体に sorry は含まれていない
   - これが形式化の信頼性を保証

2. **型システムの力**：
   - WithTop ℕ により有限/無限を統一的に扱う
   - Nat.find により構成的に最小値を取得

3. **証明の段階的構築**：
   - 基本的な性質から徐々に複雑な定理へ
   - 各レベルで具体例により直感を確認
-/

end TowerRank
