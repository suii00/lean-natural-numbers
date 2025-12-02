# 構造塔理論：ステップバイステップ学習ガイド

## 🎯 このガイドの使い方

このガイドは、構造塔理論を**ゼロから理解する**ための完全な道筋を提供します。

### 前提知識

- **必須**: 線形代数の基礎（ベクトル空間、基底、線形独立）
- **必須**: Lean 4 の基本構文（`def`, `lemma`, `by`タクティク）
- **推奨**: 集合論の基礎（包含関係、写像）
- **任意**: 圏論の初歩（対象、射）

### 学習時間の目安

- **Level 1** (基礎): 2-3日
- **Level 2** (統合): 3-5日
- **Level 3** (一般化): 5-7日
- **Total**: 2-3週間（1日2-3時間の学習を想定）

---

## 📅 Day 1-2: 構造塔とは何か？

### 目標
- 構造塔の直感的理解
- Bourbaki の階層的思考法

### 学習内容

#### Step 1.1: Bourbaki_StructureTower_原点.pdf を読む

**重要な概念**:
1. **半順序集合**: (α, ≤) の定義と例
2. **上限の一意性**: supremum が存在すれば一意
3. **単調な集合族**: i ≤ j ⇒ Xᵢ ⊆ Xⱼ

**理解度チェック**:
```
Q1: 半順序の3つの性質を述べよ
    - 反射律: a ≤ a
    - 反対称律: a ≤ b ∧ b ≤ a ⇒ a = b
    - 推移律: a ≤ b ∧ b ≤ c ⇒ a ≤ c

Q2: 自然数の初期区間 Iₙ = {k ∈ ℕ | k ≤ n} は単調か？
    - Yes. m ≤ n ⇒ Iₘ ⊆ Iₙ

Q3: なぜ構造塔を「塔」と呼ぶのか？
    - 層が添字に沿って積み上がっているから
```

#### Step 1.2: Bourbaki_Lean_Guide.lean を読む

**ファイルを開いて確認**:
```lean
-- 45-47行目: 上限の一意性
lemma supremum_unique' {A : Set α} {s s' : α}
    (hs : IsLUB A s) (hs' : IsLUB A s') : s = s'

-- 79-81行目: StructureTower の定義
structure StructureTower (ι α : Type*) [Preorder ι] : Type _ where
  level : ι → Set α
  monotone_level : ∀ ⦃i j⦄, i ≤ j → level i ⊆ level j

-- 144-148行目: 自然数の初期区間
def natInitialSegments : StructureTower ℕ ℕ where
  level n := {k : ℕ | k ≤ n}
  monotone_level := by ...
```

**理解度チェック**:
```
Q1: StructureTower に minLayer がないのはなぜ？
    - これは「原点版」で、最もシンプルな定義
    - minLayer は後の発展で追加される

Q2: natInitialSegments.level 3 は何か？
    - {0, 1, 2, 3}

Q3: natInitialSegments.union = ℕ を証明する方針は？
    - すべての n ∈ ℕ に対して n ∈ level n を示す
```

**演習**:
```lean
-- 1. 偶数の初期区間を定義せよ
def evenInitialSegments : StructureTower ℕ ℕ where
  level n := {k : ℕ | k ≤ n ∧ Even k}
  monotone_level := by sorry

-- 2. union_eq_univ は成り立つか？
-- ヒント: 奇数はどこにも属さない
```

---

## 📅 Day 3-5: 線形包と minLayer

### 目標
- 具体的な構造塔の実装
- minLayer の意味理解

### 学習内容

#### Step 2.1: Basic.lean を**完全に理解**する

**最重要セクション**:

##### 1. Vec2Q の定義（82-100行目）
```lean
def Vec2Q : Type := ℚ × ℚ
def Vec2Q.zero : Vec2Q := (0, 0)
def e₁ : Vec2Q := (1, 0)
def e₂ : Vec2Q := (0, 1)
```

**手を動かす**:
```
紙に書いて確認:
- 零ベクトル (0, 0)
- 基底ベクトル e₁ = (1, 0), e₂ = (0, 1)
- 一般のベクトル (3, 5) を e₁, e₂ で表現
  → (3, 5) = 3·e₁ + 5·e₂
```

##### 2. minBasisCount の定義（132-136行目）
```lean
noncomputable def minBasisCount (v : Vec2Q) : ℕ :=
  if v.1 = 0 ∧ v.2 = 0 then 0      -- 零ベクトル
  else if v.1 = 0 ∨ v.2 = 0 then 1  -- 軸上
  else 2                             -- 一般位置
```

**計算練習**:
```
minBasisCount (0, 0) = ?    答え: 0
minBasisCount (5, 0) = ?    答え: 1（e₁のみ）
minBasisCount (0, 3) = ?    答え: 1（e₂のみ）
minBasisCount (2, 7) = ?    答え: 2（両方必要）
minBasisCount (-3, 0) = ?   答え: 1（e₁のみ）
```

**理解度チェック**:
```
Q1: なぜ minBasisCount (5, 0) = 1 なのか？
    - (5, 0) = 5·e₁ + 0·e₂ なので e₁ だけで表現可能

Q2: minBasisCount は単調か？
    - No. ベクトルの順序が定義されていない
    - しかし v ∈ layer(n) ⇒ v ∈ layer(n+1) は成立

Q3: minBasisCount (0, 0) = 0 の意味は？
    - 零ベクトルは基底なしで表現できる（0個の基底の線形結合）
```

##### 3. linearSpanTower の定義（230-256行目）

**最も重要な部分**:
```lean
layer := fun n => {v : Vec2Q | minBasisCount v ≤ n}
```

**この定義の天才性**:
- ✅ 単調性が自明: n ≤ m ⇒ {v | minBasisCount v ≤ n} ⊆ {v | minBasisCount v ≤ m}
- ✅ 被覆性が自明: すべての v に対して v ∈ layer(minBasisCount v)
- ✅ minLayer_mem が自明: minBasisCount v ≤ minBasisCount v
- ✅ minLayer_minimal が自明: v ∈ layer i ⇔ minBasisCount v ≤ i

**視覚化**:
```
layer(0) = {(0,0)}
         ↓
layer(1) = {(0,0), (a,0), (0,b) | a,b ∈ ℚ}
         ↓
layer(2) = ℚ² 全体
```

**演習**:
```lean
-- 1. 以下のベクトルがどの層に属するか判定せよ
example : (0, 0) ∈ linearSpanTower.layer 0 := by sorry
example : (1, 0) ∈ linearSpanTower.layer 1 := by sorry
example : (1, 0) ∈ linearSpanTower.layer 2 := by sorry  -- これも真！
example : (2, 3) ∈ linearSpanTower.layer 1 := by sorry  -- これは偽

-- 2. 層0の特徴付けを完成させよ
example {v : Vec2Q} (hv : v ∈ linearSpanTower.layer 0) :
    v = Vec2Q.zero := by
  -- LinearSpanTower_Integrated.lean 220-238行目参照
  sorry
```

#### Step 2.2: 補題の証明を読む

**補題の役割を理解**:

```lean
-- 143-145行目: 零ベクトルの性質
lemma minBasisCount_zero : minBasisCount Vec2Q.zero = 0
-- → layer(0) の特徴付けに使用

-- 147-149行目: e₁ の性質
lemma minBasisCount_e1 : minBasisCount e₁ = 1
-- → layer(1) の元であることの証明に使用

-- 155-164行目: 一般のベクトル
lemma minBasisCount_general (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    minBasisCount (a, b) = 2
-- → layer(2) が全空間であることの証明に使用
```

**証明のパターンを学ぶ**:
```lean
-- パターン1: 定義展開 + simp
lemma minBasisCount_zero : minBasisCount Vec2Q.zero = 0 := by
  classical
  simp [minBasisCount, Vec2Q.zero]

-- パターン2: 場合分け + 矛盾導出
lemma minBasisCount_general (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    minBasisCount (a, b) = 2 := by
  classical
  have h2 : ¬ (a = 0 ∧ b = 0) := by intro h; exact ha h.left
  have h3 : ¬ (a = 0 ∨ b = 0) := by
    intro h; cases h with
    | inl ha0 => exact ha ha0
    | inr hb0 => exact hb hb0
  simp [minBasisCount, h2, h3]
```

**理解度チェック**:
```
Q1: なぜ classical タクティクが必要か？
    - minBasisCount の定義に if-then-else があるため
    - 排中律を使って場合分けする

Q2: なぜ simp だけで証明が完了するのか？
    - 仮定 h2, h3 により if の条件が決まる
    - simp が自動的に該当する枝を選ぶ

Q3: この証明パターンを他の場合に応用できるか？
    - Yes. 他の座標の場合も同様
```

---

## 📅 Day 6-8: 構造塔の射

### 目標
- 射（morphism）の理解
- minLayer_preserving の意味

### 学習内容

#### Step 3.1: LinearSpanTower_Integrated.lean を読む

**CAT2_complete.lean との違い**:
- Basic.lean: `SimpleTowerWithMin`（簡易版）
- Integrated版: `StructureTowerWithMin`（完全版）
- CAT2: 上記 + 圏構造（Category instance）

**射の定義（81-92行目）**:
```lean
structure StructureTowerWithMin.Hom (T T' : StructureTowerWithMin) where
  map : T.carrier → T'.carrier              -- 基礎写像
  indexMap : T.Index → T'.Index             -- 添字写像
  indexMap_mono : ∀ {i j}, i ≤ j → indexMap i ≤ indexMap j
  layer_preserving : ∀ i x, x ∈ T.layer i → map x ∈ T'.layer (indexMap i)
  minLayer_preserving : ∀ x, T'.minLayer (map x) = indexMap (T.minLayer x)
```

**各フィールドの意味**:

1. **map**: ベクトルの変換
   - 例: `map (3, 5) = (6, 10)`（スカラー倍）

2. **indexMap**: 添字の変換
   - 例: `indexMap n = n`（恒等写像）

3. **indexMap_mono**: 添字写像は順序を保つ
   - n ≤ m ⇒ indexMap n ≤ indexMap m

4. **layer_preserving**: 層を保存
   - v ∈ layer i ⇒ map v ∈ layer (indexMap i)

5. **minLayer_preserving**: **最重要！**
   - minLayer (map v) = indexMap (minLayer v)
   - これが射の一意性を保証

**具体例: スカラー倍（307-318行目）**:
```lean
noncomputable def scalarMultHom (r : ℚ) (hr : r ≠ 0) :
    StructureTowerWithMin.Hom linearSpanTower linearSpanTower where
  map := scalarMultMap r hr              -- v ↦ r·v
  indexMap := id                         -- n ↦ n
  indexMap_mono := by intro i j hij; exact hij
  layer_preserving := by ...
  minLayer_preserving := by ...
```

**なぜ indexMap = id なのか？**:
```
スカラー倍は基底の個数を変えない:
- (a, 0) を 2倍 → (2a, 0) も軸上（layer 1）
- (a, b) を 2倍 → (2a, 2b) も一般位置（layer 2）
- したがって minBasisCount は不変
- ゆえに indexMap = id
```

**理解度チェック**:
```
Q1: なぜ minLayer_preserving が重要なのか？
    - これがないと indexMap が一意に決まらない
    - 例: layer を保存するが minLayer を保存しない写像も考えられる

Q2: scalarMultHom は全射か？単射か？
    - r ≠ 0 なので全単射（同型射）

Q3: 以下は構造塔の射になるか？
    - f(a, b) = (a + b, 0)
    - 答え: No. minLayer を保存しない
      (1, 1) の minLayer は 2 だが f(1,1) = (2, 0) の minLayer は 1
```

**演習**:
```lean
-- 1. ゼロ写像は射になるか？
def zeroMap : Vec2Q → Vec2Q := fun _ => Vec2Q.zero

-- これは射になるか？ならないか？理由は？
-- ヒント: minLayer_preserving をチェック

-- 2. 射の合成
-- scalarMultHom 2 と scalarMultHom 3 の合成は？
example (h2 : (2 : ℚ) ≠ 0) (h3 : (3 : ℚ) ≠ 0) :
    -- 合成を書いてみよ
    sorry
```

---

## 📅 Day 9-11: 位相的視点

### 目標
- 別の閉包作用素での構造塔
- 統一的視点の獲得

### 学習内容

#### Step 4.1: TopologicalClosureTower.lean を読む

**線形包との対比**:

| | 線形包 | 位相的閉包 |
|---|--------|------------|
| 基礎空間 | ℚ² | ExtendedRatSpace |
| 閉包操作 | Span | cl (topological closure) |
| minLayer | 最小基底数 | 初めて閉じる段階 |
| layer(0) | {零ベクトル} | {孤立点} |
| layer(1) | {軸上} | {孤立点 + 極限点} |

**ExtendedRatSpace の定義（190-193行目）**:
```lean
inductive ExtendedRatSpace : Type
  | rational : ℚ → ExtendedRatSpace
  | limitPoint : ExtendedRatSpace
```

**解釈**:
- `rational q`: 有理数点（例: 1/2, 1/3, ...）
- `limitPoint`: 極限点（例: 0）

**閉包レベル（200-202行目）**:
```lean
def extendedClosureLevel : ExtendedRatSpace → ℕ
  | .limitPoint => 1
  | .rational _ => 0
```

**意味**:
- 有理数点: 初めから存在（レベル 0）
- 極限点: 1回の閉包で追加（レベル 1）

**構造塔の構成（205-229行目）**:
```lean
noncomputable def extendedClosureTower : StructureTowerWithMin where
  carrier := ExtendedRatSpace
  layer k := {x | extendedClosureLevel x ≤ k}
  minLayer := extendedClosureLevel
  -- ... 他のフィールド
```

**理解度チェック**:
```
Q1: なぜ有理数のレベルは 0 なのか？
    - 集合 {1/2, 1/3, ...} は既に存在している
    - 閉包操作なしで含まれている

Q2: なぜ極限点のレベルは 1 なのか？
    - 0 は {1/n | n ∈ ℕ} の極限点
    - 1回の閉包操作で追加される

Q3: 2回目の閉包で新しい点は追加されるか？
    - No. {孤立点 + 極限点} は既に閉集合
```

**演習**:
```lean
-- 1. 有限空間での閉包塔
-- n = 5 の場合、各点の閉包レベルを計算せよ
#check finiteClosureTower 5

-- 2. レベルの意味
-- 点 3 の閉包レベルは？
-- ヒント: closureLevel の定義を見よ
example : (finiteClosureTower 5).minLayer (3 : Fin 5) = ? := by
  sorry
```

---

## 📅 Day 12-14: 統一と応用

### 目標
- 閉包作用素の統一的理解
- 他分野への応用

### 学習内容

#### Step 5.1: StructureTowerGuide.lean を読む

**閉包作用素の3公理（再確認）**:
```lean
structure TowerInducingClosure (X : Type) where
  closure : Set X → Set X
  mono : ∀ {S T}, S ⊆ T → closure S ⊆ closure T       -- 単調性
  extensive : ∀ S, S ⊆ closure S                       -- 拡大性
  idempotent : ∀ S, closure (closure S) = closure S    -- 冪等性
```

**具体例での検証**:

##### 線形包
```
closure(S) = Span(S)

単調性: S ⊆ T ⇒ Span(S) ⊆ Span(T)
  証明: S の線形結合 ⊆ T の線形結合

拡大性: S ⊆ Span(S)
  証明: s ∈ S ⇒ s = 1·s ∈ Span(S)

冪等性: Span(Span(S)) = Span(S)
  証明: Span(S) の線形結合 = S の線形結合
```

##### 位相的閉包
```
closure(S) = cl(S) (topological closure)

単調性: S ⊆ T ⇒ cl(S) ⊆ cl(T)
  証明: S の極限点 ⊆ T の極限点

拡大性: S ⊆ cl(S)
  証明: 閉包の定義

冪等性: cl(cl(S)) = cl(S)
  証明: 閉包は閉集合
```

**理解度チェック**:
```
Q1: なぜ冪等性が重要なのか？
    - 閉包を何回取っても同じ
    - minLayer が well-defined

Q2: 単調性がないとどうなるか？
    - 構造塔の monotone が証明できない
    - 階層構造が崩れる

Q3: 他の閉包作用素の例は？
    - 凸包: conv(S) = S の凸結合
    - イデアル: ⟨S⟩ = S で生成されるイデアル
    - 演繹閉包: S から証明可能な命題全体
```

**演習**:
```lean
-- 1. 凸包による構造塔
-- 2次元平面での凸包を定義せよ
def convexHull (S : Set (ℚ × ℚ)) : Set (ℚ × ℚ) :=
  -- S の凸結合全体
  sorry

-- これは閉包作用素の3公理を満たすか？
lemma convexHull_mono : ... := sorry
lemma convexHull_extensive : ... := sorry
lemma convexHull_idempotent : ... := sorry

-- 2. 構造塔を構成せよ
noncomputable def convexHullTower : StructureTowerWithMin where
  carrier := ℚ × ℚ
  layer n := {v | 凸包に必要な頂点数 ≤ n}
  -- ...
  sorry
```

#### Step 5.2: CAT2_StructureTower_解説.pdf を読む

**普遍性の理解**:

自由構造塔 F(X) の普遍性:
```
任意の単調写像 f : X → T.carrier に対して
一意的な射 φ : F(X) → T が存在
```

**具体例での確認**:
```lean
-- linearSpanTower は自由構造塔か？
-- 部分的に yes:
-- - ℚ² の標準基底 {e₁, e₂} から生成
-- - 任意の線形写像が射を誘導
```

**理解度チェック**:
```
Q1: 普遍性の「一意性」はどこから来るのか？
    - minLayer_preserving により indexMap が決まる
    - indexMap が決まると map も決まる（線形性より）

Q2: 直積の普遍性は？
    - T₁ × T₂ への射 = T₁ への射 + T₂ への射

Q3: 忘却関手とは？
    - 構造塔 → その基礎集合
    - 構造を「忘れる」写像
```

---

## 📅 Day 15+: 応用と発展

### プロジェクト例

#### プロジェクト1: 3次元への拡張
```lean
-- 目標: ℚ³ での構造塔を実装
def Vec3Q : Type := ℚ × ℚ × ℚ

noncomputable def minBasisCount3 (v : Vec3Q) : ℕ :=
  -- v.1, v.2, v.3 が何個非零か？
  sorry

noncomputable def linearSpanTower3 : StructureTowerWithMin where
  carrier := Vec3Q
  layer n := {v | minBasisCount3 v ≤ n}
  -- ...
```

#### プロジェクト2: 確率論への応用
```lean
-- 目標: 離散時間フィルトレーションを構造塔で記述
structure DiscreteFilteredSpace where
  Ω : Type                           -- 標本空間
  ℱ : ℕ → Set (Set Ω)              -- σ-代数の増加列
  measurable : ∀ n, IsMeasurable (ℱ n)
  increasing : ∀ n, ℱ n ⊆ ℱ (n + 1)

-- これを StructureTowerWithMin として定式化
```

#### プロジェクト3: グラフの到達可能性
```lean
-- 目標: グラフの n ステップ到達可能性を構造塔で記述
structure Graph where
  V : Type                           -- 頂点集合
  E : V → V → Prop                   -- 辺関係

def reachableInN (G : Graph) (n : ℕ) (v : G.V) : Set G.V :=
  {w | n ステップで v から w へ到達可能}

-- これを使って構造塔を構成
```

---

## 🎯 最終チェックリスト

### Level 1: 基礎 ✓
- [ ] 構造塔の定義を理解
- [ ] minLayer の意味を理解
- [ ] Basic.lean が読める
- [ ] 簡単な計算ができる

### Level 2: 統合 ✓
- [ ] 射の定義を理解
- [ ] minLayer_preserving の重要性を理解
- [ ] scalarMultHom を構成できる
- [ ] 層の特徴付けができる

### Level 3: 一般化 ✓
- [ ] 閉包作用素の3公理を理解
- [ ] 異なる閉包での構造塔を比較できる
- [ ] 新しい閉包作用素を実装できる
- [ ] 応用分野への展開を構想できる

---

## 📚 追加リソース

### オンラインリソース
- Lean Zulip: https://leanprover.zulipchat.com/
- Mathlib Docs: https://leanprover-community.github.io/mathlib4_docs/

### 推薦図書
1. **入門**: "Theorem Proving in Lean 4"
2. **線形代数**: Axler, "Linear Algebra Done Right"
3. **圏論**: Leinster, "Basic Category Theory"
4. **位相**: Munkres, "Topology"

### コミュニティ
- GitHub Issues で質問
- Zulip で議論
- Pull Request で貢献

---

## 🚀 次のステップ

このガイドを完了したら：

1. **自分の例を作る**: 興味のある分野で構造塔を実装
2. **証明を完成させる**: sorry の部分を埋める
3. **発表する**: 学んだことをブログや勉強会で共有
4. **貢献する**: Mathlib への貢献を検討

---

**おめでとうございます！構造塔理論の旅を始める準備が整いました。**

一歩ずつ、確実に進んでいきましょう。わからないことがあれば、いつでもコミュニティに質問してください。
