# 計算可能な構造塔の実装 - 完全版サマリー

## ファイル構成: `DecidableStructureTower_Examples.lean` (907行)

本ファイルは、Bourbakiの構造理論に基づく構造塔（StructureTowerWithMin）の
**完全に形式化された計算可能な実装例**を提供します。

---

## 🎯 主要な追加機能

### 1. **HomLe の導入** (行 151-199)

```lean
structure HomLe (T T' : StructureTowerWithMin) where
  map : T.carrier → T'.carrier
  indexMap : T.Index → T'.Index
  indexMap_mono : ∀ {i j}, i ≤ j → indexMap i ≤ indexMap j
  layer_preserving : ∀ {x i}, x ∈ T.layer i → map x ∈ T'.layer (indexMap i)
  minLayer_le : ∀ x, T'.minLayer (map x) ≤ indexMap (T.minLayer x)
```

**動機**: 
- 通常の射（Hom）は `minLayer` の完全な一致を要求: `T'.minLayer (map x) = indexMap (T.minLayer x)`
- しかし、整数の加法 `k ↦ k + a` や多項式の加法 `(p,q) ↦ p + q` は上限のみを保存
- HomLe は上限 `≤` のみを要求し、より多くの自然な写像を捉える

**応用例**:
- `intAddHomLe a`: 整数の平行移動 `k ↦ k + a`
- `polyAddHomLe`: 多項式の加法 `(p, q) ↦ p + q`
- `polyMulHomLe`: 多項式の乗法 `(p, q) ↦ p * q`
- `polyZeroHomLe`: 零写像 `p ↦ 0`

### 2. **圏論的性質の完全な証明** (行 92-138)

```lean
-- 外延性
@[ext] theorem Hom.ext {T T'} (f g : Hom T T') : ...

-- 結合律
@[simp] lemma Hom.comp_assoc : Hom.comp h₃ (Hom.comp h₂ h₁) = ...

-- 単位律
@[simp] lemma Hom.id_comp (f : Hom T₁ T₂) : Hom.comp (Hom.id T₂) f = f
@[simp] lemma Hom.comp_id (f : Hom T₁ T₂) : Hom.comp f (Hom.id T₁) = f
```

**意義**: 構造塔が真に圏をなすことの形式的証明

---

## 📚 実装された構造塔（5つ）

### 例1: 整数塔 `intAbsTower` (行 250-283)
- **基礎集合**: ℤ
- **添字集合**: ℕ
- **層**: `layer n = {k : ℤ | |k| ≤ n}`
- **minLayer**: `k ↦ |k|`
- **計算可能**: 完全に `#eval` 可能

**実装された射**:
1. `intAbsTowerDouble`: 倍数写像 `k ↦ 2k`
2. `intAbsTowerDiag`: 対角射 `k ↦ (k, k)`
3. `intAddHomLe a`: 平行移動 `k ↦ k + a` (HomLe)

**計算例**:
```lean
#eval intAbsTower.minLayer (-3)          -- 3
#eval intAbsTowerDouble.map (5)          -- 10
#eval (intAddHomLe 3).map (-2)           -- 1
```

### 例2: リスト塔 `listLengthTower` (行 448-495)
- **基礎集合**: List ℕ
- **添字集合**: ℕ
- **層**: `layer n = {l : List ℕ | l.length ≤ n}`
- **minLayer**: `l ↦ l.length`
- **計算可能**: 完全に `#eval` 可能

**理論的性質**:
```lean
lemma listLengthTower_cons (a : ℕ) (l : List ℕ) :
    minLayer (a :: l) = minLayer l + 1

lemma listLengthTower_append (l₁ l₂ : List ℕ) :
    minLayer (l₁ ++ l₂) = minLayer l₁ + minLayer l₂
```

### 例3: 有限集合塔 `finsetCardTower` (行 524-563)
- **基礎集合**: Finset ℕ
- **添字集合**: ℕ
- **層**: `layer n = {S : Finset ℕ | S.card ≤ n}`
- **minLayer**: `S ↦ S.card`
- **計算可能**: 完全に `#eval` 可能

**計算例**:
```lean
#eval finsetCardTower.minLayer ({1, 2, 3} : Finset ℕ)   -- 3
#eval checkFinsetLayer ({1, 2} : Finset ℕ) 1            -- false
```

### 例4: 多項式塔 `polyDegreeTower` (行 600-797)
- **基礎集合**: Polynomial ℚ
- **添字集合**: ℕ
- **層**: `layer n = {p : Polynomial ℚ | p.natDegree ≤ n}`
- **minLayer**: `p ↦ p.natDegree`
- **計算可能性**: noncomputable（次数の計算のため）

**理論的境界補題**:
```lean
theorem poly_add_natDegree_le (p q : Polynomial ℚ) :
    (p + q).natDegree ≤ max p.natDegree q.natDegree

theorem poly_mul_natDegree_le (p q : Polynomial ℚ) :
    (p * q).natDegree ≤ p.natDegree + q.natDegree
```

**実装された射**:
1. `polySmulHom c`: 非零スカラー倍 `p ↦ c · p` (同型射)
2. `polyAddHomLe`: 加法 `(p, q) ↦ p + q` (HomLe)
3. `polyMulHomLe`: 乗法 `(p, q) ↦ p * q` (HomLe)
4. `polyZeroHomLe`: 零写像 `p ↦ 0` (HomLe)

**モノイド準同型性**:
```lean
@[simp] lemma polySmulHom_comp (c d : Units ℚ) :
    polySmulHom (c * d) = Hom.comp (polySmulHom c) (polySmulHom d)

@[simp] lemma polySmulHom_one :
    polySmulHom 1 = Hom.id polyDegreeTower
```

### 例5: 文字列塔 `stringLengthTower` (行 840-867)
- **基礎集合**: String
- **添字集合**: ℕ
- **層**: `layer n = {s : String | s.length ≤ n}`
- **minLayer**: `s ↦ s.length`
- **計算可能**: 完全に `#eval` 可能

**計算例**:
```lean
#eval stringLengthTower.minLayer "hello"        -- 5
#eval checkStringLayer "lean" 4                 -- true
```

---

## 🔑 重要な理論的補題

### 基本補題（StructureTowerWithMin namespace内、行 64-80）

```lean
-- minLayerの一意性
lemma minLayer_unique (T : StructureTowerWithMin) (x : T.carrier) (i : T.Index)
    (hi : x ∈ T.layer i) (hmin : ∀ k, x ∈ T.layer k → i ≤ k) :
    i ≤ T.minLayer x ∧ T.minLayer x ≤ i

-- minLayerの特徴付け
lemma minLayer_le_iff (T : StructureTowerWithMin) (x : T.carrier) (i : T.Index) :
    T.minLayer x ≤ i ↔ x ∈ T.layer i
```

これらは**演習問題1, 2の解答**として機能します。

---

## 💡 教育的価値

### 演習問題との対応

| 演習 | 対応する実装 | 行番号 |
|------|------------|--------|
| 1. minLayerの一意性 | `minLayer_unique` | 67-71 |
| 2. 単調性の特徴付け | `minLayer_le_iff` | 74-80 |
| 3. 倍数写像 | `intAbsTowerDouble` | 385-405 |
| 4. 加法射 | `intAddHomLe`, `polyAddHomLe` | 340-354, 742-771 |
| 5. 多項式塔 | `polyDegreeTower` | 600-625 |
| 6. 同型射 | `polySmulHom` | 690-709 |
| 7. 計算量解析 | コメントで詳述 | - |

### 計算量の解析

各塔の `minLayer` の計算量:

| 塔 | 計算量 | 理由 |
|----|--------|------|
| `intAbsTower` | O(1) | `natAbs`は符号の単純な場合分け |
| `listLengthTower` | O(n) | リスト全体を走査（キャッシュなしの場合） |
| `finsetCardTower` | O(1) | 濃度は通常キャッシュされる |
| `polyDegreeTower` | O(1) | 次数は多項式表現に含まれる |
| `stringLengthTower` | O(n) | 文字列全体を走査 |

---

## 🚀 発展的な機能

### 1. HomからHomLeへの忘却関手（行 166-174）

```lean
def Hom.toHomLe {T T' : StructureTowerWithMin} (h : Hom T T') : HomLe T T'
```

すべての完全な射は自動的にHomLeでもある。

### 2. 直積構造（StructureTowerWithMin namespace内）

```lean
def prod (T₁ T₂ : StructureTowerWithMin) : StructureTowerWithMin
```

2つの構造塔の直積を成分ごとに構成。

### 3. 型安全な層判定ヘルパー

```lean
def checkInLayer (tower : StructureTowerWithMin)
    (x : tower.carrier) (i : tower.Index)
    [Decidable (x ∈ tower.layer i)] : Bool
```

計算可能な層の包含判定。

---

## 📊 統計

| 項目 | 数 |
|------|-----|
| 総行数 | 907 |
| 構造塔の例 | 5個 |
| 完全な射（Hom） | 4個 |
| 上限保存射（HomLe） | 5個 |
| 理論的補題 | 10個以上 |
| #eval計算例 | 30個以上 |

---

## 🎓 学習の道筋

### レベル1: 基礎理解
1. `intAbsTower`と`listLengthTower`の定義を読む
2. `#eval`例を実行して計算可能性を確認
3. `minLayer_unique`と`minLayer_le_iff`の証明を理解

### レベル2: 射の理解
1. `intAbsTowerDouble`の実装を読む
2. `minLayer_preserving`条件の重要性を理解
3. `intAddHomLe`でHomLeの必要性を確認

### レベル3: 圏論的視点
1. `Hom.comp`の実装と結合律を確認
2. `Hom.ext`による外延性の意味を理解
3. `prod`による直積の構成を学ぶ

### レベル4: 多項式塔の深い理解
1. `polySmulHom`のモノイド準同型性を確認
2. `polyAddHomLe`と`polyMulHomLe`の境界の意味を理解
3. なぜ零写像は通常のHomではないかを考察

---

## 💻 実装の品質

### ビルド状態
- ✅ `lake build`成功
- ✅ すべての定義はsorryなし
- ✅ Mathlibのみに依存

### 計算可能性
- ✅ 整数塔: 完全に計算可能
- ✅ リスト塔: 完全に計算可能
- ✅ 有限集合塔: 完全に計算可能
- ✅ 文字列塔: 完全に計算可能
- ⚠️ 多項式塔: noncomputable（本質的制約）

### 形式化の完全性
- ✅ すべての公理が証明済み
- ✅ 圏論的性質の完全な証明
- ✅ 具体例での検証

---

## 🔮 今後の拡張可能性

### 追加可能な構造塔
1. **有理数塔**: 分母による階層
2. **グラフ塔**: 頂点数や辺数による階層
3. **論理式塔**: ネストの深さによる階層

### 理論的発展
1. **極限と余極限**: 構造塔の圏での普遍構成
2. **随伴関手**: 自由-忘却随伴の完全な証明
3. **モナド構造**: 構造塔上のモナドの研究

### 教育的応用
1. 学部生向けの圏論入門教材
2. 形式数学の実践的ガイド
3. Bourbaki構造理論の現代的解釈

---

## 📝 引用と参考文献

このファイルは以下の文献の精神に基づいています：

1. Nicolas Bourbaki, *Éléments de mathématique: Théorie des ensembles*
2. Saunders Mac Lane, *Categories for the Working Mathematician*
3. The mathlib Community, *The Lean Mathematical Library*

---

## ✍️ 著者とライセンス

- **著者**: Su（構造塔理論研究プロジェクト）
- **生成支援**: Claude Code
- **ライセンス**: このドキュメントはファイルと同じライセンスに従います

---

**最終更新**: 2025年11月24日
**バージョン**: 完全版（907行）
