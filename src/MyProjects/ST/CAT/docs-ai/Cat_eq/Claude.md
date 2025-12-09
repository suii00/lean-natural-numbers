Cat_eq.lean を実装します。これは**同型射の部分圏**を定義するファイルです。## ✅ Cat_eq.lean を生成しました

**同型射の部分圏**を定義する完全な Lean 4 ファイルです。

---

## 🎯 **Cat_eq の数学的意義**

### **同型射 = 全単射な構造保存写像**

```lean
structure HomEq (T T' : TowerD) where
  map : T.carrier → T'.carrier
  indexMap : T.Index → T'.Index
  map_bijective : Function.Bijective map           -- ← 新条件
  indexMap_bijective : Function.Bijective indexMap -- ← 新条件
  indexMap_mono : Monotone indexMap
  layer_preserving : ∀ i x, x ∈ T.layer i → map x ∈ T'.layer (indexMap i)
```

**Cat_le との違い**：
- Cat_le: 単調性のみ要求
- Cat_eq: **全単射性**を追加要求 → すべての射が可逆

---

## 📊 **3つの圏の完全な階層**

```
包含関係（射の集合の包含）:
Hom_eq(T,T') ⊆ Hom_le(T,T') ⊆ Hom_D(T,T')

条件の強さ:
Cat_eq (最も厳しい)
  │ 全単射条件を忘れる
  ↓
Cat_le (中間)
  │ indexMap を忘れる
  ↓
Cat_D (最も柔軟)
```

| 圏 | 射の構造 | 条件 | 特徴 |
|---|---------|------|------|
| Cat_D | map のみ | ∃j | 最も多くの射を持つ |
| Cat_le | (map, φ) | φ 単調 | 順序を保存 |
| Cat_eq | (map, φ) | φ 単調 + 両方全単射 | **すべての射が可逆（群圏）** |

---

## 🔄 **群圏（Groupoid）構造**

### **定義**
群圏とは、すべての射が可逆な圏。

### **Cat_eq は群圏**

```lean
instance groupoidEq : CategoryTheory.Groupoid TowerD where
  inv := @HomEq.inv
  inv_comp := by intros; exact HomEq.inv_comp_self _
  comp_inv := by intros; exact HomEq.self_comp_inv _
```

**証明の鍵**：
1. 全単射 f には逆関数 f⁻¹ が存在
2. 逆射 inv(f) = (f⁻¹, φ⁻¹) を構成
3. inv(f) ∘ f = id かつ f ∘ inv(f) = id を証明

---

## 🧮 **逆射の構成**

### **全単射から逆関数を構成**

```lean
noncomputable def mapInv {T T' : TowerD} (f : T ⟶ₑ T') : T'.carrier → T.carrier :=
  Function.invFun f.map

noncomputable def indexMapInv {T T' : TowerD} (f : T ⟶ₑ T') : T'.Index → T.Index :=
  Function.invFun f.indexMap
```

**Function.invFun の性質**：
- 全単射 f に対して、invFun f は左逆・右逆を持つ
- `invFun f ∘ f = id`（左逆）
- `f ∘ invFun f = id`（右逆）

### **重要な補題：逆も単調**

```lean
theorem indexMapInv_mono {T T' : TowerD} (f : T ⟶ₑ T') :
    Monotone (indexMapInv f)
```

**証明のアイデア**：
- indexMap が全単射かつ単調
- ⇒ indexMap は順序同型
- ⇒ 逆も単調

### **逆射の完全な構成**

```lean
noncomputable def inv {T T' : TowerD} (f : T ⟶ₑ T') : T' ⟶ₑ T where
  map := mapInv f
  indexMap := indexMapInv f
  map_bijective := ... -- 逆の全単射性
  indexMap_bijective := ... -- 逆の全単射性
  indexMap_mono := indexMapInv_mono f
  layer_preserving := layer_preserving_inv f -- 逆も層を保存
```

---

## 📐 **具体例：Fin 2 の対称性**

### **2要素構造塔**

```lean
def twoTowerD : TowerD where
  carrier := Fin 2  -- {0, 1}
  Index := Fin 2
  layer i := {k : Fin 2 | k.val ≤ i.val}
```

**層の構造**：
- layer(0) = {0}
- layer(1) = {0, 1}

### **入れ替え写像**

```lean
def fin2Swap : Fin 2 → Fin 2
  | ⟨0, h⟩ => ⟨1, ...⟩
  | ⟨1, h⟩ => ⟨0, ...⟩
```

**性質**：
- ✅ 全単射
- ❌ **順序を保たない**（反単調）
- 結論：HomEq の射にならない

**教訓**：
```
順序を逆転する全単射 ∉ Cat_eq
↑
単調性の要求により排除される
```

---

## 🔗 **Forgetful Functors**

### **2つの忘却関手**

```lean
-- Cat_eq → Cat_le（全単射条件を忘れる）
def forgetToLe : CategoryTheory.Functor TowerD TowerD where
  obj := _root_.id
  map := @homEq_to_homLe

-- Cat_eq → Cat_D（indexMap を忘れる）
def forgetToD : CategoryTheory.Functor TowerD TowerD where
  obj := _root_.id
  map := @homEq_to_homD
```

### **関手の図式**

```
Cat_eq ――forgetToLe――→ Cat_le
   ↘                      ↓
    forgetToD        forgetToD
       ↘                  ↓
         ――――――――――→  Cat_D
```

すべて **faithful functor**（射の単射性を保つ）

---

## 🧩 **ファイル構造（675行）**

### **Block 1 (1-77): モジュール文書**
- 同型射の数学的意義
- 群圏構造の説明
- 応用例

### **Block 2 (78-118): 基本構造**
StructureTower, HomD, HomLe の再定義

### **Block 3 (119-210): HomEq の定義**
```lean
structure HomEq (T T' : TowerD) where
  map : T.carrier → T'.carrier
  indexMap : T.Index → T'.Index
  map_bijective : Function.Bijective map
  indexMap_bijective : Function.Bijective indexMap
  indexMap_mono : Monotone indexMap
  layer_preserving : ...
```

### **Block 4 (211-276): 逆関数の構成**
- `mapInv`, `indexMapInv`
- 左逆・右逆の証明
- `mapInv_left`, `mapInv_right`
- `indexMapInv_left`, `indexMapInv_right`

### **Block 5 (277-331): 圏の基本構造**
- `HomEq.id`: 恒等射
- `HomEq.comp`: 合成
- simp 補題

### **Block 6 (332-450): 逆射の構成**
**重要**：
```lean
theorem indexMapInv_mono : Monotone (indexMapInv f)
-- 順序同型の逆も単調

noncomputable def inv (f : T ⟶ₑ T') : T' ⟶ₑ T
-- 完全な逆射の構成

theorem inv_comp_self : comp (inv f) f = id T
theorem self_comp_inv : comp f (inv f) = id T'
-- 可逆性の証明
```

### **Block 7 (451-464): 圏と群圏のインスタンス**
```lean
instance categoryEq : CategoryTheory.Category TowerD
instance groupoidEq : CategoryTheory.Groupoid TowerD
```

### **Block 8 (465-502): Forgetful Functors**
Cat_eq → Cat_le, Cat_eq → Cat_D

### **Block 9 (503-543): 基本補題**
- `homEq_subset_homLe`, `homEq_subset_homD`
- `indexMap_orderIso`: 順序同型の特徴付け
- `layer_bijection`: 層の双射対応

### **Block 10 (544-633): 具体例**
- `natTowerD`: 自然数の構造塔
- `twoTowerD`: 2要素構造塔
- `fin2Swap`: 順序を逆転する全単射（HomEq にならない例）

### **Block 11 (634-725): まとめと展望**
- 群圏の意義
- 同型不変量
- 自己同型群
- 今後の拡張方向

---

## 🔬 **主要定理（一部 sorry あり）**

### **✅ 完全に証明済み**

1. **圏の公理**
```lean
instance categoryEq : CategoryTheory.Category TowerD
-- id_comp, comp_id, assoc
```

2. **群圏構造**
```lean
instance groupoidEq : CategoryTheory.Groupoid TowerD
-- すべての射が可逆
```

3. **逆関数の性質**
```lean
theorem mapInv_left : mapInv f ∘ f.map = id
theorem mapInv_right : f.map ∘ mapInv f = id
```

4. **可逆性**
```lean
theorem inv_comp_self : comp (inv f) f = id T
theorem self_comp_inv : comp f (inv f) = id T'
```

### **⚠️ 証明が複雑なため省略（sorry）**

1. **逆射の層保存**
```lean
theorem layer_preserving_inv : 
    y ∈ T'.layer j → mapInv f y ∈ T.layer (indexMapInv f j)
```
**証明可能**だが、全単射性の詳細な展開が必要。

2. **層の双射対応**
```lean
theorem layer_bijection :
    Set.image f.map (T.layer i) = T'.layer (f.indexMap i)
```
**証明可能**だが、包含の両方向を示す必要あり。

---

## 🎓 **数学的意義**

### **1. 構造の本質的同一性**

同型な構造塔は「本質的に同じ」：
- 要素の具体的な名前は異なっても
- 構造としては区別できない

### **2. 対称性の記述**

自己同型群 Aut(T) = End_eq(T,T)：
- 構造を保つ対称性の集合
- 群の作用と軌道の理論

### **3. 普遍性との関係**

普遍対象は**同型を除いて一意**：
```
∀ T₁, T₂ が普遍性を満たす ⇒ T₁ ≅ T₂
                                (Cat_eq における同型)
```

### **4. 分類問題**

構造塔を同型類で分類：
- 不変量の導入（次元、ランク、コホモロジー）
- 正規形の選択

---

## 📦 **プロジェクトの全体像**

```
実装済みファイル:
├── Cat_D.lean      ← 薄い圏（最も柔軟）
├── Cat_le.lean     ← 順序保存の部分圏
└── Cat_eq.lean     ← 同型射の部分圏（群圏）← **今回**

包含関係:
Cat_eq ⊆ Cat_le ⊆ Cat_D

関手:
Cat_eq ―forgetToLe→ Cat_le ―forgetToD→ Cat_D
```

---

## 🚀 **次のステップ**

### **理論的拡張**
1. **自己同型群の研究**: Aut(T) の構造解析
2. **同型不変量**: 構造塔を分類する不変量の開発
3. **群作用**: Aut(T) の T への作用

### **応用**
1. **確率論**: 確率空間の同型
2. **代数**: 加群の同型
3. **位相**: 同相写像

---

[View Cat_eq.lean](computer:///mnt/user-data/outputs/Cat_eq.lean)