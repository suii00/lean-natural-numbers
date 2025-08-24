## 課題2：代数構造論

### 数学分野

**群の同型定理（第一同型定理）**

### ブルバキ的アプローチ

群を集合と演算の組として公理的に定義し、準同型写像を構造を保つ写像として特徴づける。商群の構成は同値関係による集合の分割から自然に導出される。

### Lean言語での定理記述

```
-- 群の公理的定義（ブルバキ第1巻第3章）
class Group (G : Type*) extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  mul_one : ∀ a : G, a * 1 = a
  mul_left_inv : ∀ a : G, a⁻¹ * a = 1

-- 群準同型
structure GroupHom (G H : Type*) [Group G] [Group H] where
  toFun : G → H
  map_mul' : ∀ a b : G, toFun (a * b) = toFun a * toFun b

-- 核の定義
def GroupHom.ker {G H : Type*} [Group G] [Group H] (f : GroupHom G H) : Set G :=
  {g : G | f.toFun g = 1}

-- 第一同型定理
theorem first_isomorphism_theorem {G H : Type*} [Group G] [Group H]
    (f : GroupHom G H) :
    Nonempty (GroupIso (G ⧸ f.ker) (Set.range f.toFun)) := by
  sorry

```

### 集合論的基盤

- 同値関係による集合の分割
- 写像の単射性・全射性
- 像と逆像の対応関係

### 証明戦略

1. 商群の well-defined 性を示す
2. 自然な同型写像を構成
3. 逆写像の存在を示す

### 関連する数学原論の章

- 第1巻第2章「写像」
- 第1巻第3章「代数構造」

### 現代数学への応用例

ガロア理論、代数幾何の基本群、表現論