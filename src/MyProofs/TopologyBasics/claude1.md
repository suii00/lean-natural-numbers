# ブルバキ流集合論・写像理論 Lean証明課題集（学部レベル）

## 課題1：一般位相論

### 数学分野

**一般位相空間における連続写像の合成定理**

### ブルバキ的アプローチ

位相空間を開集合系による公理的定義から構築し、連続写像を逆像による集合論的特徴づけで定義する。合成の結合律は写像の合成の一般的性質から自然に導出される。

### Lean言語での定理記述

```
-- 位相空間の定義（ブルバキ第3巻第1章）
structure TopologicalSpace (X : Type*) where
  IsOpen : Set X → Prop
  isOpen_univ : IsOpen Set.univ
  isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  isOpen_sUnion : ∀ S, (∀ s ∈ S, IsOpen s) → IsOpen (⋃₀ S)

-- 連続写像の定義
def Continuous {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  ∀ U, TopologicalSpace.IsOpen U → TopologicalSpace.IsOpen (f ⁻¹' U)

-- 証明すべき定理
theorem continuous_comp {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous (g ∘ f) := by
  sorry

```

### 集合論的基盤

- 逆像の性質：`(g ∘ f)⁻¹' = f⁻¹' ∘ g⁻¹'`
- 開集合の定義による位相構造
- 写像の合成における結合律

### 証明戦略

1. 連続性の定義を展開
2. 合成写像の逆像を分解
3. 各写像の連続性を順次適用

### 関連する数学原論の章

- 第1巻第2章「写像」
- 第3巻第1章「位相構造」

### 現代数学への応用例

関数解析における作用素の連続性、微分幾何の滑らかな写像