## 課題4：測度論基礎

### 数学分野

**σ-代数の性質と可測写像の合成**

### ブルバキ的アプローチ

σ-代数を集合の族の抽象的性質として公理的に定義し、可測写像を構造を保つ写像として特徴づける。測度論は集合論と位相論の自然な拡張である。

### Lean言語での定理記述

```
-- σ-代数の定義
structure MeasurableSpace (Ω : Type*) where
  MeasurableSet : Set Ω → Prop
  measurableSet_empty : MeasurableSet ∅
  measurableSet_compl : ∀ s, MeasurableSet s → MeasurableSet sᶜ
  measurableSet_iUnion : ∀ f : ℕ → Set Ω,
    (∀ i, MeasurableSet (f i)) → MeasurableSet (⋃ i, f i)

-- 可測写像
def Measurable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (f : Ω₁ → Ω₂) : Prop :=
  ∀ s, MeasurableSpace.MeasurableSet s →
    MeasurableSpace.MeasurableSet (f ⁻¹' s)

-- 可測写像の合成定理
theorem measurable_comp {Ω₁ Ω₂ Ω₃ : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
    {f : Ω₁ → Ω₂} {g : Ω₂ → Ω₃}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (g ∘ f) := by
  sorry

```

### 集合論的基盤

- De Morganの法則
- 可算無限操作の性質
- 逆像と集合演算の可換性

### 証明戦略

1. 可測性の定義を展開
2. 合成の逆像公式を適用
3. 各写像の可測性を利用

### 関連する数学原論の章

- 第1巻第2章「写像」
- 第3巻第9章「測度の使用」

### 現代数学への応用例

確率論、実解析、調和解析