# prodUniversal_unique の証明可能性分析

## 問題の定式化

```lean
lemma prodUniversal_unique {T T₁ T₂ : StructureTower} 
    (f₁ : T ⟶ T₁) (f₂ : T ⟶ T₂)
    (g : T ⟶ prod T₁ T₂) 
    (h₁ : g ≫ proj₁ T₁ T₂ = f₁) 
    (h₂ : g ≫ proj₂ T₁ T₂ = f₂) :
    g = prodUniversal f₁ f₂
```

**目標:** `g` と `prodUniversal f₁ f₂` が等しいことを示す

**必要な等式:**
1. `g.map = (prodUniversal f₁ f₂).map`  ← これは証明可能
2. `g.indexMap = (prodUniversal f₁ f₂).indexMap`  ← これが問題

---

## 部分的証明：基礎写像の等式

### 証明可能な部分

```lean
lemma prodUniversal_unique_map {T T₁ T₂ : StructureTower} 
    (f₁ : T ⟶ T₁) (f₂ : T ⟶ T₂)
    (g : T ⟶ prod T₁ T₂) 
    (h₁ : g ≫ proj₁ T₁ T₂ = f₁) 
    (h₂ : g ≫ proj₂ T₁ T₂ = f₂) :
    g.map = (prodUniversal f₁ f₂).map := by
  funext x
  -- g.map x : T₁.carrier × T₂.carrier
  -- これを ⟨f₁.map x, f₂.map x⟩ と等しいことを示す
  
  -- Step 1: (g.map x).1 = f₁.map x を示す
  have h1_map : (g.map x).1 = f₁.map x := by
    have : (g ≫ proj₁ T₁ T₂).map = f₁.map := by
      rw [h₁]
    exact congrFun this x
  
  -- Step 2: (g.map x).2 = f₂.map x を示す  
  have h2_map : (g.map x).2 = f₂.map x := by
    have : (g ≫ proj₂ T₁ T₂).map = f₂.map := by
      rw [h₂]
    exact congrFun this x
  
  -- Step 3: 組み合わせる
  exact Prod.ext h1_map h2_map
```

**結論:** 基礎写像の等式は **完全に証明可能** ✅

---

## 困難な部分：indexMap の等式

### 問題の詳細

```lean
-- 示すべきこと:
g.indexMap = (prodUniversal f₁ f₂).indexMap

-- つまり、∀ i : T.Index,
g.indexMap i = ⟨f₁.indexMap i, f₂.indexMap i⟩
```

### なぜ困難か

**既知の情報:**
1. `h₁ : g ≫ proj₁ T₁ T₂ = f₁`
2. `h₂ : g ≫ proj₂ T₁ T₂ = f₂`

**これから導けること:**
- `(g ≫ proj₁).map = f₁.map` ← map について
- `(g ≫ proj₁).indexMap = f₁.indexMap` ← indexMap について

つまり：
```lean
Prod.fst ∘ g.indexMap = f₁.indexMap  -- h₁ から
Prod.snd ∘ g.indexMap = f₂.indexMap  -- h₂ から
```

### 一見証明できそうだが...

**直観的な議論:**
```
g.indexMap i = ⟨a, b⟩ とする（ある a : T₁.Index, b : T₂.Index）

h₁ から: Prod.fst (g.indexMap i) = f₁.indexMap i
        よって a = f₁.indexMap i

h₂ から: Prod.snd (g.indexMap i) = f₂.indexMap i
        よって b = f₂.indexMap i

したがって: g.indexMap i = ⟨f₁.indexMap i, f₂.indexMap i⟩
```

**この議論は正しい！**

### 実際の証明

```lean
lemma prodUniversal_unique {T T₁ T₂ : StructureTower} 
    (f₁ : T ⟶ T₁) (f₂ : T ⟶ T₂)
    (g : T ⟶ prod T₁ T₂) 
    (h₁ : g ≫ proj₁ T₁ T₂ = f₁) 
    (h₂ : g ≫ proj₂ T₁ T₂ = f₂) :
    g = prodUniversal f₁ f₂ := by
  ext
  
  -- Part 1: g.map = (prodUniversal f₁ f₂).map
  · funext x
    have h1_map := congrArg (·.map) h₁
    have h2_map := congrArg (·.map) h₂
    simp only at h1_map h2_map
    have : (g.map x).1 = f₁.map x := congrFun h1_map x
    have : (g.map x).2 = f₂.map x := congrFun h2_map x
    exact Prod.ext ‹_› ‹_›
  
  -- Part 2: g.indexMap = (prodUniversal f₁ f₂).indexMap
  · funext i
    have h1_idx := congrArg (·.indexMap) h₁
    have h2_idx := congrArg (·.indexMap) h₂
    simp only at h1_idx h2_idx
    have : (g.indexMap i).1 = f₁.indexMap i := congrFun h1_idx i
    have : (g.indexMap i).2 = f₂.indexMap i := congrFun h2_idx i
    exact Prod.ext ‹_› ‹_›
```

---

## 結論：証明可能！

### 証明の鍵

**重要な観察:**
射の合成 `g ≫ proj₁ = f₁` は：
- `(g ≫ proj₁).map = f₁.map` **かつ**
- `(g ≫ proj₁).indexMap = f₁.indexMap`

を意味する（射の等式の定義から）。

**直積の場合の特殊性:**
- 直積型 `T₁.Index × T₂.Index` では、
- 射影 `Prod.fst` と `Prod.snd` が対を一意に決定する
- したがって indexMap の一意性も成り立つ

### freeStructureTower_universal との違い

| 問題 | 状況 | 証明可能性 |
|------|------|------------|
| **freeStructureTower** | 各 f(x) が複数の層に属しうる | ❌ 一意性なし |
| **prodUniversal** | 直積の射影が indexMap を制約 | ✅ 一意性あり |

**なぜ違いが生じるか:**

1. **freeStructureTower の場合:**
   ```
   f(x) ∈ T.layer i
   f(x) ∈ T.layer j  (i ≠ j も可能)
   
   → indexMap(x) = i でも j でも条件を満たす
   ```

2. **prodUniversal の場合:**
   ```
   h₁: (g ≫ proj₁).indexMap = f₁.indexMap
   h₂: (g ≫ proj₂).indexMap = f₂.indexMap
   
   → g.indexMap = ⟨f₁.indexMap, f₂.indexMap⟩ と一意に決まる
   ```

---

## 実装可能な完全証明

```lean
import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Mathlib.CategoryTheory.Category.Basic

-- [前の定義は省略]

lemma prodUniversal_unique {T T₁ T₂ : StructureTower.{u, v}} 
    (f₁ : T ⟶ T₁) (f₂ : T ⟶ T₂)
    (g : T ⟶ prod T₁ T₂) 
    (h₁ : g ≫ proj₁ T₁ T₂ = f₁) 
    (h₂ : g ≫ proj₂ T₁ T₂ = f₂) :
    g = prodUniversal f₁ f₂ := by
  -- 射の等式は成分ごとに示す
  apply StructureTower.Hom.ext
  
  -- Part 1: map の等式
  · funext x
    -- g.map x と ⟨f₁.map x, f₂.map x⟩ の等式
    have eq1 : (g.map x).1 = f₁.map x := by
      have := congrArg StructureTower.Hom.map h₁
      exact congrFun this x
    have eq2 : (g.map x).2 = f₂.map x := by
      have := congrArg StructureTower.Hom.map h₂
      exact congrFun this x
    exact Prod.ext eq1 eq2
  
  -- Part 2: indexMap の等式  
  · funext i
    -- g.indexMap i と ⟨f₁.indexMap i, f₂.indexMap i⟩ の等式
    have eq1 : (g.indexMap i).1 = f₁.indexMap i := by
      have := congrArg StructureTower.Hom.indexMap h₁
      exact congrFun this i
    have eq2 : (g.indexMap i).2 = f₂.indexMap i := by
      have := congrArg StructureTower.Hom.indexMap h₂
      exact congrFun this i
    exact Prod.ext eq1 eq2
```

---

## 数学的教訓

### 1. 直積の特殊性

直積は「普遍射影」を持つため、射を一意に決定する。
これは一般の構造塔では成り立たない性質。

### 2. 圏論的構造の力

射影射を通じた制約により、indexMap の自由度が消える。
これは圏論的な普遍性の真の力。

### 3. 形式化による発見

非形式的には「明らか」に見えた一意性が、
形式化により2つの異なるケースに分かれることが判明：
- 一般の場合: 一意性なし
- 直積の場合: 一意性あり

---

## 推奨事項

### すぐにできること

1. **prodUniversal_unique の完全証明を実装**
   ```lean
   -- CAT2_advanced.lean の 365-369 行を上記の証明で置き換え
   ```

2. **対応する定理を追加**
   ```lean
   -- 基礎写像の一意性（弱いバージョン）
   lemma prodUniversal_unique_map : g.map = ... := by ...
   
   -- indexMap の一意性（強いバージョン）
   lemma prodUniversal_unique_indexMap : g.indexMap = ... := by ...
   ```

3. **コメントで説明を追加**
   ```lean
   /-- 積の普遍性における一意性
   
   注意: この一意性は「射としての一意性」であり、
   freeStructureTower のケースとは異なり完全に証明可能である。
   理由は、射影射 proj₁ と proj₂ が indexMap を完全に制約するため。
   -/
   ```

### さらなる発展

4. **一般化の探求**
   - どのような条件で indexMap の一意性が成り立つか？
   - 「十分な射影」の概念の形式化

5. **他の圏論的構成**
   - 余積（coproduct）
   - イコライザー（equalizer）
   - プルバック（pullback）

---

## 結論

**prodUniversal_unique は完全に証明可能！** ✅

この証明は：
- 技術的に実装可能
- 数学的に正しい
- 教育的に価値がある

あなたの直観は正しく、実際に証明できます。

次のステップ：
1. 上記の証明を CAT2_advanced.lean に実装
2. コンパイルを確認
3. テストケースを追加

頑張ってください！
