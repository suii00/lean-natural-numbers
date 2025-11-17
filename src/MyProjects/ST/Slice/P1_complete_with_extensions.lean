import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import MyProjects.ST.CAT2_complete

universe u v

namespace StructureTowerWithMin

variable {T : StructureTowerWithMin.{u, v}}

/-- 構造塔を添字 i より上で切断する操作
幾何学的には「塔を水平に切って上半分を取る」イメージ -/
def sliceAbove (T : StructureTowerWithMin.{u, v}) (i : T.Index) :
    StructureTowerWithMin.{u, v} where
  carrier := {x : T.carrier // i ≤ T.minLayer x}
  Index := {j : T.Index // i ≤ j}
  indexPreorder := inferInstance
  layer j := {x | x.val ∈ T.layer j.val}
  covering := by
    intro x
    obtain ⟨k, hk⟩ := T.covering x.val
    have hik : i ≤ k := by
      calc
        i ≤ T.minLayer x.val := x.property
        _ ≤ k := T.minLayer_minimal x.val k hk
    use ⟨k, hik⟩
    exact hk
  monotone := by
    intro j₁ j₂ hjj
    intro x hx
    exact T.monotone hjj hx
  minLayer := fun x => ⟨T.minLayer x.val, x.property⟩
  minLayer_mem := by
    intro x
    exact T.minLayer_mem x.val
  minLayer_minimal := by
    intro x j hx
    exact T.minLayer_minimal x.val j.val hx

/-! ## 拡張課題の解答例 -/

/-- sliceAbove から元の構造塔への包含射 -/
def sliceAbove_inclusion (T : StructureTowerWithMin) (i : T.Index) :
    sliceAbove T i ⟶ T where
  map := Subtype.val
  indexMap := Subtype.val
  indexMap_mono := fun hjj => hjj
  layer_preserving := fun _ _ hx => hx
  minLayer_preserving := fun _ => rfl

/-- 包含射は単射である -/
lemma sliceAbove_inclusion_injective (T : StructureTowerWithMin) (i : T.Index) :
    Function.Injective (sliceAbove_inclusion T i).map := by
  -- Subtype.val は常に単射
  exact Subtype.val_injective

/-- sliceAbove の union は元の塔の union の部分集合 -/
lemma sliceAbove_union_subset (T : StructureTowerWithMin) (i : T.Index)
    (x : (sliceAbove T i).carrier) : ∃ k, x.val ∈ T.layer k := by
  -- x.val は T.carrier の要素なので、covering により
  -- ある層に属する
  obtain ⟨k, hk⟩ := T.covering x.val
  exact ⟨k, hk⟩

/-! ## さらなる補題：敷き詰めと積み上げの実践 -/

/-- 補題1（基礎層）: sliceAbove の要素の性質 -/
lemma sliceAbove_mem_iff (T : StructureTowerWithMin) (i : T.Index) 
    (x : T.carrier) :
    (∃ h : i ≤ T.minLayer x, (⟨x, h⟩ : (sliceAbove T i).carrier) ∈ 
      (sliceAbove T i).layer ⟨T.minLayer x, h⟩) ↔ 
    i ≤ T.minLayer x := by
  constructor
  · intro ⟨h, _⟩
    exact h
  · intro h
    use h
    exact T.minLayer_mem x

/-- 補題2（基礎層）: 層の包含関係 -/
lemma sliceAbove_layer_subset (T : StructureTowerWithMin) (i j : T.Index)
    (hij : i ≤ j) :
    {x : (sliceAbove T i).carrier | x.val ∈ T.layer j} ⊆
    (sliceAbove T i).layer ⟨j, hij⟩ := by
  intro x hx
  show x ∈ (sliceAbove T i).layer ⟨j, hij⟩
  exact hx

/-- 補題3（中間層）: 包含射と層構造の可換性 -/
lemma sliceAbove_inclusion_layer_comm (T : StructureTowerWithMin) 
    (i : T.Index) (j : (sliceAbove T i).Index) :
    ∀ x : (sliceAbove T i).carrier,
    x ∈ (sliceAbove T i).layer j → 
    (sliceAbove_inclusion T i).map x ∈ T.layer j.val := by
  intro x hx
  exact (sliceAbove_inclusion T i).layer_preserving j x hx

/-- 定理（屋根）: sliceAbove の完全性
元の塔で i より上のすべての要素は、sliceAbove に含まれる -/
theorem sliceAbove_complete (T : StructureTowerWithMin) (i : T.Index)
    (x : T.carrier) (hx : i ≤ T.minLayer x) :
    ∃ y : (sliceAbove T i).carrier, y.val = x :=
  ⟨⟨x, hx⟩, rfl⟩

/-! 
## 学習のポイント

この実装を通じて学んだこと：

1. **Subtype の使い方**: 
   - `{x : A | P x}` は集合（Set A）
   - `{x : A // P x}` は部分型（Type）
   - 構造体のフィールドには Type が必要

2. **証明の敷き詰めパターン**:
   ```
   ┌─────────────────────────┐
   │ sliceAbove_complete     │ ← 定理（屋根）
   ├─────────────────────────┤
   │ inclusion_layer_comm    │ ← 第2層
   ├─────────────────────────┤
   │ layer_subset, mem_iff   │ ← 第1層（基礎）
   ├─────────────────────────┤
   │ sliceAbove定義          │ ← 土台
   └─────────────────────────┘
   ```

3. **部分構造の構成**:
   - carrier: 条件を満たす要素の部分型
   - Index: 条件を満たす添字の部分型
   - layer: 元の層と新しい carrier の交差
   - covering と monotone: 元の性質から自然に導出

4. **包含射の普遍性**:
   - Subtype.val は自然な包含
   - 常に単射
   - 構造を保存する

5. **幾何学的直感**:
   切断操作は「塔を水平に切る」という視覚的イメージと、
   形式的な Subtype による制限が完全に対応している
-/

end StructureTowerWithMin
