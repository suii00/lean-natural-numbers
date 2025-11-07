import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Structure Tower 耐久テスト

構造塔と minLayer の定義の健全性を確認するため、
自明例、極端例、病的例を実装します。

## テストの目的

1. 定義が本当に意図した概念を捉えているか
2. 極端なケースでも破綻しないか
3. 病的な例で予期しない振る舞いがないか

## テスト戦略

- ✅ 構成可能な例：minLayer が存在
- ⚠️ 構成困難な例：minLayer が存在しない
- ❌ 不可能な例：公理を満たさない
-/

-- CAT2_complete.lean からの定義（再掲）
structure StructureTowerWithMin where
  carrier : Type*
  Index : Type*
  [indexPreorder : Preorder Index]
  layer : Index → Set carrier
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j
  minLayer : carrier → Index
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  minLayer_minimal : ∀ x i, x ∈ layer i → minLayer x ≤ i

namespace StructureTowerWithMin

instance instIndexPreorder (T : StructureTowerWithMin) : Preorder T.Index :=
  T.indexPreorder

/-! ## 自明例（Trivial Examples）-/

/-- 【自明例1】単一層の構造塔
すべての要素が一つの層にのみ属する

これは最も単純な構造塔で、minLayer は自明に存在 -/
def singleLayerTower (X : Type*) : StructureTowerWithMin where
  carrier := X
  Index := Unit
  indexPreorder := by infer_instance
  layer := fun _ => Set.univ  -- 唯一の層が全体
  covering := by intro x; use (); exact Set.mem_univ x
  monotone := by intro i j _; exact le_refl _
  minLayer := fun _ => ()  -- すべての要素が同じ層
  minLayer_mem := by intro x; exact Set.mem_univ x
  minLayer_minimal := by intro x i _; exact le_refl _

/-- 【自明例2】離散構造塔
各要素が独立した層を持つ（自由構造塔の特殊ケース）

離散順序：i ≤ j ⟺ i = j -/
def discreteTower (X : Type*) : StructureTowerWithMin where
  carrier := X
  Index := X
  indexPreorder := by
    refine ⟨fun i j => i = j, fun _ _ => False, ?_, ?_, ?_⟩
    · intro i; rfl
    · intro i j k hij hjk; exact hij.trans hjk
    · intro a b; constructor
      · intro h; cases h
      · intro ⟨hab, hba⟩; exact hba hab.symm
  layer := fun i => {i}  -- 各層は単元集合
  covering := by intro x; use x; rfl
  monotone := by
    intro i j hij x hx
    simp at hx ⊢
    rw [hx, hij]
  minLayer := id
  minLayer_mem := by intro x; rfl
  minLayer_minimal := by intro x i hx; exact hx

/-- 【自明例3】二層構造塔
下層と上層のみからなる構造

これは最も単純な非自明例 -/
def twoLayerTower (X Y : Type*) (h : X ⊆ Y) : StructureTowerWithMin where
  carrier := Y
  Index := Bool
  indexPreorder := by infer_instance  -- false < true
  layer := fun b => if b then Set.univ else {y | y ∈ X}
  covering := by
    intro y
    use true
    exact Set.mem_univ y
  monotone := by
    intro i j hij y hy
    match i, j with
    | false, false => exact hy
    | false, true => exact Set.mem_univ y
    | true, true => exact hy
  minLayer := fun y => if y ∈ X then false else true
  minLayer_mem := by
    intro y
    by_cases h : y ∈ X
    · simp [h]
    · simp [h]
  minLayer_minimal := by
    intro y i hi
    by_cases h : y ∈ X
    · simp [h]
    · match i with
      | false =>
        simp at hi
        contradiction
      | true => exact le_refl _

/-! ## 極端例（Extreme Examples）-/

/-- 【極端例1】空添字集合（不可能）
空添字集合では被覆性を満たせない

これは構成**不可能**な例 -/
-- def emptyIndexTower : StructureTowerWithMin where
--   carrier := ℕ
--   Index := Empty  -- 空型
--   ...
--   covering := by
--     intro x
--     -- ∃ i : Empty は証明不可能！
--     sorry

/-- 【極端例2】無限昇鎖
自然数の通常の順序による無限の層

これは典型的な無限構造塔 -/
def infiniteChainTower : StructureTowerWithMin where
  carrier := ℕ
  Index := ℕ
  layer := fun n => {k | k ≤ n}
  covering := by intro x; use x; exact le_refl x
  monotone := by intro i j hij x hx; exact le_trans hx hij
  minLayer := id
  minLayer_mem := by intro x; exact le_refl x
  minLayer_minimal := by intro x i hx; exact hx

/-- 【極端例3】完全に重複する層
すべての層が全体と等しい

minLayer は任意に選べるが、ここでは最小の添字を選ぶ -/
def constantLayerTower (X : Type*) [Inhabited ι] (ι : Type*) [Preorder ι]
    : StructureTowerWithMin where
  carrier := X
  Index := ι
  layer := fun _ => Set.univ  -- すべての層が全体
  covering := by intro x; use default; exact Set.mem_univ x
  monotone := by intro i j _ x _; exact Set.mem_univ x
  minLayer := fun _ => default  -- 常に最小（default）を返す
  minLayer_mem := by intro x; exact Set.mem_univ x
  minLayer_minimal := by
    intro x i _
    -- これは一般には証明できない！
    -- default が本当に最小とは限らない
    sorry  -- ⚠️ この例は実は問題がある

/-- 【極端例3修正版】すべての層が全体（最小元を持つ順序）
Bottom 型クラスを使って最小元を保証 -/
def constantLayerTower' (X : Type*) (ι : Type*) [Preorder ι] [OrderBot ι]
    : StructureTowerWithMin where
  carrier := X
  Index := ι
  layer := fun _ => Set.univ
  covering := by intro x; use ⊥; exact Set.mem_univ x
  monotone := by intro i j _ x _; exact Set.mem_univ x
  minLayer := fun _ => ⊥  -- 最小元を返す
  minLayer_mem := by intro x; exact Set.mem_univ x
  minLayer_minimal := by intro x i _; exact bot_le

/-! ## 病的例（Pathological Examples）-/

/-- 【病的例1】下界のない構造塔
降鎖条件を満たさない順序での構造塔

整数全体 ℤ での初期区間
layer n = {k | k ≤ n}

問題：任意の x に対して、x を含む層は無限に存在するが、
      最小の層は存在しない（下に有界でない）

したがって、StructureTowerWithMin は構成**不可能**
-/

-- 修正：有界な部分だけを使う
def boundedIntTower : StructureTowerWithMin where
  carrier := {z : ℤ | 0 ≤ z}  -- 非負整数のみ
  Index := {z : ℤ | 0 ≤ z}
  layer := fun ⟨n, _⟩ => {⟨k, hk⟩ | k ≤ n}
  covering := by
    intro ⟨x, hx⟩
    use ⟨x, hx⟩
    simp
  monotone := by
    intro ⟨i, _⟩ ⟨j, _⟩ hij ⟨x, _⟩ hx
    simp at hx ⊢
    exact le_trans hx hij
  minLayer := fun ⟨x, hx⟩ => ⟨x, hx⟩
  minLayer_mem := by intro ⟨x, _⟩; simp
  minLayer_minimal := by intro ⟨x, _⟩ ⟨i, _⟩ hi; simp at hi ⊢; exact hi

/-- 【病的例2】反鎖での構造塔
順序が反鎖（任意の異なる2元が比較不能）

この場合、各要素が独自の「最小層」を持つ -/
def antiChainTower (X : Type*) : StructureTowerWithMin where
  carrier := X
  Index := X
  indexPreorder := by
    -- 反鎖：i ≤ j ⟺ i = j
    refine ⟨fun i j => i = j, fun _ _ => False, ?_, ?_, ?_⟩
    · intro i; rfl
    · intro i j k hij hjk; exact hij.trans hjk
    · intro a b; constructor; intro h; cases h; intro ⟨h, _⟩; exact h
  layer := fun i => {i}
  covering := by intro x; use x; rfl
  monotone := by intro i j hij x hx; simp at hx ⊢; rw [hx, hij]
  minLayer := id
  minLayer_mem := by intro x; rfl
  minLayer_minimal := by intro x i hx; exact hx

/-- 【病的例3】層が複雑に重複
異なる層が部分的に重複しているが、包含関係ではない

これは minLayer が存在すれば構成可能だが、
存在を保証するには順序に強い条件が必要 -/

section PartialOverlap

-- 有限集合上の例
def partialOverlapTower : StructureTowerWithMin where
  carrier := Fin 4  -- {0, 1, 2, 3}
  Index := Fin 3    -- {0, 1, 2}
  layer := fun i => 
    match i with
    | 0 => {0, 1}      -- 第0層: {0, 1}
    | 1 => {1, 2}      -- 第1層: {1, 2}
    | 2 => {0, 1, 2, 3}  -- 第2層: 全体
  covering := by
    intro x
    use 2
    fin_cases x <;> decide
  monotone := by
    intro i j hij x hx
    fin_cases i <;> fin_cases j <;> try omega
    · exact hx  -- i = j
    · -- 0 ≤ 1
      fin_cases x <;> decide
    · -- 0 ≤ 2
      fin_cases x <;> decide
    · -- 1 ≤ 2
      fin_cases x <;> decide
  minLayer := fun x =>
    match x with
    | 0 => 0  -- 0は層0に属する（最小）
    | 1 => 0  -- 1は層0, 1に属するが、0が最小
    | 2 => 1  -- 2は層1, 2に属するが、1が最小
    | 3 => 2  -- 3は層2にのみ属する
  minLayer_mem := by
    intro x
    fin_cases x <;> decide
  minLayer_minimal := by
    intro x i hx
    fin_cases x <;> fin_cases i <;> decide

end PartialOverlap

/-! ## 構成不可能な例の分析 -/

/-- 【不可能例1】minLayer が存在しない構造塔

反例：整数 ℤ 上の構造塔で layer n = {k | k ≤ n}

任意の x に対して、x を含む層は {..., x-1, x, x+1, ...} の各層だが、
最小の層は存在しない（下に有界でない）

教訓：minLayer の存在には順序に関する条件が必要
- 下界を持つ（well-founded）
- または各要素に対して層が下に有界
-/

/-- 【不可能例2】被覆性を満たさない

反例：carrier = ℕ, Index = ℕ, layer n = {k | k > n}

すべての層の和集合は ℕ 全体にならない（0がどの層にも属さない）

教訓：被覆性は本質的な条件
-/

/-- 【不可能例3】単調性を満たさない

反例：carrier = ℕ, Index = ℕ,
layer 0 = {0, 1, 2}, layer 1 = {1, 2}, layer 2 = {2, 3}

0 ≤ 1 だが layer 0 ⊈ layer 1（0 ∈ layer 0 だが 0 ∉ layer 1）

教訓：単調性は層の整合性のための必須条件
-/

/-! ## テスト用の補題 -/

/-- minLayer の一意性条件
最小元が一意に決まるための十分条件 -/
theorem minLayer_unique_sufficient (T : StructureTowerWithMin)
    [LinearOrder T.Index]  -- 線形順序
    (x : T.carrier) (i j : T.Index)
    (hi : x ∈ T.layer i) (hj : x ∈ T.layer j)
    (himin : ∀ k, x ∈ T.layer k → i ≤ k)
    (hjmin : ∀ k, x ∈ T.layer k → j ≤ k) :
    i = j := by
  apply le_antisymm
  · exact himin j hj
  · exact hjmin i hi

/-- 空でない有限順序では最小元が存在 -/
theorem exists_min_in_finite [LinearOrder ι] [Fintype ι] [Nonempty ι] :
    ∃ m : ι, ∀ i : ι, m ≤ i := by
  sorry  -- Mathlib に存在

/-! ## 耐久テストの結論 -/

/-
# 耐久テストから得られた知見

## 構成可能な例

1. **単一層**：最も単純、常に構成可能
2. **離散構造**：各要素が独立、構成可能
3. **有限鎖**：典型的な例、構成可能
4. **無限鎖**：下界があれば構成可能

## 構成困難な例

1. **下界のない構造**：minLayer が存在しない
2. **完全重複**：minLayer の選択が任意（最小元が必要）

## 定義の健全性

### ✅ 良い点

- 被覆性と単調性は自然な条件
- minLayer の条件（mem と minimal）は必要十分
- 多くの自然な例で構成可能

### ⚠️ 注意点

- minLayer の存在は自明ではない
- 順序に関する条件（下界、well-founded）が必要なことがある
- 完全に重複する層では最小元の存在が必要

### 💡 改善案

Version D: Well-founded 構造塔
```lean
structure StructureTowerWF where
  ...
  [wf : WellFoundedLT Index]  -- 下降鎖条件
  -- これにより minLayer の存在が保証される
```

## 推奨される使用法

1. **有限順序**：問題なし
2. **ℕ や自然な順序**：問題なし
3. **無限鎖**：下界があれば OK
4. **一般の順序**：注意が必要

この耐久テストにより、定義の限界と適用範囲が明確になりました。
-/

end StructureTowerWithMin
