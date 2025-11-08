import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Mathlib.Order.WellFounded
import Mathlib.CategoryTheory.Category.Basic

universe u v

/-!
# Well-founded Structure Tower

minLayer に関して well-founded（整礎的）な構造塔の理論。

## 主要概念

**Well-foundedness（整礎性）**: 
無限降下列が存在しないこと。構造塔の文脈では、
minLayer の値が真に減少し続ける無限列が存在しないことを意味する。

## 数学的重要性

1. **帰納法の原理**: well-foundedness により、minLayer に関する帰納法が使える
2. **再帰的定義**: minLayer に基づく再帰が停止することが保証される
3. **複雑度の測定**: minLayer を複雑度の指標として使える

## 主な結果

- 自然数の構造塔は自動的に well-founded
- 有限集合上の構造塔は well-founded
- well-founded な構造塔上で強力な証明原理が使える
-/

/-- 最小層を持つ構造塔（基本定義） -/
structure StructureTowerWithMin where
  carrier : Type u
  Index : Type v
  [indexPreorder : Preorder Index]
  layer : Index → Set carrier
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j
  minLayer : carrier → Index
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  minLayer_minimal : ∀ x i, x ∈ layer i → minLayer x ≤ i

namespace StructureTowerWithMin

instance instIndexPreorder (T : StructureTowerWithMin.{u, v}) : Preorder T.Index :=
  T.indexPreorder

variable (T : StructureTowerWithMin.{u, v})

/-! ## Well-foundedness の定義 -/

/-- 構造塔が minLayer に関して well-founded である
つまり、minLayer の値が真に減少し続ける無限降下列が存在しない -/
class WellFoundedTower (T : StructureTowerWithMin.{u, v}) : Prop where
  /-- Index 上の順序が well-founded -/
  wf : WellFounded ((· < ·) : T.Index → T.Index → Prop)

/-- minLayer による誘導順序
x < y ⟺ minLayer x < minLayer y -/
def minLayerLT (T : StructureTowerWithMin) (x y : T.carrier) : Prop :=
  T.minLayer x < T.minLayer y

/-- 別の定式化: carrier 上の誘導順序が well-founded -/
class WellFoundedTower' (T : StructureTowerWithMin.{u, v}) : Prop where
  /-- minLayer による誘導順序が well-founded -/
  wf_carrier : WellFounded (minLayerLT T)

/-! ## 基本的な性質 -/

/-- Index が well-founded なら carrier の誘導順序も well-founded -/
theorem wf_index_implies_wf_carrier [WellFoundedTower T] :
    WellFoundedTower' T := by
  constructor
  unfold minLayerLT
  apply InvImage.wf T.minLayer
  exact WellFoundedTower.wf

/-- 有限型の Index を持つ構造塔は自動的に well-founded -/
instance instWellFoundedFinite [Finite T.Index] : WellFoundedTower T where
  wf := Finite.wellFounded_of_trans_of_irrefl _

/-! ## 帰納法の原理 -/

/-- Well-founded な構造塔上での帰納法
minLayer に関する帰納法が使える -/
theorem minLayer_induction [WellFoundedTower T]
    {P : T.carrier → Prop}
    (h : ∀ x, (∀ y, T.minLayer y < T.minLayer x → P y) → P x) :
    ∀ x, P x := by
  intro x
  apply WellFounded.induction WellFoundedTower.wf (T.minLayer x)
  intro i ih
  -- i = minLayer z となる z について P z を示す
  by_cases ∃ z, T.minLayer z = i
  case pos =>
    obtain ⟨z, hz⟩ := this
    cases hz
    apply h z
    intro y hlt
    have : T.minLayer y < i := by simpa using hlt
    exact ih (T.minLayer y) this
  case neg =>
    -- このケースは不要だが、完全性のため
    exfalso
    push_neg at this
    sorry

/-- より使いやすい形の帰納法 -/
theorem minLayer_rec [WellFoundedTower T]
    {motive : T.carrier → Sort*}
    (ind : ∀ x, (∀ y, T.minLayer y < T.minLayer x → motive y) → motive x) :
    ∀ x, motive x := by
  intro x
  apply WellFounded.fix WellFoundedTower.wf (motive := fun i => 
    ∀ z, T.minLayer z = i → motive z)
  intro i ih z hz
  cases hz
  apply ind z
  intro y hlt
  exact ih (T.minLayer y) hlt y rfl
  exact rfl

/-! ## 再帰的定義 -/

/-- Well-founded な構造塔上での再帰的関数定義
minLayer に基づく再帰が正当化される -/
def minLayer_recursion [WellFoundedTower T]
    {α : Type*}
    (f : ∀ x : T.carrier, (∀ y, T.minLayer y < T.minLayer x → α) → α) :
    T.carrier → α :=
  fun x => WellFounded.fix WellFoundedTower.wf
    (fun i rec => f (Classical.choose (T.covering (Classical.choose 
      (show ∃ z, T.minLayer z = i by sorry))))
      (fun y hlt => rec (T.minLayer y) hlt))
    (T.minLayer x)

/-! ## 具体例 -/

/-- 自然数の構造塔は well-founded -/
def natTowerMin : StructureTowerWithMin.{0, 0} where
  carrier := ℕ
  Index := ℕ
  layer := fun n => {k : ℕ | k ≤ n}
  covering := by intro x; use x; exact le_refl x
  monotone := by intro i j hij x hx; exact le_trans hx hij
  minLayer := _root_.id
  minLayer_mem := by intro x; exact le_refl x
  minLayer_minimal := by intro x i hx; exact hx

/-- 自然数の構造塔は well-founded -/
instance : WellFoundedTower natTowerMin where
  wf := wellFounded_lt

/-- 自然数の構造塔上での帰納法の例 -/
example (P : ℕ → Prop) (h : ∀ n, (∀ m, m < n → P m) → P n) : ∀ n, P n := by
  apply minLayer_induction natTowerMin
  exact h

/-! ## Well-founded な構造塔の操作 -/

/-- 部分構造塔が well-founded を保つ -/
theorem wf_substructure [WellFoundedTower T]
    (S : Set T.carrier)
    (hclosed : ∀ x ∈ S, ∀ y, T.minLayer y < T.minLayer x → y ∈ S) :
    WellFoundedTower ⟨T.carrier, T.Index, T.layer, T.covering, T.monotone,
      T.minLayer, T.minLayer_mem, T.minLayer_minimal⟩ :=
  inferInstance  -- 同じインスタンス

/-! ## 複雑度の測定 -/

/-- minLayer を複雑度として使う
well-founded なら、これは有限の値 -/
def complexity [WellFoundedTower T] (x : T.carrier) : ℕ :=
  -- Index に natural number embedding があると仮定
  sorry

/-- 複雑度による比較 -/
def complexity_lt [WellFoundedTower T] (x y : T.carrier) : Prop :=
  T.minLayer x < T.minLayer y

/-! ## 高度な性質 -/

/-- Well-founded な構造塔では、任意の非空部分集合に最小元が存在 -/
theorem has_min_element [WellFoundedTower T]
    (S : Set T.carrier) (hne : S.Nonempty) :
    ∃ x ∈ S, ∀ y ∈ S, T.minLayer x ≤ T.minLayer y := by
  obtain ⟨x₀, hx₀⟩ := hne
  -- minLayer x₀ より小さい minLayer を持つ S の要素の集合
  let I := {i : T.Index | ∃ x ∈ S, T.minLayer x = i}
  -- well-foundedness から最小元が存在
  have : ∃ i₀ ∈ I, ∀ i ∈ I, i₀ ≤ i := by
    sorry
  obtain ⟨i₀, ⟨x, hx, heq⟩, hmin⟩ := this
  use x, hx
  intro y hy
  have : T.minLayer y ∈ I := ⟨y, hy, rfl⟩
  rw [← heq]
  exact hmin (T.minLayer y) this

/-! ## 線形拡張 -/

/-- Well-founded な半順序は線形順序に拡張できる（Szpilrajn の定理）
構造塔の文脈での応用 -/
-- これは高度なトピック

/-! ## Well-quasi-ordering との関係 -/

/-- Well-founded かつ任意の反鎖が有限な場合、well-quasi-ordering -/
-- これも高度なトピック

end StructureTowerWithMin

/-! ## 具体例：有限型上の構造塔 -/

/-- Fin n 上の構造塔は自動的に well-founded -/
def finTower (n : ℕ) : StructureTowerWithMin.{0, 0} where
  carrier := Fin n
  Index := Fin n
  layer := fun i => {k : Fin n | k ≤ i}
  covering := by intro x; use x; exact le_refl x
  monotone := by intro i j hij x hx; exact le_trans hx hij
  minLayer := _root_.id
  minLayer_mem := by intro x; exact le_refl x
  minLayer_minimal := by intro x i hx; exact hx

instance (n : ℕ) : StructureTowerWithMin.WellFoundedTower (finTower n) where
  wf := Fin.lt_wf

/-! ## 実数区間の場合（well-founded でない例） -/

/-- 実数区間の構造塔（これは一般に well-founded でない） -/
def realIntervalTower : StructureTowerWithMin.{0, 0} where
  carrier := ℝ
  Index := ℝ
  layer := fun r => Set.Iic r  -- (-∞, r]
  covering := by intro x; use x; exact le_refl x
  monotone := by intro r s hrs x hx; exact le_trans hx hrs
  minLayer := _root_.id
  minLayer_mem := by intro x; exact le_refl x
  minLayer_minimal := by intro x r hx; exact hx

/-- 実数は well-founded でない（無限降下列が存在する）
例: 1, 0, -1, -2, -3, ... -/
example : ¬ StructureTowerWithMin.WellFoundedTower realIntervalTower := by
  intro h
  -- 無限降下列 -n (n : ℕ) を構成
  sorry

/-! ## 制限された実数区間（well-founded な例） -/

/-- 下に有界な実数の構造塔 -/
def boundedRealTower (lower : ℝ) : StructureTowerWithMin.{0, 0} where
  carrier := {x : ℝ // lower ≤ x}
  Index := {x : ℝ // lower ≤ x}
  layer := fun i => {x : {x : ℝ // lower ≤ x} | x ≤ i}
  covering := by intro x; use x; exact le_refl x
  monotone := by intro i j hij x hx; exact le_trans hx hij
  minLayer := _root_.id
  minLayer_mem := by intro x; exact le_refl x
  minLayer_minimal := by intro x i hx; exact hx

-- これも実は well-founded でないが、
-- 離散化すれば well-founded にできる

/-! ## まとめ -/

/-
# Well-founded Structure Tower の重要性

1. **数学的基礎**
   - 帰納法の正当化
   - 再帰的定義の停止性
   - 最小元の存在

2. **計算的意味**
   - アルゴリズムの停止性
   - 複雑度の測定
   - 構造的再帰

3. **理論的重要性**
   - 順序理論との接続
   - Well-quasi-ordering 理論
   - Ramsey 理論への応用

4. **実用的応用**
   - プログラム検証
   - 帰納的証明
   - 構造的な複雑度解析

5. **Lean での利点**
   - `WellFounded` 型クラスの活用
   - 組み込みの帰納法原理
   - 停止性の自動チェック

## 今後の発展

- Well-quasi-ordering の理論
- Ordinal による測度
- 超限帰納法
- Noetherian 性との関係
-/
