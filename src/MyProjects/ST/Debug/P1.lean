import Mathlib.Data.Set.Lattice
import Mathlib.Order.Hom.Basic

/-!
# Bourbaki流構造塔

このモジュールでは、ブルバキの集合論風に、任意の順序集合上に構造の階層（塔）を載せる `StructureTower`
と、その合併の性質を扱う。主な定義は、索引ごとの構造を集めた `union`、順序に対して単調な制約、
そして集合全体を覆う場合に合併が全体集合になることの補題である。

## 主要な項目
* `StructureTower`
* `StructureTower.union`
* `StructureTower.level_subset_union`
* `StructureTower.union_eq_univ_of_covering`

## Example
`example {ι α : Type*} [Preorder ι] (T : StructureTower ι α) (hcover : ∀ x, ∃ i, x ∈ T.level i) :
  T.union = Set.univ := T.union_eq_univ_of_covering hcover`
-/

open Set

/-- ブルバキ的な「構造塔」。各レベルに集合を載せ、順序に従って単調に増える。 -/
structure StructureTower (ι α : Type*) [Preorder ι] : Type _ where
  level : ι → Set α
  monotone_level : ∀ {i j}, i ≤ j → level i ⊆ level j

namespace StructureTower

variable {ι α : Type*} [Preorder ι]

/-- 構造塔全体の合併（塔の上に載ったすべての構造を集めた集合）。 -/
def union (T : StructureTower ι α) : Set α := ⋃ i, T.level i

/-- 各レベルは合併に含まれている。 -/
lemma level_subset_union (T : StructureTower ι α) (i : ι) :
    T.level i ⊆ T.union := by
  intro x hx
  exact mem_iUnion.2 ⟨i, hx⟩

/-- 順序が増加すればレベルも包含関係にある。 -/
lemma level_subset_of_le (T : StructureTower ι α) {i j : ι} (hij : i ≤ j) :
    T.level i ⊆ T.level j := T.monotone_level hij

/-- 全体集合を覆うようにレベルが存在すれば合併は `univ` になる。 -/
lemma union_eq_univ_of_covering (T : StructureTower ι α)
    (hcover : ∀ x : α, ∃ i : ι, x ∈ T.level i) :
    T.union = Set.univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨i, hi⟩ := hcover x
    exact mem_iUnion.2 ⟨i, hi⟩

/-- 例：被覆条件が満たされていれば `union` が `univ` に一致する。 -/
example (T : StructureTower ι α)
    (hcover : ∀ x : α, ∃ i : ι, x ∈ T.level i) : T.union = Set.univ :=
  T.union_eq_univ_of_covering hcover

end StructureTower
