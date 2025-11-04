import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Mathlib.CategoryTheory.Category.Basic

universe u v

/-!
# 構造塔の圏論的構造

この課題では、構造塔 (Structure Tower) の射を定義し、
それが圏を形成することを証明します。

## 参考文献
- Bourbaki, "Theory of Sets"
- Mac Lane, "Categories for the Working Mathematician"
-/

/-- 構造塔 (Structure Tower) の定義
三つ組 (X, (Xᵢ), ≤) からなり、被覆性と単調性を満たす -/
structure StructureTower where
  /-- 基礎集合 -/
  carrier : Type u
  /-- 添字集合 -/
  Index : Type v
  /-- 添字集合上の順序 -/
  [indexPreorder : Preorder Index]
  /-- 各層の定義: Index → Set carrier -/
  layer : Index → Set carrier
  /-- 被覆性: すべての層の和集合が全体を覆う -/
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  /-- 単調性: 順序を保存 -/
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j

instance instIndexPreorder (T : StructureTower.{u, v}) : Preorder T.Index :=
  T.indexPreorder

namespace StructureTower

variable {u v}
variable {T T' T'' T''' : StructureTower.{u, v}}

/-- 構造塔の射 (Structure Tower Morphism)
対 (f, φ) であって、f が集合の写像、φ が順序を保つ写像、
かつ f が層構造を保存する -/
structure Hom (T T' : StructureTower.{u, v}) where
  /-- 基礎集合間の写像 -/
  map : T.carrier → T'.carrier
  /-- 添字集合間の順序を保つ写像 -/
  indexMap : T.Index → T'.Index
  /-- φ が順序を保存することの証明 -/
  indexMap_mono : ∀ {i j : T.Index}, i ≤ j → indexMap i ≤ indexMap j
  /-- f が層構造を保存することの証明 -/
  layer_preserving : ∀ (i : T.Index) (x : T.carrier),
    x ∈ T.layer i → map x ∈ T'.layer (indexMap i)

/-- 射の合成 -/
def Hom.comp {T T' T'' : StructureTower.{u, v}} (g : Hom T' T'') (f : Hom T T') : Hom T T'' where
  map := fun x => g.map (f.map x)
  indexMap := fun i => g.indexMap (f.indexMap i)
  indexMap_mono := by
    intro i j hij
    have hf : f.indexMap i ≤ f.indexMap j := f.indexMap_mono hij
    exact g.indexMap_mono hf
  layer_preserving := by
    intro i x hx
    exact
      g.layer_preserving (f.indexMap i) (f.map x) (f.layer_preserving i x hx)

/-- 恒等射 -/
def Hom.id (T : StructureTower.{u, v}) : Hom T T where
  map := _root_.id
  indexMap := _root_.id
  indexMap_mono := by
    intro i j hij
    simpa using hij
  layer_preserving := by
    intro i x hx
    simpa using hx

/-- 補題: 射の合成は結合的 -/
@[simp]
theorem Hom.comp_assoc (f : Hom T T') (g : Hom T' T'') (h : Hom T'' T''') :
    Hom.comp h (Hom.comp g f) = Hom.comp (Hom.comp h g) f := by
  rfl

/-- 補題: 恒等射は左単位元 -/
@[simp]
theorem Hom.id_comp (f : Hom T T') : Hom.comp f (Hom.id T) = f := by
  rfl

/-- 補題: 恒等射は右単位元 -/
@[simp]
theorem Hom.comp_id (f : Hom T T') : Hom.comp (Hom.id T') f = f := by
  rfl

/-- 構造塔は圏をなす -/
instance : CategoryTheory.Category (StructureTower.{u, v}) where
  Hom := Hom
  id := Hom.id
  comp := fun {X Y Z} (f : Hom X Y) (g : Hom Y Z) => Hom.comp g f
  id_comp := by
    intro X Y f
    exact Hom.id_comp (T := X) (T' := Y) f
  comp_id := by
    intro X Y f
    exact Hom.comp_id (T := X) (T' := Y) f
  assoc := by
    intro W X Y Z f g h
    exact
      Hom.comp_assoc
        (T := W) (T' := X) (T'' := Y) (T''' := Z) f g h

end StructureTower

/-! ## 具体例: 自然数の初期区間による構造塔 -/

/-- 自然数上の構造塔の具体例
carrier = ℕ, Index = ℕ, layer n = {0, 1, ..., n} -/
def natIntervalTower : StructureTower where
  carrier := ℕ
  Index := ℕ
  indexPreorder := inferInstance
  layer := fun n => {k : ℕ | k ≤ n}
  covering := by
    intro x
    refine ⟨x, ?_⟩
    show x ≤ x
    exact le_rfl
  monotone := by
    intro i j hij x hx
    exact le_trans hx hij

/-- 補題: natIntervalTower の恒等射は well-defined -/
example : StructureTower.Hom natIntervalTower natIntervalTower :=
  StructureTower.Hom.id natIntervalTower

/-- 恒等射の合成が右単位となる具体例 -/
example :
    StructureTower.Hom.comp (StructureTower.Hom.id natIntervalTower)
        (StructureTower.Hom.id natIntervalTower) =
      StructureTower.Hom.id natIntervalTower := by
  rfl

/-- 二つの構造塔の直積 -/
def StructureTower.prod (T₁ T₂ : StructureTower.{u, v}) : StructureTower.{u, v} where
  carrier := T₁.carrier × T₂.carrier
  Index := T₁.Index × T₂.Index
  indexPreorder :=
    inferInstanceAs (Preorder (T₁.Index × T₂.Index))
  layer := fun ⟨i, j⟩ => T₁.layer i ×ˢ T₂.layer j
  covering := by
    intro x
    obtain ⟨i, hi⟩ := T₁.covering x.1
    obtain ⟨j, hj⟩ := T₂.covering x.2
    refine ⟨⟨i, j⟩, ?_⟩
    exact And.intro hi hj
  monotone := by
    intro a b hab x hx
    obtain hx₁ := T₁.monotone hab.1 hx.1
    obtain hx₂ := T₂.monotone hab.2 hx.2
    exact And.intro hx₁ hx₂

/-- 例: 直積構造塔における対角要素 -/
example (x : ℕ) :
    (x, x) ∈ (StructureTower.prod natIntervalTower natIntervalTower).layer ⟨x, x⟩ := by
  simp [StructureTower.prod, natIntervalTower]

-- ## 発展課題（オプション）

/- 射の圏論的な性質をCategoryTheoryライブラリで表現 -/
-- これは上級者向けの発展課題です
-- instance : Category StructureTower where
--   Hom := StructureTower.Hom
--   id := StructureTower.Hom.id
--   comp := StructureTower.Hom.comp
--   id_comp := StructureTower.Hom.id_comp
--   comp_id := StructureTower.Hom.comp_id
--   assoc := StructureTower.Hom.comp_assoc

/-- ファイル末尾の整合性確認用の補題 -/
lemma StructureTower.end_marker : True := trivial
