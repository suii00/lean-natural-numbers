import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Types.Basic

universe u v

/-!
# 構造塔の忘却関手

構造塔から基礎集合や添字集合への忘却関手を定義する。
これらは圏論における典型的な忘却関手の例である。
-/

/-- 最小層を持つ構造塔 -/
structure StructureTowerWithMin where
  carrier : Type u
  Index : Type v
  [indexPreorder : Preorder Index]
  layer : Index → Set carrier
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j
  minLayer : carrier → Index
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  minLayer_minimal : ∀ {x i}, x ∈ layer i → minLayer x ≤ i

namespace StructureTowerWithMin

instance instIndexPreorder (T : StructureTowerWithMin.{u, v}) : Preorder T.Index :=
  T.indexPreorder

variable {T T' T'' : StructureTowerWithMin.{u, v}}

/-- 構造塔の射 -/
structure Hom (T T' : StructureTowerWithMin.{u, v}) where
  map : T.carrier → T'.carrier
  indexMap : T.Index → T'.Index
  indexMap_mono : ∀ {i j : T.Index}, i ≤ j → indexMap i ≤ indexMap j
  layer_preserving : ∀ (i : T.Index) (x : T.carrier),
    x ∈ T.layer i → map x ∈ T'.layer (indexMap i)
  minLayer_preserving : ∀ x, T'.minLayer (map x) = indexMap (T.minLayer x)

/-- 恒等射 -/
def Hom.id (T : StructureTowerWithMin.{u, v}) : Hom T T where
  map := _root_.id
  indexMap := _root_.id
  indexMap_mono := fun hij => hij
  layer_preserving := fun _ _ hx => hx
  minLayer_preserving := fun _ => rfl

/-- 射の合成 -/
def Hom.comp (g : Hom T' T'') (f : Hom T T') : Hom T T'' where
  map := fun x => g.map (f.map x)
  indexMap := fun i => g.indexMap (f.indexMap i)
  indexMap_mono := fun hij => g.indexMap_mono (f.indexMap_mono hij)
  layer_preserving := fun i x hx =>
    g.layer_preserving (f.indexMap i) (f.map x) (f.layer_preserving i x hx)
  minLayer_preserving := by
    intro x
    calc T''.minLayer (g.map (f.map x))
        = g.indexMap (T'.minLayer (f.map x)) := by rw [g.minLayer_preserving]
      _ = g.indexMap (f.indexMap (T.minLayer x)) := by rw [f.minLayer_preserving]

/-- 構造塔は圏をなす -/
instance : CategoryTheory.Category StructureTowerWithMin.{u, v} where
  Hom := Hom
  id := Hom.id
  comp := fun f g => Hom.comp g f
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

open CategoryTheory

/-- エラー1: 基礎集合への忘却関手（記法エラー） -/
-- エラー: 関手の記法が間違っている
def forgetCarrier : StructureTowerWithMin.{u, v} ⥤ Type u where
  obj := fun T => T.carrier
  map := fun f => f.map
  map_id := by intro T; funext x; rfl
  map_comp := by intro T T' T'' f g; funext x; rfl

/-- エラー2: 添字集合への忘却関手（map_idの証明エラー） -/
def forgetIndex : StructureTowerWithMin.{u, v} ⥤ Type v where
  obj := fun T => T.Index
  map := fun f => f.indexMap
  -- エラー: map_idの証明が不完全
  map_id := by
    intro T
    funext i
    rfl
  map_comp := by intro T T' T'' f g; funext i; rfl

/-- エラー3: 関手の合成（map_compの論理エラー） -/
def forgetCarrierAlt : StructureTowerWithMin.{u, v} ⥤ Type u where
  obj := fun T => T.carrier
  map := fun f => f.map
  map_id := by intro T; funext x; rfl
  -- エラー: map_compで引数の順序が間違っている
  map_comp := by
    intro T T' T'' f g
    funext x
    rfl

/-- エラー4: 関手則の検証補題（型エラー） -/
-- 関手が恒等射を保つことの明示的な確認
lemma forgetCarrier_map_id (T : StructureTowerWithMin.{u, v}) :
    forgetCarrier.map (𝟙 T) = _root_.id := by
  -- エラー: forgetCarrierがまだ正しく定義されていない状態で参照
  rfl

end StructureTowerWithMin
