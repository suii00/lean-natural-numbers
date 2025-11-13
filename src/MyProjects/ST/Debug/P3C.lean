import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Types.Basic

universe u v

/-!
# 自然数の構造塔：忘却関手の応用

自然数上の構造塔を具体例として、忘却関手がどのように機能するかを示す。
特に、後者関数 succ が誘導する射と忘却関手の関係を調べる。
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

def Hom.id (T : StructureTowerWithMin.{u, v}) : Hom T T where
  map := _root_.id
  indexMap := _root_.id
  indexMap_mono := fun hij => hij
  layer_preserving := fun _ _ hx => hx
  minLayer_preserving := fun _ => rfl

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

instance : CategoryTheory.Category StructureTowerWithMin.{u, v} where
  Hom := Hom
  id := Hom.id
  comp := fun f g => Hom.comp g f
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

open CategoryTheory

/-- 基礎集合への忘却関手 -/
def forgetCarrier : StructureTowerWithMin.{u, v} ⥤ Type u where
  obj := fun T => T.carrier
  map := fun f => f.map
  map_id := by intro T; funext x; rfl
  map_comp := by intro T T' T'' f g; funext x; rfl

/-- 添字集合への忘却関手 -/
def forgetIndex : StructureTowerWithMin.{u, v} ⥤ Type v where
  obj := fun T => T.Index
  map := fun f => f.indexMap
  map_id := by intro T; funext i; rfl
  map_comp := by intro T T' T'' f g; funext i; rfl

/-! ## 自然数の構造塔 -/

/-- エラー1: 自然数上の構造塔（minLayer_minimalの証明エラー） -/
def natTowerMin : StructureTowerWithMin.{0, 0} where
  carrier := ℕ
  Index := ℕ
  layer := fun n => {k : ℕ | k ≤ n}
  covering := by intro x; use x; exact le_refl x
  monotone := by intro i j hij x hx; exact le_trans hx hij
  minLayer := _root_.id
  minLayer_mem := by intro x; exact le_refl x
  -- エラー: minLayer_minimalの証明が不完全
  minLayer_minimal := by
    intro x i hx
    -- x ∈ {k | k ≤ i} つまり x ≤ i
    -- minLayer x = x なので x ≤ i を示せばよい
    exact hx

/-- エラー2: 後者関数が誘導する射（indexMap_monoの証明エラー） -/
def natSuccHom : natTowerMin ⟶ natTowerMin where
  map := Nat.succ
  indexMap := Nat.succ
  -- エラー: 単調性の証明が不適切
  indexMap_mono := by
    intro i j hij
    -- succ i ≤ succ j を示す必要がある
    exact Nat.succ_le_succ hij
  layer_preserving := by
    intro i x hx
    -- x ∈ {k | k ≤ i} から succ x ∈ {k | k ≤ succ i} を示す
    show Nat.succ x ≤ Nat.succ i
    exact Nat.succ_le_succ hx
  minLayer_preserving := by intro x; rfl

/-- エラー3: 忘却関手を通じた射の可換性（等式の証明エラー） -/
lemma forgetCarrier_natSuccHom :
    forgetCarrier.map natSuccHom = Nat.succ := by
  -- エラー: 関数の等式の証明が不完全
  funext x; rfl

/-- エラー4: 添字への忘却でも可換（証明戦略のエラー） -/
lemma forgetIndex_natSuccHom :
    forgetIndex.map natSuccHom = Nat.succ := by
  -- エラー: funextを使う必要がある
  funext i; rfl

/-- エラー5: 恒等射の忘却（型の不一致） -/
-- 恒等射を忘却すると、Type の恒等関数になる
lemma forgetCarrier_id :
    forgetCarrier.map (𝟙 natTowerMin) = _root_.id := by
  -- エラー: id の型が明確でない
  funext x; rfl

/-! ## 忘却関手の関係性 -/

/-- 射の合成と忘却関手の関係 -/
lemma forgetCarrier_comp (f g : natTowerMin ⟶ natTowerMin) :
    forgetCarrier.map (f ≫ g) = forgetCarrier.map f ≫ forgetCarrier.map g := by
  -- これは関手の法則から自動的に従う
  rfl

/-- 2つの忘却関手の対象への適用 -/
example : forgetCarrier.obj natTowerMin = ℕ := rfl
example : forgetIndex.obj natTowerMin = ℕ := rfl

/-- natTowerMinでは carrier と Index が一致する特殊なケース -/
lemma natTower_carrier_eq_index :
    forgetCarrier.obj natTowerMin = forgetIndex.obj natTowerMin := rfl

end StructureTowerWithMin
