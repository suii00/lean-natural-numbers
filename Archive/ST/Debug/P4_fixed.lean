import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Order.Category.Preord
import Mathlib.Order.Hom.Basic

universe u

/-!
# 自由構造塔と随伴関手（完全版）

自由構造塔関手と忘却関手の間の随伴関係を形式化する。
すべての証明を明示的に記述し、simpに頼らずrflとext補題で構成する。

## 主要な定理

* `forgetCarrier_Free_comp`: forgetCarrier ∘ Free の合成則
* `leftTriangleIdentity`: 左三角恒等式
* `rightTriangleIdentity`: 右三角恒等式

## 設計方針

1. 射のベースとなる関数を明示的に定義（helper関数）
2. Preord.ext/Hom.extを使った構造的な等式証明
3. rflで示せるように定義を調整
-/

/-- 最小層を持つ構造塔 -/
structure StructureTowerWithMin where
  carrier : Type u
  Index : Type u
  [indexPreorder : Preorder Index]
  layer : Index → Set carrier
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j
  minLayer : carrier → Index
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  minLayer_minimal : ∀ {x i}, x ∈ layer i → minLayer x ≤ i

/-- `T.minLayer` によって導かれる carrier 上の順序 -/
def StructureTowerWithMin.carrierPreorder (T : StructureTowerWithMin) : Preorder T.carrier where
  le := fun x y => T.minLayer x ≤ T.minLayer y
  le_refl := fun _ => le_refl _
  le_trans := fun _ _ _ hxy hyz => le_trans hxy hyz

namespace StructureTowerWithMin

instance instIndexPreorder (T : StructureTowerWithMin) : Preorder T.Index :=
  T.indexPreorder

variable {T T' T'' : StructureTowerWithMin}

/-- 構造塔の射 -/
structure Hom (T T' : StructureTowerWithMin) where
  map : T.carrier → T'.carrier
  indexMap : T.Index → T'.Index
  indexMap_mono : ∀ {i j : T.Index}, i ≤ j → indexMap i ≤ indexMap j
  layer_preserving : ∀ (i : T.Index) (x : T.carrier),
    x ∈ T.layer i → map x ∈ T'.layer (indexMap i)
  minLayer_preserving : ∀ x, T'.minLayer (map x) = indexMap (T.minLayer x)

/-- 恒等射 -/
def Hom.id (T : StructureTowerWithMin) : Hom T T where
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

@[ext]
lemma Hom.ext {f g : Hom T T'} (hmap : f.map = g.map) (hindex : f.indexMap = g.indexMap) :
    f = g := by
  cases f; cases g; cases hmap; cases hindex; rfl

/-- 構造塔は圏をなす -/
instance : CategoryTheory.Category StructureTowerWithMin where
  Hom := Hom
  id := Hom.id
  comp := fun f g => Hom.comp g f
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

open CategoryTheory

/-! ## 忘却関手の詳細構成 -/

/-- 構造塔の射から誘導される順序準同型（補助定義） -/
def forgetCarrierOrderHom {T T' : StructureTowerWithMin} (f : Hom T T') :
    @OrderHom T.carrier T'.carrier T.carrierPreorder T'.carrierPreorder where
  toFun := f.map
  monotone' := by
    intro x y hxy
    -- hxy : T.minLayer x ≤ T.minLayer y
    calc T'.minLayer (f.map x)
        = f.indexMap (T.minLayer x) := by rw [f.minLayer_preserving]
      _ ≤ f.indexMap (T.minLayer y) := by apply f.indexMap_mono hxy
      _ = T'.minLayer (f.map y) := by rw [f.minLayer_preserving]

/-- 基礎集合への忘却関手 -/
def forgetCarrier : StructureTowerWithMin ⥤ Preord.{u} where
  obj := fun T => ⟨T.carrier, T.carrierPreorder⟩
  map := fun f => Preord.ofHom (forgetCarrierOrderHom f)
  map_id := by
    intro T
    apply Preord.ext
    funext x
    rfl
  map_comp := by
    intro T T' T'' f g
    apply Preord.ext
    funext x
    rfl

/-! ## 自由関手の詳細構成 -/

/-- 半順序集合から自由構造塔を構成 -/
def freeStructureTowerMin (X : Preord.{u}) : StructureTowerWithMin where
  carrier := X
  Index := X
  indexPreorder := X.str
  layer := fun i => { x : X | x ≤ i }
  covering := by intro x; use x; exact le_refl x
  monotone := by intros i j hij x hx; exact le_trans hx hij
  minLayer := _root_.id
  minLayer_mem := by intro x; exact le_refl x
  minLayer_minimal := by intro x i hx; exact hx

/-- Preordの射から誘導される構造塔の射（補助定義） -/
def FreeMap {X Y : Preord.{u}} (f : X ⟶ Y) : 
    Hom (freeStructureTowerMin X) (freeStructureTowerMin Y) where
  map := f
  indexMap := f
  indexMap_mono := by
    intro i j hij
    exact f.monotone' hij
  layer_preserving := by
    intro i x hx
    -- hx : x ≤ i in X
    -- need to show: f x ≤ f i in Y
    exact f.monotone' hx
  minLayer_preserving := by
    intro x
    -- minLayer (f x) = id (f x) = f x
    -- indexMap (minLayer x) = f (id x) = f x
    rfl

/-- 自由関手 -/
def Free : Preord.{u} ⥤ StructureTowerWithMin where
  obj := freeStructureTowerMin
  map := FreeMap
  map_id := by
    intro X
    apply Hom.ext <;> rfl
  map_comp := by
    intro X Y Z f g
    apply Hom.ext <;> rfl

/-! ## 合成に関する補題 -/

/-- forgetCarrier ∘ Free の対象への作用 -/
lemma forgetCarrier_Free_obj (X : Preord.{u}) :
    (forgetCarrier.obj (Free.obj X)).carrier = X.carrier := rfl

/-- forgetCarrier ∘ Free の射への作用が恒等になる補題 -/
lemma forgetCarrier_Free_map {X Y : Preord.{u}} (f : X ⟶ Y) :
    forgetCarrier.map (Free.map f) = f := by
  apply Preord.ext
  funext x
  -- forgetCarrier.map (Free.map f) の定義を展開
  -- = Preord.ofHom (forgetCarrierOrderHom (FreeMap f))
  -- = Preord.ofHom { toFun := (FreeMap f).map, ... }
  -- = Preord.ofHom { toFun := f, ... }
  -- f は Preord.ofHom { toFun := f.hom, ... } の形
  rfl

/-! ## 随伴の単位と余単位 -/

/-- 随伴の単位: Id ⟶ forgetCarrier ∘ Free -/
def adjunctionUnit : 𝟭 Preord.{u} ⟶ Free ⋙ forgetCarrier where
  app := fun X => Preord.ofHom (OrderHom.id : X →o X)
  naturality := by
    intro X Y f
    apply Preord.ext
    funext x
    -- 左辺: (𝟭 Preord).map f ≫ adjunctionUnit.app Y
    --     = f ≫ id = f x
    -- 右辺: adjunctionUnit.app X ≫ (Free ⋙ forgetCarrier).map f
    --     = id ≫ forgetCarrier.map (Free.map f)
    
    -- forgetCarrier.map (Free.map f) の定義を展開すると
    -- Preord.ofHom (forgetCarrierOrderHom (FreeMap f))
    -- その toFun は (FreeMap f).map = f
    
    -- したがって両辺とも f x に等しい
    change f x = (forgetCarrier.map (Free.map f)) x
    
    -- forgetCarrier_Free_map 補題により forgetCarrier.map (Free.map f) = f
    show f x = f x
    rfl

/-- 随伴の余単位: forgetCarrier ∘ Free ⟶ Id -/
def adjunctionCounit : forgetCarrier ⋙ Free ⟶ 𝟭 StructureTowerWithMin where
  app := fun T => {
    map := _root_.id
    indexMap := T.minLayer
    indexMap_mono := by
      intro i j hij
      -- carrierPreorderの定義により i ≤ j iff minLayer i ≤ minLayer j
      exact hij
    layer_preserving := by
      intro i x hx
      -- i : (Free.obj (forgetCarrier.obj T)).Index = T.carrier (with carrierPreorder)
      -- x : (Free.obj (forgetCarrier.obj T)).carrier = T.carrier
      -- hx : x ∈ (Free.obj ...).layer i = {y | y ≤ i} (carrierPreorderでの順序)
      --    つまり hx : T.minLayer x ≤ T.minLayer i
      
      -- 示すべき: id x ∈ T.layer (T.minLayer i)
      --          つまり x ∈ T.layer (T.minLayer i)
      
      -- T.minLayer i は i が属する最小の層なので
      -- i ∈ T.layer (T.minLayer i)
      have hi_mem : i ∈ T.layer (T.minLayer i) := T.minLayer_mem i
      
      -- hx より T.minLayer x ≤ T.minLayer i
      -- 単調性より T.layer (T.minLayer x) ⊆ T.layer (T.minLayer i)
      have h_mono : T.layer (T.minLayer x) ⊆ T.layer (T.minLayer i) := 
        T.monotone hx
      
      -- x ∈ T.layer (T.minLayer x) より
      have hx_mem : x ∈ T.layer (T.minLayer x) := T.minLayer_mem x
      
      -- したがって x ∈ T.layer (T.minLayer i)
      exact h_mono hx_mem
    minLayer_preserving := by
      intro x
      -- minLayer (id x) = minLayer x
      -- indexMap (minLayer x) = T.minLayer (minLayer x) ... ではない
      -- Free.obj の定義では minLayer = id なので
      -- minLayer x (in Free carrier sense) = id x = x
      -- indexMap は T.minLayer : T.carrier → T.Index
      -- でも x : forgetCarrier.obj T = T.carrier (with carrierPreorder)
      -- Free.obj では minLayer = id なので
      -- 示すべき: id = T.minLayer ... これは成り立たない
      
      -- 実は定義を見直す必要がある
      -- Free.obj (forgetCarrier.obj T) の carrier は T.carrier
      -- その minLayer は id : T.carrier → T.carrier
      -- したがって minLayer (id x) = id (id x) = x
      -- indexMap (minLayer x) = T.minLayer (minLayer x) ではなく
      -- ここでの minLayer は Free の意味での minLayer = id
      -- だから indexMap (id x) = T.minLayer x
      rfl
  }
  naturality := by
    intro T T' f
    apply Hom.ext
    · -- map成分の等式
      funext x
      -- 左辺: ((forgetCarrier ⋙ Free).map f ≫ adjunctionCounit.app T').map x
      --     = (adjunctionCounit.app T').map ((Free.map (forgetCarrier.map f)).map x)
      --     = id ((forgetCarrier.map f) x) = (forgetCarrier.map f) x = f.map x
      -- 右辺: (adjunctionCounit.app T ≫ f).map x
      --     = f.map ((adjunctionCounit.app T).map x) = f.map (id x) = f.map x
      rfl
    · -- indexMap成分の等式
      funext i
      -- i : (forgetCarrier.obj T).carrier = T.carrier
      
      -- 左辺: ((forgetCarrier ⋙ Free).map f ≫ adjunctionCounit.app T').indexMap i
      -- まず (forgetCarrier ⋙ Free).map f = Free.map (forgetCarrier.map f)
      -- この indexMap は (forgetCarrier.map f) そのもの (FreeMap の定義より)
      -- 合成すると: (adjunctionCounit.app T').indexMap ((forgetCarrier.map f) i)
      --            = T'.minLayer (f.map i)
      
      -- 右辺: (adjunctionCounit.app T ≫ f).indexMap i
      -- 合成の定義より: f.indexMap ((adjunctionCounit.app T).indexMap i)
      --                = f.indexMap (T.minLayer i)
      
      -- f.minLayer_preserving により T'.minLayer (f.map i) = f.indexMap (T.minLayer i)
      exact (f.minLayer_preserving i).symm

/-! ## 三角恒等式 -/

/-- 左三角恒等式: Free.map η_X ≫ ε_{F(X)} = id -/
theorem leftTriangleIdentity (X : Preord.{u}) :
    (Free.map (adjunctionUnit.app X)) ≫ (adjunctionCounit.app (Free.obj X)) = 𝟙 _ := by
  apply Hom.ext
  · -- map成分
    funext x
    -- adjunctionUnit.app X = id なので Free.map id = id
    -- adjunctionCounit.app の map も id
    -- したがって id ∘ id = id
    rfl
  · -- indexMap成分
    funext i
    -- adjunctionUnit.app X = id なので Free.map id の indexMap = id
    -- adjunctionCounit.app (Free.obj X) の indexMap = minLayer
    -- Free.obj X では minLayer = id
    -- したがって id ∘ id = id
    rfl

/-- 右三角恒等式: η_{U(T)} ≫ U(ε_T) = id -/
theorem rightTriangleIdentity (T : StructureTowerWithMin) :
    (adjunctionUnit.app (forgetCarrier.obj T)) ≫
    (forgetCarrier.map (adjunctionCounit.app T)) = 𝟙 _ := by
  apply Preord.ext
  funext x
  -- adjunctionUnit.app (forgetCarrier.obj T) = id
  -- forgetCarrier.map (adjunctionCounit.app T) の toFun
  --   = (adjunctionCounit.app T).map = id
  -- したがって id ∘ id = id
  rfl

/-! ## 随伴の構成（形式的） -/

/-- 自由構造塔関手と忘却関手は随伴をなす -/
def adjunction : Free ⊣ forgetCarrier where
  unit := adjunctionUnit
  counit := adjunctionCounit
  left_triangle := by
    ext X
    exact leftTriangleIdentity X
  right_triangle := by
    ext T
    exact rightTriangleIdentity T

end StructureTowerWithMin
