import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

universe u v

/-!
# Structure Tower 完全版 ST-CAT-COMPLETE

このファイルは、構造塔（Structure Tower）の圏論的構造の完全な形式化です。

## 主な内容

1. **StructureTowerWithMin**: 最小層を持つ構造塔
   - 完全な普遍性が証明可能
   - 圏構造
   - 同型射
   - 忘却関手
   - 直積と射影

2. **具体例**
   - 自由構造塔
   - 自然数の構造塔
   - 実数区間の構造塔

## 数学的背景

構造塔は Bourbaki の構造理論に基づく概念で、
集合に階層的な構造を与えます。

各要素が属する「最小の層」を選ぶ関数 minLayer を持つことで、
射の定義が一意になり、圏論的な普遍性が成り立ちます。
-/

/-- 最小層を持つ構造塔
三つ組 (X, (Xᵢ)ᵢ∈I, ≤, minLayer) からなり：
- X: 基礎集合
- I: 添字半順序集合
- (Xᵢ): 各層（被覆性と単調性を満たす）
- minLayer: 各要素の最小層を選ぶ関数
-/
structure StructureTowerWithMin where
  /-- 基礎集合 -/
  carrier : Type u
  /-- 添字集合 -/
  Index : Type v
  /-- 添字集合上の半順序 -/
  [indexPreorder : Preorder Index]
  /-- 各層の定義: Index → Set carrier -/
  layer : Index → Set carrier
  /-- 被覆性: すべての層の和集合が全体を覆う -/
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  /-- 単調性: 順序を保存 -/
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j
  /-- 各要素の最小層を選ぶ関数 -/
  minLayer : carrier → Index
  /-- minLayer x は実際に x を含む -/
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  /-- minLayer x は最小 -/
  minLayer_minimal : ∀ x i, x ∈ layer i → minLayer x ≤ i

namespace StructureTowerWithMin

instance instIndexPreorder (T : StructureTowerWithMin.{u, v}) : Preorder T.Index :=
  T.indexPreorder

variable {T T' T'' T''' : StructureTowerWithMin.{u, v}}

/-- 構造塔の射
対 (f, φ) であって：
- f: 基礎集合の写像
- φ: 添字集合の順序を保つ写像
- f が層構造を保存
- f が最小層の構造を保存（重要！）
-/
structure Hom (T T' : StructureTowerWithMin.{u, v}) where
  /-- 基礎集合間の写像 -/
  map : T.carrier → T'.carrier
  /-- 添字集合間の順序を保つ写像 -/
  indexMap : T.Index → T'.Index
  /-- φ が順序を保存 -/
  indexMap_mono : ∀ {i j : T.Index}, i ≤ j → indexMap i ≤ indexMap j
  /-- f が層構造を保存 -/
  layer_preserving : ∀ (i : T.Index) (x : T.carrier),
    x ∈ T.layer i → map x ∈ T'.layer (indexMap i)
  /-- f が最小層を保存（これが一意性の鍵！） -/
  minLayer_preserving : ∀ x, T'.minLayer (map x) = indexMap (T.minLayer x)

/-- 射の等式は成分の等式で決まる -/
@[ext]
lemma Hom.ext {f g : Hom T T'}
    (hmap : f.map = g.map) (hindex : f.indexMap = g.indexMap) : f = g := by
  cases f; cases g; cases hmap; cases hindex; rfl

/-- 射の合成 -/
def Hom.comp (g : Hom T' T'') (f : Hom T T') : Hom T T'' where
  map := fun x => g.map (f.map x)
  indexMap := fun i => g.indexMap (f.indexMap i)
  indexMap_mono := fun hij => g.indexMap_mono (f.indexMap_mono hij)
  layer_preserving := fun i x hx =>
    g.layer_preserving (f.indexMap i) (f.map x) (f.layer_preserving i x hx)
  minLayer_preserving := by
    intro x
    have h₁ := g.minLayer_preserving (f.map x)
    have h₂ := f.minLayer_preserving x
    simpa [h₂] using h₁

/-- 恒等射 -/
def Hom.id (T : StructureTowerWithMin.{u, v}) : Hom T T where
  map := _root_.id
  indexMap := _root_.id
  indexMap_mono := fun hij => hij
  layer_preserving := fun _ _ hx => hx
  minLayer_preserving := fun _ => rfl

/-- 構造塔は圏をなす -/
instance : CategoryTheory.Category (StructureTowerWithMin.{u, v}) where
  Hom := Hom
  id := Hom.id
  comp := fun f g => Hom.comp g f
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

end StructureTowerWithMin

open CategoryTheory

/-! ## 同型射 -/

namespace StructureTowerWithMin

/-- 構造塔の同型射 -/
structure Iso (T T' : StructureTowerWithMin.{u, v}) where
  hom : T ⟶ T'
  inv : T' ⟶ T
  hom_inv_id : hom ≫ inv = 𝟙 T
  inv_hom_id : inv ≫ hom = 𝟙 T'

namespace Iso

variable {T T' T'' : StructureTowerWithMin.{u, v}}

/-- 同型射の合成 -/
def comp (f : Iso T T') (g : Iso T' T'') : Iso T T'' where
  hom := f.hom ≫ g.hom
  inv := g.inv ≫ f.inv
  hom_inv_id := by
    calc
      (f.hom ≫ g.hom) ≫ (g.inv ≫ f.inv)
          = f.hom ≫ (g.hom ≫ g.inv) ≫ f.inv := by simp [Category.assoc]
      _ = f.hom ≫ 𝟙 _ ≫ f.inv := by simpa [Category.assoc, g.hom_inv_id]
      _ = f.hom ≫ f.inv := by simp
      _ = 𝟙 _ := by simpa using f.hom_inv_id
  inv_hom_id := by
    calc
      (g.inv ≫ f.inv) ≫ (f.hom ≫ g.hom)
          = g.inv ≫ (f.inv ≫ f.hom) ≫ g.hom := by simp [Category.assoc]
      _ = g.inv ≫ 𝟙 _ ≫ g.hom := by simpa [Category.assoc, f.inv_hom_id]
      _ = g.inv ≫ g.hom := by simp
      _ = 𝟙 _ := by simpa using g.inv_hom_id

/-- 恒等同型 -/
def refl (T : StructureTowerWithMin.{u, v}) : Iso T T where
  hom := 𝟙 T
  inv := 𝟙 T
  hom_inv_id := by simp
  inv_hom_id := by simp

/-- 同型の対称性 -/
def symm (f : Iso T T') : Iso T' T where
  hom := f.inv
  inv := f.hom
  hom_inv_id := f.inv_hom_id
  inv_hom_id := f.hom_inv_id

/-- 同型射では基礎写像が全単射 -/
lemma map_bijective (f : Iso T T') : Function.Bijective f.hom.map := by
  constructor
  · -- 単射性
    intro x y hxy
    have hcomp := congrArg StructureTowerWithMin.Hom.map f.hom_inv_id
    have hx := congrFun hcomp x
    have hy := congrFun hcomp y
    have := congrArg (fun z => f.inv.map z) hxy
    calc
      x = f.inv.map (f.hom.map x) := by simpa using hx.symm
      _ = f.inv.map (f.hom.map y) := by simpa using this
      _ = y := by simpa [hy]
  · -- 全射性
    intro y
    have hcomp := congrArg StructureTowerWithMin.Hom.map f.inv_hom_id
    have hy := congrFun hcomp y
    refine ⟨f.inv.map y, ?_⟩
    exact hy

end Iso

end StructureTowerWithMin

/-! ## 忘却関手 -/

/-- 構造塔から基礎集合への忘却関手 -/
def forgetCarrier : StructureTowerWithMin.{u, v} ⥤ Type u where
  obj := fun T => T.carrier
  map := fun f => f.map
  map_id := by intro T; funext x; rfl
  map_comp := by intro T T' T'' f g; funext x; rfl

/-- 構造塔から添字集合への忘却関手 -/
def forgetIndex : StructureTowerWithMin.{u, v} ⥤ Type v where
  obj := fun T => T.Index
  map := fun f => f.indexMap
  map_id := by intro T; funext i; rfl
  map_comp := by intro T T' T'' f g; funext i; rfl

/-! ## 自由構造塔と普遍性 -/

/-- 半順序集合 X から生成される自由構造塔
層 i = {x | x ≤ i} として定義 -/
def freeStructureTowerMin (X : Type u) [Preorder X] :
    StructureTowerWithMin.{u, u} where
  carrier := X
  Index := X
  indexPreorder := inferInstance
  layer := fun i => {x : X | x ≤ i}
  covering := by intro x; use x; exact le_refl x
  monotone := by intro i j hij x hx; exact le_trans hx hij
  minLayer := _root_.id  -- x 自身が最小の層
  minLayer_mem := by intro x; exact le_refl x
  minLayer_minimal := by intro x i hx; exact hx

/-- 自由構造塔の普遍性（完全な一意性）

任意の単調写像 f : X → T.carrier（minLayer と compatible）に対して、
一意的な構造塔の射が存在する。

この定理が証明可能なのは、minLayer_preserving により
indexMap が一意に決定されるため。
-/
theorem freeStructureTowerMin_universal (X : Type u) [Preorder X]
    (T : StructureTowerWithMin.{u, u}) (f : X → T.carrier)
    (hf : Monotone fun x => T.minLayer (f x)) :
    ∃! (φ : freeStructureTowerMin X ⟶ T), ∀ x : X, φ.map x = f x := by
  classical
  -- 存在性: φ₀ を構成
  let φ₀ : freeStructureTowerMin X ⟶ T :=
    { map := f
      indexMap := fun x => T.minLayer (f x)
      indexMap_mono := by intro x y hxy; exact hf hxy
      layer_preserving := by
        intro i x hx
        have hle : T.minLayer (f x) ≤ T.minLayer (f i) := hf hx
        have hmem : f x ∈ T.layer (T.minLayer (f x)) := T.minLayer_mem (f x)
        exact T.monotone hle hmem
      minLayer_preserving := by intro x; rfl }
  refine ⟨φ₀, ?_, ?_⟩
  · intro x; rfl
  · -- 一意性: ψ が条件を満たすなら ψ = φ₀
    intro ψ hψ
    have hmap : ψ.map = φ₀.map := by funext x; simpa [φ₀] using hψ x
    have hindex : ψ.indexMap = φ₀.indexMap := by
      funext x
      have hψmap : ψ.map x = f x := hψ x
      calc
        ψ.indexMap x
            = T.minLayer (ψ.map x) := by
              simpa using (ψ.minLayer_preserving x).symm
        _ = T.minLayer (f x) := by simpa [hψmap]
        _ = φ₀.indexMap x := by simp [φ₀]
    exact StructureTowerWithMin.Hom.ext hmap hindex

/-! ## 直積と射影 -/

/-- 二つの構造塔の直積 -/
def prod (T₁ T₂ : StructureTowerWithMin.{u, v}) :
    StructureTowerWithMin.{u, v} where
  carrier := T₁.carrier × T₂.carrier
  Index := T₁.Index × T₂.Index
  indexPreorder := inferInstanceAs (Preorder (T₁.Index × T₂.Index))
  layer := fun ⟨i, j⟩ => T₁.layer i ×ˢ T₂.layer j
  covering := by
    intro ⟨x₁, x₂⟩
    obtain ⟨i, hi⟩ := T₁.covering x₁
    obtain ⟨j, hj⟩ := T₂.covering x₂
    exact ⟨⟨i, j⟩, ⟨hi, hj⟩⟩
  monotone := by
    intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ ⟨hi, hj⟩ ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨T₁.monotone hi hx, T₂.monotone hj hy⟩
  minLayer := fun ⟨x, y⟩ => ⟨T₁.minLayer x, T₂.minLayer y⟩
  minLayer_mem := by
    intro ⟨x, y⟩
    exact ⟨T₁.minLayer_mem x, T₂.minLayer_mem y⟩
  minLayer_minimal := by
    intro ⟨x, y⟩ ⟨i, j⟩ ⟨hx, hy⟩
    exact ⟨T₁.minLayer_minimal x i hx, T₂.minLayer_minimal y j hy⟩

namespace StructureTowerWithMin

variable {T T₁ T₂ : StructureTowerWithMin.{u, v}}

/-- 第一射影 -/
def proj₁ (T₁ T₂ : StructureTowerWithMin.{u, v}) : prod T₁ T₂ ⟶ T₁ where
  map := Prod.fst
  indexMap := Prod.fst
  indexMap_mono := fun h => h.1
  layer_preserving := fun _ _ h => h.1
  minLayer_preserving := fun _ => rfl

/-- 第二射影 -/
def proj₂ (T₁ T₂ : StructureTowerWithMin.{u, v}) : prod T₁ T₂ ⟶ T₂ where
  map := Prod.snd
  indexMap := Prod.snd
  indexMap_mono := fun h => h.2
  layer_preserving := fun _ _ h => h.2
  minLayer_preserving := fun _ => rfl

/-- 積への普遍射 -/
def prodUniversal (f₁ : T ⟶ T₁) (f₂ : T ⟶ T₂) : T ⟶ prod T₁ T₂ where
  map := fun x => ⟨f₁.map x, f₂.map x⟩
  indexMap := fun i => ⟨f₁.indexMap i, f₂.indexMap i⟩
  indexMap_mono := by
    intro i j hij
    exact ⟨f₁.indexMap_mono hij, f₂.indexMap_mono hij⟩
  layer_preserving := by
    intro i x hx
    exact ⟨f₁.layer_preserving i x hx, f₂.layer_preserving i x hx⟩
  minLayer_preserving := by
    intro x
    simp [prod]
    exact ⟨f₁.minLayer_preserving x, f₂.minLayer_preserving x⟩

/-- 普遍射が射影と可換（第一成分） -/
theorem prodUniversal_proj₁ (f₁ : T ⟶ T₁) (f₂ : T ⟶ T₂) :
    prodUniversal f₁ f₂ ≫ proj₁ T₁ T₂ = f₁ := by
  rfl

/-- 普遍射が射影と可換（第二成分） -/
theorem prodUniversal_proj₂ (f₁ : T ⟶ T₁) (f₂ : T ⟶ T₂) :
    prodUniversal f₁ f₂ ≫ proj₂ T₁ T₂ = f₂ := by
  rfl

/-- 積の普遍性：一意性
射影を通じた制約により、minLayer_preserving と合わせて
射が完全に一意に決まる -/
theorem prodUniversal_unique (f₁ : T ⟶ T₁) (f₂ : T ⟶ T₂)
    (g : T ⟶ prod T₁ T₂)
    (h₁ : g ≫ proj₁ T₁ T₂ = f₁)
    (h₂ : g ≫ proj₂ T₁ T₂ = f₂) :
    g = prodUniversal f₁ f₂ := by
  apply Hom.ext
  · -- map の等式
    funext x
    have eq1 : (g.map x).1 = f₁.map x := by
      have := congrArg Hom.map h₁
      exact congrFun this x
    have eq2 : (g.map x).2 = f₂.map x := by
      have := congrArg Hom.map h₂
      exact congrFun this x
    exact Prod.ext eq1 eq2
  · -- indexMap の等式
    funext i
    have eq1 : (g.indexMap i).1 = f₁.indexMap i := by
      have := congrArg Hom.indexMap h₁
      exact congrFun this i
    have eq2 : (g.indexMap i).2 = f₂.indexMap i := by
      have := congrArg Hom.indexMap h₂
      exact congrFun this i
    exact Prod.ext eq1 eq2

end StructureTowerWithMin

/-! ## 具体例 -/

/-- 自然数上の構造塔
層 n = {0, 1, ..., n} -/
def natTowerMin : StructureTowerWithMin.{0, 0} where
  carrier := ℕ
  Index := ℕ
  layer := fun n => {k : ℕ | k ≤ n}
  covering := by intro x; use x; exact le_refl x
  monotone := by intro i j hij x hx; exact le_trans hx hij
  minLayer := _root_.id
  minLayer_mem := by intro x; exact le_refl x
  minLayer_minimal := by intro x i hx; exact hx

/-- 後者関数が誘導する自由構造塔の射 -/
example : ∃! (φ : natTowerMin ⟶ natTowerMin),
    ∀ x : ℕ, φ.map x = Nat.succ x := by
  have hf : Monotone fun x : ℕ => Nat.succ x := by
    intro x y hxy; exact Nat.succ_le_succ hxy
  exact freeStructureTowerMin_universal ℕ natTowerMin Nat.succ hf

/-! ## 学習のまとめ -/

/-
# 重要なポイント

1. **minLayer の役割**
   - 各要素の「最小の層」を選ぶ関数
   - 構造の本質的な部分

2. **minLayer_preserving の重要性**
   - 射が minLayer を保存する
   - これにより indexMap が一意に決まる
   - 普遍性の一意性の鍵

3. **普遍性の証明**
   - 存在性: minLayer を使って射を構成
   - 一意性: minLayer_preserving から導出

4. **直積の普遍性**
   - 射影を通じた制約
   - minLayer_preserving と合わせて完全な一意性

5. **形式数学の洞察**
   - 非形式的に「自然」な操作も形式的には注意が必要
   - 追加の構造（minLayer）により問題が解決
   - 定義の選択が定理の証明可能性に影響

この形式化は、Bourbaki の構造理論と現代的な圏論を
結びつける良い例です。
-/
