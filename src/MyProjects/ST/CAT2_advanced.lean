import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.ConcreteCategory.Basic

universe u v

/-!
# Structure Tower 発展課題 ST-CAT-002

## 難易度: レベル2-3（中級〜上級）
## テーマ: 関手と自然変換

前回の課題でStructureTowerが圏をなすことを示しました。
今回は：
1. 構造塔から他の圏への関手を定義
2. 関手の間の自然変換を構成
3. 忘却関手と自由構造塔の随伴関係を探求

## 学習目標
- 圏論的構成の実践的理解
- Mathlibの関手APIの使用
- 随伴関手の概念の形式化
-/

-- 前回の定義を再利用（実際には import する）
structure StructureTower where
  carrier : Type u
  Index : Type v
  [indexPreorder : Preorder Index]
  layer : Index → Set carrier
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j

instance instIndexPreorder (T : StructureTower.{u, v}) : Preorder T.Index :=
  T.indexPreorder

namespace StructureTower

variable {u v}
variable {T T' T'' T''' : StructureTower.{u, v}}

structure Hom (T T' : StructureTower.{u, v}) where
  map : T.carrier → T'.carrier
  indexMap : T.Index → T'.Index
  indexMap_mono : ∀ {i j : T.Index}, i ≤ j → indexMap i ≤ indexMap j
  layer_preserving : ∀ (i : T.Index) (x : T.carrier),
    x ∈ T.layer i → map x ∈ T'.layer (indexMap i)

@[ext]
lemma Hom.ext {f g : Hom T T'}
    (hmap : f.map = g.map) (hindex : f.indexMap = g.indexMap) :
    f = g := by
  cases f
  cases g
  simp_all

def Hom.comp (g : Hom T' T'') (f : Hom T T') : Hom T T'' where
  map := fun x => g.map (f.map x)
  indexMap := fun i => g.indexMap (f.indexMap i)
  indexMap_mono := by
    intro i j hij
    exact g.indexMap_mono (f.indexMap_mono hij)
  layer_preserving := by
    intro i x hx
    exact g.layer_preserving (f.indexMap i) (f.map x) (f.layer_preserving i x hx)

def Hom.id (T : StructureTower.{u, v}) : Hom T T where
  map := _root_.id
  indexMap := _root_.id
  indexMap_mono := fun hij => hij
  layer_preserving := fun _ _ hx => hx

instance : CategoryTheory.Category (StructureTower.{u, v}) where
  Hom := Hom
  id := Hom.id
  comp := fun f g => Hom.comp g f
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

end StructureTower

open CategoryTheory

/-! ## 課題1: 忘却関手 (Forgetful Functor) -/

/-- 構造塔から基礎集合への忘却関手
構造塔の階層構造を「忘れて」、基礎集合だけを取り出す -/
def forgetCarrier : StructureTower.{u, v} ⥤ Type u where
  obj := fun T => T.carrier
  map := fun f => f.map
  map_id := by
    intro T
    funext x
    rfl
  map_comp := by
    intro T T' T'' f g
    funext x
    rfl

/-- 構造塔から添字集合への忘却関手 -/
def forgetIndex : StructureTower.{u, v} ⥤ Type v where
  obj := fun T => T.Index
  map := fun f => f.indexMap
  map_id := by
    intro T
    funext i
    rfl
  map_comp := by
    intro T T' T'' f g
    funext i
    rfl

/-! ## 課題2: 層関手 (Layer Functor) -/

/-- 固定された添字 i における第 i 層を取り出す「関手的操作」
注意: これを厳密な関手にするには、添字の対応も考慮する必要がある -/

-- まず、添字が固定されている場合の簡単な版

-- i番目の層の要素全体を集合として取り出す操作
-- （これは関手ではないが、関手的な性質の準備）
def layerAt (T : StructureTower.{u, v}) (i : T.Index) : Set T.carrier :=
  T.layer i

-- 補題: 射 f が層を保存することの言い換え
lemma layer_functorial {T T' : StructureTower.{u, v}} (f : T ⟶ T') (i : T.Index) :
    f.map '' (T.layer i) ⊆ T'.layer (f.indexMap i) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact f.layer_preserving i x hx

/-! ## 課題3: 構造塔の構造を保つ同型 -/

namespace StructureTower

/-- 構造塔の同型射 -/
structure Iso (T T' : StructureTower.{u, v}) where
  hom : T ⟶ T'
  inv : T' ⟶ T
  hom_inv_id : hom ≫ inv = 𝟙 T
  inv_hom_id : inv ≫ hom = 𝟙 T'

namespace Iso

variable {T T' T'' : StructureTower.{u, v}}

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
def refl (T : StructureTower.{u, v}) : Iso T T where
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
    have hcomp := congrArg StructureTower.Hom.map f.hom_inv_id
    have hx := congrFun hcomp x
    have hy := congrFun hcomp y
    have := congrArg (fun z => f.inv.map z) hxy
    calc
      x = f.inv.map (f.hom.map x) := by simpa using hx.symm
      _ = f.inv.map (f.hom.map y) := by simpa using this
      _ = y := by simpa [hy]
  · -- 全射性
    intro y
    have hcomp := congrArg StructureTower.Hom.map f.inv_hom_id
    have hy := congrFun hcomp y
    refine ⟨f.inv.map y, ?_⟩
    exact hy

end Iso

end StructureTower

/-! ## 課題4: 自由構造塔と随伴関手（発展） -/

/-- 集合 X から生成される最も簡単な構造塔
各要素を単独の層とする -/
def freeStructureTower (X : Type u) : StructureTower.{u, u} where
  carrier := X
  Index := X
  indexPreorder := by
    classical
    refine
      { le := fun i j => i = j
        lt := fun _ _ => False
        le_refl := fun i => rfl
        le_trans := by
          intro a b c hab hbc
          exact hab.trans hbc
        lt_iff_le_not_ge := by
          intro a b
          constructor
          · intro h
            cases h
          · rintro ⟨h₁, h₂⟩
            exact h₂ (by simpa using h₁.symm) }
  layer := fun i => {i}
  covering := by
    intro x
    refine ⟨x, ?_⟩
    rfl
  monotone := by
    intro i j hij x hx
    cases hij
    simpa using hx

/-- 補題: 自由構造塔の普遍性
任意の写像 f : X → T.carrier に対して、一意的な構造塔の射が存在する -/
lemma freeStructureTower_universal (X : Type u) (T : StructureTower.{u, u}) (f : X → T.carrier) :
    ∃! (φ : freeStructureTower X ⟶ T),
      ∀ x : X, φ.map x = f x := by
  -- TODO: 存在性と一意性を示す（チャレンジング！）
  -- ヒント: covering を使って、各 f(x) がある層に含まれることを利用
  sorry

/-! ## 課題5: 自然変換 -/

section

-- 2つの関手の間の自然変換を定義する準備
-- 例: forgetCarrier から forgetCarrier への自然変換（恒等）

/-- 恒等自然変換の成分 -/
def idNatTransComponent (T : StructureTower.{u, v}) : T.carrier → T.carrier :=
  _root_.id

/-- 補題: これが自然変換の条件を満たすことの検証 -/
lemma idNatTrans_naturality {T T' : StructureTower.{u, v}} (f : T ⟶ T') :
    f.map ∘ idNatTransComponent T = idNatTransComponent T' ∘ f.map := by
  funext x
  rfl

-- より非自明な例: ある種の「対角化」操作

-- 層の情報を付加する操作（擬似的な例）
-- これは正確には関手ではないが、自然変換的な構造の例示

-- ## 課題6: 構造塔の直積の関手性

/-- 二つの構造塔の直積 -/
def prod (T₁ T₂ : StructureTower.{u, v}) : StructureTower.{u, v} where
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

/-- 直積の射への作用 -/
def prodMap {T₁ T₁' T₂ T₂' : StructureTower.{u, v}}
    (f₁ : T₁ ⟶ T₁') (f₂ : T₂ ⟶ T₂') : prod T₁ T₂ ⟶ prod T₁' T₂' where
  map := fun ⟨x, y⟩ => ⟨f₁.map x, f₂.map y⟩
  indexMap := fun ⟨i, j⟩ => ⟨f₁.indexMap i, f₂.indexMap j⟩
  indexMap_mono := by
    intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ ⟨hi, hj⟩
    exact ⟨f₁.indexMap_mono hi, f₂.indexMap_mono hj⟩
  layer_preserving := by
    intro ⟨i, j⟩ ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨f₁.layer_preserving i x hx, f₂.layer_preserving j y hy⟩

/-- 補題: prodMap は恒等射を保存 -/
lemma prodMap_id (T₁ T₂ : StructureTower.{u, v}) :
    prodMap (𝟙 T₁) (𝟙 T₂) = 𝟙 (prod T₁ T₂) := by
  rfl

/-- 補題: prodMap は合成を保存 -/
lemma prodMap_comp {T₁ T₁' T₁'' T₂ T₂' T₂'' : StructureTower.{u, v}}
    (f₁ : T₁ ⟶ T₁') (g₁ : T₁' ⟶ T₁'')
    (f₂ : T₂ ⟶ T₂') (g₂ : T₂' ⟶ T₂'') :
    prodMap (f₁ ≫ g₁) (f₂ ≫ g₂) = prodMap f₁ f₂ ≫ prodMap g₁ g₂ := by
  rfl

/-!
## 課題7: 圏論的極限（チャレンジング）

構造塔の圏における積が上で定義した prod であることを示す。
これには：
1. 射影射の定義
2. 普遍性の証明
が必要。

これは非常に高度な課題なので、まずは上の課題を完成させてから挑戦してください。
-/

-- 射影射
def proj₁ (T₁ T₂ : StructureTower.{u, v}) : prod T₁ T₂ ⟶ T₁ where
  map := Prod.fst
  indexMap := Prod.fst
  indexMap_mono := fun h => h.1
  layer_preserving := fun _ _ h => h.1

def proj₂ (T₁ T₂ : StructureTower.{u, v}) : prod T₁ T₂ ⟶ T₂ where
  map := Prod.snd
  indexMap := Prod.snd
  indexMap_mono := fun h => h.2
  layer_preserving := fun _ _ h => h.2

/-- 普遍性: 積への射の一意的な構成 -/
def prodUniversal {T T₁ T₂ : StructureTower.{u, v}} (f₁ : T ⟶ T₁) (f₂ : T ⟶ T₂) :
    T ⟶ prod T₁ T₂ where
  map := fun x => ⟨f₁.map x, f₂.map x⟩
  indexMap := fun i => ⟨f₁.indexMap i, f₂.indexMap i⟩
  indexMap_mono := by
    intro i j hij
    exact ⟨f₁.indexMap_mono hij, f₂.indexMap_mono hij⟩
  layer_preserving := by
    intro i x hx
    exact ⟨f₁.layer_preserving i x hx, f₂.layer_preserving i x hx⟩

/-- 普遍射が射影と可換 -/
lemma prodUniversal_proj₁ {T T₁ T₂ : StructureTower.{u, v}} (f₁ : T ⟶ T₁) (f₂ : T ⟶ T₂) :
    prodUniversal f₁ f₂ ≫ proj₁ T₁ T₂ = f₁ := by
  rfl

lemma prodUniversal_proj₂ {T T₁ T₂ : StructureTower.{u, v}} (f₁ : T ⟶ T₁) (f₂ : T ⟶ T₂) :
    prodUniversal f₁ f₂ ≫ proj₂ T₁ T₂ = f₂ := by
  rfl

/-- 対角射の具体例: 恒等射から得られる普遍射の成分は対角写像になる -/
example (T : StructureTower.{u, v}) (x : T.carrier) :
    (prodUniversal (𝟙 T) (𝟙 T)).map x = ⟨x, x⟩ := by
  rfl

/-- 一意性 -/
lemma prodUniversal_unique {T T₁ T₂ : StructureTower.{u, v}} (f₁ : T ⟶ T₁) (f₂ : T ⟶ T₂)
    (g : T ⟶ prod T₁ T₂) (h₁ : g ≫ proj₁ T₁ T₂ = f₁) (h₂ : g ≫ proj₂ T₁ T₂ = f₂) :
    g = prodUniversal f₁ f₂ := by
  -- TODO: 証明を仕上げ、構成の一意性を形式化する
  sorry

/-! ## ボーナス課題: 関手の合成 -/

-- forgetCarrier と forgetIndex を使って、より複雑な関手を構成してみよう

/-! ## ヒント集 -/

/- 
### 関手の証明のヒント
- `map_id`: 定義を展開すると `rfl` で証明できることが多い
- `map_comp`: 合成の定義を追えば自然に示せる

### 同型の証明のヒント  
- 逆射を適用して元に戻ることを示す
- CategoryTheory の `≫` は右から左への合成なので注意

### 普遍性の証明のヒント
- 一意性は「2つの射が条件を満たせば等しい」を示す
- 存在性は具体的に射を構成する

### 自由構造塔のヒント
- 離散順序では i ≤ j ⟺ i = j
- 層 {i} は単元集合なので、包含関係は等式に帰着
-/

/-! ## この課題で学ぶこと -/

/-
1. **圏論の基本概念の実践**
   - 関手の定義と性質
   - 自然変換
   - 普遍性

2. **Mathlibの圏論ライブラリの使用法**
   - Functor型
   - 射の合成記法 (≫)
   - 圏の公理の扱い

3. **構造の保存と忘却**
   - 忘却関手の意味
   - 自由構造と随伴関手
   - 構造の輸送

4. **形式的証明の技法**
   - 関数外延性
   - 構造体の等式
   - 普遍性の証明パターン
-/
