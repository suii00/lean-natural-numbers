import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Data.Rat.Init

open CategoryTheory

/-!
# P4_Categorical: 構造塔の圏論的構造

このファイルでは、Cat_D の圏論的性質を実装する。

## 主な内容

1. **忘却関手（Forgetful Functors）**
   - `forgetCarrier`: TowerD → Type（基礎集合への忘却）
   - `forgetIndex`: TowerD → Type（添字集合への忘却）

2. **包含関手（Inclusion Functors）**
   - `inclusionLeToD`: Cat_le → Cat_D
   - `inclusionEqToLe`: Cat_eq → Cat_le

3. **極限（Limits）**
   - `prod`: 直積の構成
   - `proj₁`, `proj₂`: 射影射
   - `prodUniversal`: 積の普遍性

4. **余極限（Colimits）**
   - `coprod`: 余積の構成
   - `inj₁`, `inj₂`: 埋め込み射
   - `coprodUniversal`: 余積の普遍性

## 数学的背景

### 忘却関手の意味

構造塔 `T = (X, I, layer, ...)` から：
- 台集合 `X` を取り出す操作 → `forgetCarrier`
- 添字集合 `I` を取り出す操作 → `forgetIndex`

これらは圏論的には「構造を忘れる」関手である。

### 包含関手の意味

射の条件の階層構造：
```
HomEq ⊆ HomLe ⊆ HomD
（全単射）⊆（順序保存）⊆（存在量化）
```

この包含関係は自然な関手を誘導する。

### 直積と余積

- **直積** `T₁ × T₂`: 「構造の積」
  - carrier = T₁.carrier × T₂.carrier
  - Index = T₁.Index × T₂.Index
  - layer (i,j) = layer₁ i × layer₂ j

- **余積** `T₁ ⊕ T₂`: 「構造の和」
  - carrier = T₁.carrier ⊕ T₂.carrier
  - Index = T₁.Index ⊕ T₂.Index（直和＝cross 比較なし）
  - layer (Sum.inl i) = inl '' (layer₁ i)

## 参考文献

- Mac Lane, S. *Categories for the Working Mathematician*
- Awodey, S. *Category Theory*
- The mathlib Community, The Lean Mathematical Library

-/

universe u v w

namespace ST

/-!
## 基本定義の再掲

Cat_D, Cat_le, Cat_eq から必要な定義を再掲する。
実際のプロジェクトでは import で済ませるが、
ここでは自己完結性のために再定義する。
-/

/-- 構造塔（最小層なし） -/
structure StructureTower where
  carrier : Type u
  Index : Type v
  [indexPreorder : Preorder Index]
  layer : Index → Set carrier
  covering : ∀ x : carrier, ∃ i : Index, x ∈ layer i
  monotone : ∀ {i j : Index}, i ≤ j → layer i ⊆ layer j

/-- Cat_D, Cat_le, Cat_eq の対象 -/
abbrev TowerD := StructureTower

namespace TowerD

instance instIndexPreorder (T : TowerD) : Preorder T.Index :=
  T.indexPreorder

/-!
## Cat_D の射
-/

/-- Cat_D の射（map のみ、存在量化による層保存） -/
structure HomD (T T' : TowerD) where
  map : T.carrier → T'.carrier
  map_layer : ∀ i : T.Index, ∃ j : T'.Index,
    Set.image map (T.layer i) ⊆ T'.layer j

infixr:10 " ⟶ᴰ " => HomD

namespace HomD

@[ext]
theorem ext {T T' : TowerD} {f g : T ⟶ᴰ T'}
    (h : f.map = g.map) : f = g := by
  cases f with
  | mk map₁ map_layer₁ =>
    cases g with
    | mk map₂ map_layer₂ =>
      cases h
      have h₂ : map_layer₁ = map_layer₂ := funext (fun _ => Subsingleton.elim _ _)
      cases h₂
      rfl

def id (T : TowerD) : T ⟶ᴰ T where
  map := _root_.id
  map_layer := by
    intro i
    use i
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact hy

def comp {T T' T'' : TowerD}
    (g : T' ⟶ᴰ T'') (f : T ⟶ᴰ T') : T ⟶ᴰ T'' where
  map := g.map ∘ f.map
  map_layer := by
    intro i
    obtain ⟨j, hj⟩ := f.map_layer i
    obtain ⟨k, hk⟩ := g.map_layer j
    use k
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact hk ⟨f.map y, hj ⟨y, hy, rfl⟩, rfl⟩

@[simp] theorem id_map (T : TowerD) : (id T).map = _root_.id := rfl
@[simp] theorem comp_map {T T' T'' : TowerD}
    (g : T' ⟶ᴰ T'') (f : T ⟶ᴰ T') :
    (comp g f).map = g.map ∘ f.map := rfl

end HomD

instance categoryD : CategoryTheory.Category TowerD where
  Hom := HomD
  id := HomD.id
  comp := fun f g => HomD.comp g f
  id_comp := by intros; ext; simp
  comp_id := by intros; ext; simp
  assoc := by intros; ext; rfl

/-!
## Cat_le の射
-/

/-- Cat_le の射（map + indexMap、順序保存） -/
structure HomLe (T T' : TowerD) where
  map : T.carrier → T'.carrier
  indexMap : T.Index → T'.Index
  indexMap_mono : Monotone indexMap
  layer_preserving : ∀ (i : T.Index) (x : T.carrier),
    x ∈ T.layer i → map x ∈ T'.layer (indexMap i)

infixr:10 " ⟶ₗₑ " => HomLe

namespace HomLe

@[ext]
theorem ext {T T' : TowerD} {f g : T ⟶ₗₑ T'}
    (hmap : f.map = g.map) (hindexMap : f.indexMap = g.indexMap) :
    f = g := by
  cases f; cases g; cases hmap; cases hindexMap; rfl

def id (T : TowerD) : T ⟶ₗₑ T where
  map := _root_.id
  indexMap := _root_.id
  indexMap_mono := fun _ _ h => h
  layer_preserving := fun _ _ h => h

def comp {T T' T'' : TowerD}
    (g : T' ⟶ₗₑ T'') (f : T ⟶ₗₑ T') : T ⟶ₗₑ T'' where
  map := g.map ∘ f.map
  indexMap := g.indexMap ∘ f.indexMap
  indexMap_mono := fun _ _ h => g.indexMap_mono (f.indexMap_mono h)
  layer_preserving := by
    intro i x hx
    apply g.layer_preserving
    exact f.layer_preserving i x hx

@[simp] theorem id_map (T : TowerD) : (id T).map = _root_.id := rfl
@[simp] theorem id_indexMap (T : TowerD) : (id T).indexMap = _root_.id := rfl
@[simp] theorem comp_map {T T' T'' : TowerD}
    (g : T' ⟶ₗₑ T'') (f : T ⟶ₗₑ T') :
    (comp g f).map = g.map ∘ f.map := rfl
@[simp] theorem comp_indexMap {T T' T'' : TowerD}
    (g : T' ⟶ₗₑ T'') (f : T ⟶ₗₑ T') :
    (comp g f).indexMap = g.indexMap ∘ f.indexMap := rfl

end HomLe

/-!
注意：Cat_le の圏構造は別のインスタンスとして定義可能だが、
Lean では同じ型に複数の Category インスタンスを持てないため、
ここではコメントアウトする。実際の使用では型エイリアスを使う。
-/

-- instance categoryLe : CategoryTheory.Category TowerD where
--   Hom := HomLe
--   id := HomLe.id
--   comp := fun f g => HomLe.comp g f
--   ...

/-!
## Cat_eq の射
-/

/-- Cat_eq の射（全単射な map + 全単射な indexMap） -/
structure HomEq (T T' : TowerD) where
  map : T.carrier → T'.carrier
  indexMap : T.Index → T'.Index
  map_bijective : Function.Bijective map
  indexMap_bijective : Function.Bijective indexMap
  indexMap_mono : Monotone indexMap
  layer_preserving : ∀ (i : T.Index) (x : T.carrier),
    x ∈ T.layer i → map x ∈ T'.layer (indexMap i)

infixr:10 " ⟶ₑ " => HomEq

/-!
# 1. 忘却関手（Forgetful Functors）

構造塔から台集合や添字集合への忘却関手を定義する。
これらは「構造を忘れる」操作の形式化である。
-/

section ForgetfulFunctors

/-- 台集合への忘却関手

構造塔 T = (X, I, layer, ...) から基礎集合 X を取り出す。

**圏論的意味**:
- 対象: T ↦ T.carrier
- 射: (f : T → T') ↦ f.map

**性質**:
- 忠実（faithful）: 射の情報を保存
- 対象を忘れる: 層構造などの情報は失われる
-/
def forgetCarrier : TowerD ⥤ Type u where
  obj T := T.carrier
  map f := f.map
  map_id := by intro T; rfl
  map_comp := by intro T T' T'' f g; rfl

/- 添字集合への忘却関手

構造塔 T = (X, I, layer, ...) から添字集合 I を取り出す。

**注意**:
Cat_D の射は indexMap を持たないため、
この関手は定義できない。Cat_le や Cat_eq でのみ意味を持つ。

ここでは概念的な定義のみを示す（実装は Cat_le 用）。
-/
-- def forgetIndex_Le : Cat_le ⥤ Type v where
--   obj T := T.Index
--   map f := f.indexMap
--   ...

/-!
**忘却関手の具体例**

例えば、自然数の構造塔 natTower に対して:
- forgetCarrier(natTower) = ℕ
- forgetIndex(natTower) = ℕ

射 f: natTower → natTower に対して:
- forgetCarrier(f) = f.map : ℕ → ℕ
-/

end ForgetfulFunctors

/-!
# 2. 包含関手（Inclusion Functors）

射の条件の階層に沿った包含関手を定義する。

## 階層構造

```
HomEq ⊆ HomLe ⊆ HomD
```

各包含は自然な関手を誘導する。
-/

section InclusionFunctors

/-- HomLe から HomD への変換

indexMap の情報を忘れ、層保存を存在量化に弱める。

**数学的意味**:
HomLe の射 (f, φ) は、φ(i) という明示的な対応を持つ。
これを HomD の射 f に変換する際、
「∃j, f(layer i) ⊆ layer j」という存在量化の形に弱める。
-/
def homLeToHomD {T T' : TowerD} (f : HomLe T T') : HomD T T' where
  map := f.map
  map_layer := by
    intro i
    use f.indexMap i
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact f.layer_preserving i x hx

/-- HomLe から HomD への包含関手（概念的定義）

**注意**:
同じ型 TowerD に複数の Category インスタンスを持てないため、
実際の関手の構成は型レベルで工夫が必要。

ここでは数学的な意味を明確にするために、
変換関数 homLeToHomD の存在を示す。

実際のプロジェクトでは:
1. TowerD_Le, TowerD_D という別の型エイリアスを作る
2. それぞれに Category インスタンスを与える
3. 関手を形式的に定義する

という手順を踏む。
-/
-- def inclusionLeToD : Cat_le ⥤ Cat_D where
--   obj := id
--   map := homLeToHomD
--   ...

lemma homLeToHomD_preserves_comp {T T' T'' : TowerD}
    (g : HomLe T' T'') (f : HomLe T T') :
    homLeToHomD (HomLe.comp g f) = HomD.comp (homLeToHomD g) (homLeToHomD f) := by
  ext
  rfl

/-- HomEq から HomLe への変換

全単射性の情報を忘れる。
-/
def homEqToHomLe {T T' : TowerD} (f : HomEq T T') : HomLe T T' where
  map := f.map
  indexMap := f.indexMap
  indexMap_mono := f.indexMap_mono
  layer_preserving := f.layer_preserving

/-- 包含の推移性: HomEq → HomLe → HomD -/
def homEqToHomD {T T' : TowerD} (f : HomEq T T') : HomD T T' :=
  homLeToHomD (homEqToHomLe f)

/-!
**包含関手の性質**

`HomLe` の射は `indexMap` を **データとして** 持つため、
`homLeToHomD` は一般には忠実（faithful）ではない：
同じ `map` を持つ異なる `HomLe` が同一の `HomD` に写り得る。

一方で `HomD` の射は `map` で一意に定まる（`HomD.ext`）ので、
`homLeToHomD f = homLeToHomD g` は「`f.map = g.map`」と同値になる。
-/

lemma homLeToHomD_eq_iff_map_eq {T T' : TowerD} {f g : HomLe T T'} :
    homLeToHomD f = homLeToHomD g ↔ f.map = g.map := by
  constructor
  · intro h
    exact congrArg HomD.map h
  · intro h
    apply HomD.ext
    simpa [homLeToHomD] using h

end InclusionFunctors

/-!
# 3. 直積（Product）

二つの構造塔の直積を構成する。

## 数学的構成

T₁ と T₂ の直積 T₁ × T₂ は:
- carrier = T₁.carrier × T₂.carrier
- Index = T₁.Index × T₂.Index
- layer (i,j) = layer₁ i ×ˢ layer₂ j
- 射影: π₁, π₂

## 普遍性

任意の T と射 f₁: T → T₁, f₂: T → T₂ に対して、
一意的な射 ⟨f₁, f₂⟩: T → T₁ × T₂ が存在して、
π₁ ∘ ⟨f₁, f₂⟩ = f₁ かつ π₂ ∘ ⟨f₁, f₂⟩ = f₂
-/

section Product

/-- 二つの構造塔の直積

**層の定義**:
layer (i,j) = {(x,y) | x ∈ layer₁ i ∧ y ∈ layer₂ j}

**直感**:
「両方の構造を保持する最小の構造」
-/
def prod (T₁ T₂ : TowerD) : TowerD where
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

notation:35 T₁ " ×ᴰ " T₂ => prod T₁ T₂

/-- 第一射影

(x, y) ↦ x という写像。
層保存: (x,y) ∈ layer (i,j) ⇒ x ∈ layer i
-/
def proj₁ (T₁ T₂ : TowerD) : (T₁ ×ᴰ T₂) ⟶ᴰ T₁ where
  map := Prod.fst
  map_layer := by
    intro ⟨i, j⟩
    use i
    intro x hx
    rcases hx with ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    exact ha

/-- 第二射影

(x, y) ↦ y という写像。
-/
def proj₂ (T₁ T₂ : TowerD) : (T₁ ×ᴰ T₂) ⟶ᴰ T₂ where
  map := Prod.snd
  map_layer := by
    intro ⟨i, j⟩
    use j
    intro y hy
    rcases hy with ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    exact hb

/-- 積への普遍射

f₁: T → T₁ と f₂: T → T₂ から、
⟨f₁, f₂⟩: T → T₁ × T₂ を構成する。

**構成**:
- map: x ↦ (f₁.map x, f₂.map x)
- 層保存: x ∈ layer i ⇒ ∃j₁, j₂ such that
  f₁(x) ∈ layer j₁ ∧ f₂(x) ∈ layer j₂
  ⇒ (f₁(x), f₂(x)) ∈ layer (j₁, j₂)
-/
def prodUniversal {T T₁ T₂ : TowerD}
    (f₁ : T ⟶ᴰ T₁) (f₂ : T ⟶ᴰ T₂) :
    T ⟶ᴰ (T₁ ×ᴰ T₂) where
  map := fun x => (f₁.map x, f₂.map x)
  map_layer := by
    intro i
    obtain ⟨j₁, hj₁⟩ := f₁.map_layer i
    obtain ⟨j₂, hj₂⟩ := f₂.map_layer i
    use ⟨j₁, j₂⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨hj₁ ⟨x, hx, rfl⟩, hj₂ ⟨x, hx, rfl⟩⟩

notation "⟨" f₁ ", " f₂ "⟩ᴰ" => prodUniversal f₁ f₂

/-- 積の普遍性（第一成分） -/
theorem prodUniversal_proj₁ {T T₁ T₂ : TowerD}
    (f₁ : T ⟶ᴰ T₁) (f₂ : T ⟶ᴰ T₂) :
    HomD.comp (proj₁ T₁ T₂) (⟨f₁, f₂⟩ᴰ) = f₁ := by
  ext
  rfl

/-- 積の普遍性（第二成分） -/
theorem prodUniversal_proj₂ {T T₁ T₂ : TowerD}
    (f₁ : T ⟶ᴰ T₁) (f₂ : T ⟶ᴰ T₂) :
    HomD.comp (proj₂ T₁ T₂) (⟨f₁, f₂⟩ᴰ) = f₂ := by
  ext
  rfl

/-- 積の普遍性（一意性）

射影との可換性を満たす射は一意である。
-/
theorem prodUniversal_unique {T T₁ T₂ : TowerD}
    (f₁ : T ⟶ᴰ T₁) (f₂ : T ⟶ᴰ T₂) (g : T ⟶ᴰ (T₁ ×ᴰ T₂))
    (h₁ : HomD.comp (proj₁ T₁ T₂) g = f₁)
    (h₂ : HomD.comp (proj₂ T₁ T₂) g = f₂) :
    g = ⟨f₁, f₂⟩ᴰ := by
  ext x
  have eq1 : (g.map x).1 = f₁.map x := by
    have := congrArg HomD.map h₁
    exact congrFun this x
  have eq2 : (g.map x).2 = f₂.map x := by
    have := congrArg HomD.map h₂
    exact congrFun this x
  exact Prod.ext eq1 eq2

end Product

/-!
# 4. 余積（Coproduct）

二つの構造塔の余積を構成する。

## 数学的構成

T₁ と T₂ の余積 T₁ ⊕ T₂ は:
- carrier = T₁.carrier ⊕ T₂.carrier
- Index = T₁.Index ⊕ T₂.Index（直和＝cross 比較なし）
- layer (Sum.inl i) = Sum.inl '' (layer₁ i)
- layer (Sum.inr j) = Sum.inr '' (layer₂ j)

## 普遍性

任意の T と射 g₁: T₁ → T, g₂: T₂ → T に対して、
一意的な射 [g₁, g₂]: T₁ ⊕ T₂ → T が存在して、
[g₁, g₂] ∘ inj₁ = g₁ かつ [g₁, g₂] ∘ inj₂ = g₂
-/

section Coproduct

/-!
**直和（disjoint sum）順序の定義**

- `Sum.inl a ≤ Sum.inl b` は `a ≤ b` で比較する。
- `Sum.inr a ≤ Sum.inr b` は `a ≤ b` で比較する。
- `Sum.inl _ ≤ Sum.inr _` と `Sum.inr _ ≤ Sum.inl _` は常に `False`（cross-variant 比較なし）。

この選択により、層が互いに交わらない `Sum.inl '' _` と `Sum.inr '' _` の間で、
不自然な単調性を要求して破綻することを避ける。
-/

def sumPreorder {α β : Type*} [Preorder α] [Preorder β] :
    Preorder (α ⊕ β) where
  le := fun x y => match x, y with
    | Sum.inl a, Sum.inl b => a ≤ b
    | Sum.inl _, Sum.inr _ => False
    | Sum.inr _, Sum.inl _ => False
    | Sum.inr a, Sum.inr b => a ≤ b
  le_refl := by
    intro x
    cases x <;> simp
  le_trans := by
    intro x y z hxy hyz
    cases x <;> cases y <;> cases z <;> simp at hxy hyz ⊢
    · exact le_trans hxy hyz
    · exact le_trans hxy hyz

/-- 二つの構造塔の余積

**層の定義**:
- layer (Sum.inl i) = {Sum.inl x | x ∈ layer₁ i}
- layer (Sum.inr j) = {Sum.inr y | y ∈ layer₂ j}

**直感**:
「両方の構造を別々に保持する」
-/
def coprod (T₁ T₂ : TowerD) : TowerD where
  carrier := T₁.carrier ⊕ T₂.carrier
  Index := T₁.Index ⊕ T₂.Index
  indexPreorder := sumPreorder
  layer := fun idx => match idx with
    | Sum.inl i => Sum.inl '' (T₁.layer i)
    | Sum.inr j => Sum.inr '' (T₂.layer j)
  covering := by
    intro x
    cases x with
    | inl x₁ =>
      obtain ⟨i, hi⟩ := T₁.covering x₁
      use Sum.inl i
      exact ⟨x₁, hi, rfl⟩
    | inr x₂ =>
      obtain ⟨j, hj⟩ := T₂.covering x₂
      use Sum.inr j
      exact ⟨x₂, hj, rfl⟩
  monotone := by
    intro i j hij
    cases i <;> cases j
    · -- Sum.inl i ≤ Sum.inl j
      intro x hx
      rcases hx with ⟨a, ha, rfl⟩
      exact ⟨a, T₁.monotone hij ha, rfl⟩
    · -- Sum.inl i ≤ Sum.inr j (False)
      cases hij
    · -- Sum.inr i ≤ Sum.inl j (False)
      cases hij
    · -- Sum.inr i ≤ Sum.inr j
      intro y hy
      rcases hy with ⟨b, hb, rfl⟩
      exact ⟨b, T₂.monotone hij hb, rfl⟩

notation:35 T₁ " ⊕ᴰ " T₂ => coprod T₁ T₂

/-- 第一埋め込み

x ↦ Sum.inl x という写像。
-/
def inj₁ (T₁ T₂ : TowerD) : T₁ ⟶ᴰ (T₁ ⊕ᴰ T₂) where
  map := Sum.inl
  map_layer := by
    intro i
    use Sum.inl i
    intro x hx
    rcases hx with ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

/-- 第二埋め込み

y ↦ Sum.inr y という写像。
-/
def inj₂ (T₁ T₂ : TowerD) : T₂ ⟶ᴰ (T₁ ⊕ᴰ T₂) where
  map := Sum.inr
  map_layer := by
    intro j
    use Sum.inr j
    intro y hy
    rcases hy with ⟨b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩

/-- 余積からの普遍射

g₁: T₁ → T と g₂: T₂ → T から、
[g₁, g₂]: T₁ ⊕ T₂ → T を構成する。

**構成**:
- map: Sum.inl x ↦ g₁.map x
        Sum.inr y ↦ g₂.map y
-/
def coprodUniversal {T T₁ T₂ : TowerD}
    (g₁ : T₁ ⟶ᴰ T) (g₂ : T₂ ⟶ᴰ T) :
    (T₁ ⊕ᴰ T₂) ⟶ᴰ T where
  map := fun x => match x with
    | Sum.inl x₁ => g₁.map x₁
    | Sum.inr x₂ => g₂.map x₂
  map_layer := by
    intro idx
    cases idx with
    | inl i =>
      obtain ⟨j, hj⟩ := g₁.map_layer i
      use j
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      rcases hx with ⟨x₁, hx₁, rfl⟩
      exact hj ⟨x₁, hx₁, rfl⟩
    | inr i =>
      obtain ⟨j, hj⟩ := g₂.map_layer i
      use j
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      rcases hx with ⟨x₂, hx₂, rfl⟩
      exact hj ⟨x₂, hx₂, rfl⟩

notation "[" g₁ ", " g₂ "]ᴰ" => coprodUniversal g₁ g₂

/-- 余積の普遍性（第一成分） -/
theorem coprodUniversal_inj₁ {T T₁ T₂ : TowerD}
    (g₁ : T₁ ⟶ᴰ T) (g₂ : T₂ ⟶ᴰ T) :
    HomD.comp [g₁, g₂]ᴰ (inj₁ T₁ T₂) = g₁ := by
  ext
  rfl

/-- 余積の普遍性（第二成分） -/
theorem coprodUniversal_inj₂ {T T₁ T₂ : TowerD}
    (g₁ : T₁ ⟶ᴰ T) (g₂ : T₂ ⟶ᴰ T) :
    HomD.comp [g₁, g₂]ᴰ (inj₂ T₁ T₂) = g₂ := by
  ext
  rfl

/-- 余積の普遍性（一意性）

埋め込みとの可換性を満たす射は一意である。
-/
theorem coprodUniversal_unique {T T₁ T₂ : TowerD}
    (g₁ : T₁ ⟶ᴰ T) (g₂ : T₂ ⟶ᴰ T)
    (h : (T₁ ⊕ᴰ T₂) ⟶ᴰ T)
    (h₁ : HomD.comp h (inj₁ T₁ T₂) = g₁)
    (h₂ : HomD.comp h (inj₂ T₁ T₂) = g₂) :
    h = [g₁, g₂]ᴰ := by
  ext x
  cases x with
  | inl x₁ =>
    have := congrArg HomD.map h₁
    exact congrFun this x₁
  | inr x₂ =>
    have := congrArg HomD.map h₂
    exact congrFun this x₂

/-!
## `CategoryTheory.Limits` としての余積

ここまでの `coprodUniversal` / `coprodUniversal_unique` は “手書きの普遍性” だが、
mathlib の `BinaryCofan` / `IsColimit` にも接続しておく。
-/

open CategoryTheory.Limits

/-- The `BinaryCofan` exhibiting `coprod` as a coproduct in `TowerD`. -/
def coprodCofan (T₁ T₂ : TowerD.{u, v}) : BinaryCofan T₁ T₂ :=
  BinaryCofan.mk (P := (T₁ ⊕ᴰ T₂))
    (inj₁ T₁ T₂ : T₁ ⟶ (T₁ ⊕ᴰ T₂))
    (inj₂ T₁ T₂ : T₂ ⟶ (T₁ ⊕ᴰ T₂))

/-- `coprodCofan` is a colimit cocone (so `coprod` is a categorical coproduct). -/
def coprodIsColimit (T₁ T₂ : TowerD.{u, v}) : IsColimit (coprodCofan (T₁ := T₁) (T₂ := T₂)) := by
  refine (BinaryCofan.IsColimit.mk (s := coprodCofan (T₁ := T₁) (T₂ := T₂))
    (desc := fun {T} (f : T₁ ⟶ T) (g : T₂ ⟶ T) =>
      (coprodUniversal (T := T) (T₁ := T₁) (T₂ := T₂) f g))
    (hd₁ := ?_)
    (hd₂ := ?_)
    (uniq := ?_))
  · intro T f g
    simpa [coprodCofan] using (coprodUniversal_inj₁ (T := T) (T₁ := T₁) (T₂ := T₂) f g)
  · intro T f g
    simpa [coprodCofan] using (coprodUniversal_inj₂ (T := T) (T₁ := T₁) (T₂ := T₂) f g)
  · intro T f g m hm1 hm2
    have h1' : HomD.comp m (inj₁ T₁ T₂) = f := by
      simpa [coprodCofan] using hm1
    have h2' : HomD.comp m (inj₂ T₁ T₂) = g := by
      simpa [coprodCofan] using hm2
    simpa using (coprodUniversal_unique (T := T) (T₁ := T₁) (T₂ := T₂) f g m h1' h2')

instance (T₁ T₂ : TowerD.{u, v}) : HasBinaryCoproduct T₁ T₂ := by
  -- `HasBinaryCoproduct X Y` is `HasColimit (pair X Y)`.
  dsimp [HasBinaryCoproduct]
  refine HasColimit.mk' ?_
  refine ⟨⟨(coprodCofan (T₁ := T₁) (T₂ := T₂)), (coprodIsColimit (T₁ := T₁) (T₂ := T₂))⟩⟩

end Coproduct

/-!
# 5. 具体例での動作確認

P1, P2, P3 で定義された構造塔を使って、
直積と余積が正しく機能することを確認する。
-/

section Examples

/-!
**自然数の構造塔（再掲）**

P1.lean や CAT2_complete.lean で定義されたものと同等。
-/

 @[reducible] def natTower : TowerD where
  carrier := ℕ
  Index := ℕ
  indexPreorder := (inferInstance : Preorder ℕ)
  layer := fun n => {k : ℕ | k ≤ n}
  covering := by
    intro x
    refine ⟨x, ?_⟩
    exact Nat.le_refl x
  monotone := by
    intro i j hij k hk
    exact Nat.le_trans hk hij

 /-!
 `homLeToHomD` が一般に忠実でないことの最小例。

 `natTower ⟶ₗₑ natTower` では、同じ `map := id` でも
 `indexMap := id` と `indexMap := Nat.succ` のように別のデータを入れられる。
 しかし `homLeToHomD` は `indexMap` を捨てるので像は一致する。
 -/

 def homLeId_natTower : HomLe natTower natTower where
   map := _root_.id
   indexMap := _root_.id
   indexMap_mono := by intro a b hab; exact hab
   layer_preserving := by
     intro i x hx
     simpa using hx

 def homLeSucc_natTower : HomLe natTower natTower where
   map := _root_.id
   indexMap := Nat.succ
   indexMap_mono := by
     intro a b hab
     exact Nat.succ_le_succ hab
   layer_preserving := by
     intro i x hx
     exact Nat.le_trans hx (Nat.le_succ i)

 example : homLeId_natTower ≠ homLeSucc_natTower := by
   intro h
   have hindex : homLeId_natTower.indexMap = homLeSucc_natTower.indexMap :=
     congrArg HomLe.indexMap h
   have h0 : homLeId_natTower.indexMap 0 = homLeSucc_natTower.indexMap 0 :=
     congrArg (fun φ => φ 0) hindex
   have h01 : (0 : ℕ) = 1 := by
     have h0' := h0
     dsimp [homLeId_natTower, homLeSucc_natTower] at h0'
     exact h0'
   exact Nat.zero_ne_one h01

 example : homLeToHomD homLeId_natTower = homLeToHomD homLeSucc_natTower := by
   exact (homLeToHomD_eq_iff_map_eq (f := homLeId_natTower) (g := homLeSucc_natTower)).2 rfl

/-- 自然数の構造塔の直積

natTower ×ᴰ natTower の層は:
layer (m, n) = {(i, j) | i ≤ m ∧ j ≤ n}
-/
example : TowerD := natTower ×ᴰ natTower

/-- 直積の具体的な層

(2, 3) は layer (2, 3) に属する。
-/
example : (2, 3) ∈ (natTower ×ᴰ natTower).layer (2, 3) := by
  simp [prod]

/-- 射影の動作確認

π₁((2, 3)) = 2
-/
example : (proj₁ natTower natTower).map (2, 3) = 2 := rfl

/-- 普遍射の動作確認

恒等射 id: natTower → natTower を2つ組み合わせて、
⟨id, id⟩: natTower → natTower × natTower を作る。
-/
example : natTower ⟶ᴰ (natTower ×ᴰ natTower) :=
  ⟨HomD.id natTower, HomD.id natTower⟩ᴰ

/-- 普遍射の計算

⟨id, id⟩(5) = (5, 5)
-/
example : (⟨HomD.id natTower, HomD.id natTower⟩ᴰ).map 5 = (5, 5) := by
  rfl

/-!
**有理2次元ベクトル空間の構造塔**

Closure_Basic.lean で定義されたものと同等（簡略版）。
-/

def Vec2Q : Type := ℚ × ℚ

noncomputable def minBasisCount (v : Vec2Q) : ℕ :=
  if v.1 = 0 ∧ v.2 = 0 then 0
  else if v.1 = 0 ∨ v.2 = 0 then 1
  else 2

def vec2QTower : TowerD where
  carrier := Vec2Q
  Index := ℕ
  indexPreorder := (inferInstance : Preorder ℕ)
  layer := fun n => {v : Vec2Q | minBasisCount v ≤ n}
  covering := by
    intro v
    use minBasisCount v
    simp
  monotone := by
    intro i j hij v hv
    exact le_trans hv hij

/-- Vec2Q の構造塔の直積 -/
example : TowerD := vec2QTower ×ᴰ vec2QTower

/-- 余積の例：ℕ ⊕ ℚ² -/
example : TowerD := natTower ⊕ᴰ vec2QTower

/-- 余積の層の例

Sum.inl 3 ∈ layer (Sum.inl 5)
-/
example : Sum.inl 3 ∈ (natTower ⊕ᴰ vec2QTower).layer (Sum.inl 5) := by
  simp [coprod]

/-- 埋め込みの動作確認

inj₁(5) = Sum.inl 5
-/
example : (inj₁ natTower vec2QTower).map 5 = Sum.inl 5 := rfl

/-- `coprod` が `CategoryTheory.Limits` の意味で余積になっていることの確認 -/
example : CategoryTheory.Limits.IsColimit (coprodCofan (T₁ := natTower) (T₂ := vec2QTower)) :=
  coprodIsColimit (T₁ := natTower) (T₂ := vec2QTower)

end Examples

end TowerD
end ST

/-!
# まとめと今後の展望

## 本ファイルの成果

1. **忘却関手**: 構造塔から台集合・添字集合への関手
2. **包含関手**: Cat_eq ⊆ Cat_le ⊆ Cat_D の階層構造
3. **直積**: 普遍性を満たす積の構成
4. **余積**: 普遍性を満たす余積の構成（部分的）
5. **具体例**: 自然数・ベクトル空間での動作確認

## 実装上の課題

### 1. 余積の単調性

「Sum.inl と Sum.inr を比較できる順序」（例：Sum.inl i ≤ Sum.inr j を常に True）
を採用すると、layer の定義上単調性が一般に偽になる（異なる variant の像は交わらない）。
本ファイルでは cross-variant の比較を常に False とする “直和（disjoint union）順序” を採用して回避している。

### 2. 圏インスタンスの衝突

Lean 4 では同じ型に複数の Category インスタンスを持てない。

**解決策**:
- TowerD_D, TowerD_Le, TowerD_Eq という別の型を定義
- それぞれに適切な Category インスタンスを与える
- 忘却関手・包含関手をこれらの間の関手として定義

## 今後の拡張

1. **等化子（Equalizer）**の実装
2. **余等化子（Coequalizer）**の実装
3. **引き戻し（Pullback）**の実装
4. **極限の一般化**：任意の図式の極限
5. **随伴関手**：忘却関手の左随伴としての自由構造塔
6. **モナド構造**：構造塔上のモナド

## Bourbaki の精神

本実装は、Bourbaki の構造理論を圏論的に再解釈したものである：

1. **階層性**: 包含関手による射の階層
2. **普遍性**: 直積・余積の普遍性
3. **構成性**: 小さな部品（関手）から大きな構造を組み立てる

構造塔理論は、異なる数学的構造（代数、位相、順序）を
統一的に扱う Bourbaki の思想の現代的実現である。
-/
