import Mathlib.Data.Set.Lattice
import Mathlib.Order.Hom.Basic

/-!
# 課題: 構造塔の圏論的視点 — 基礎編
# Task: Categorical Aspects of Structure Towers — Foundations

## メタデータ / Metadata
- **課題番号**: ST-CAT-001
- **難易度**: レベル1（基礎）
- **カテゴリ**: 圏論的視点 (Categorical Aspects)
- **推定所要時間**: 60–90 分
- **前提知識**:
  - 集合と写像の基本
  - 部分集合の包含関係
  - 圏の定義（対象・射・合成・恒等射）の直観的理解

## 導入 / Introduction

Bourbakiは数学的構造を「集合に定義された演算や関係の族」として捉えた。
構造塔（Structure Tower）は、添字づけられた集合の単調族という最小限の
データで「階層的構造」を表現する。

圏論的に見ると、構造塔を **対象** (object)、構造塔間の準同型を **射** (morphism)
として圏を構成できる。本課題では、この圏の最も基本的な構成要素——
**射の定義**、**恒等射**、**合成**、および **圏の公理**（結合律・単位律）
——をLean 4で形式化し、`sorry` を埋めることで証明する。

## 学習目標 / Learning Objectives

1. 構造塔の射（TowerHom）が何を保存すべきかを理解する
2. 恒等射と合成を構成的に定義できる
3. 圏の公理（結合律・単位律）を集合論的に証明できる
4. `funext` や `Set.Subset.trans` 等の基本タクティクに慣れる

---

## ヒント（必要に応じて参照）/ Hints

### ヒント1（大まかな証明戦略）
- 射の等価性は `funext` で関数の外延性に帰着させる
- 集合の等式は `Set.ext` で元ごとの同値に帰着させる
- 合成の結合律は関数合成の結合律そのもの

### ヒント2（具体的な補題）
- `Function.comp_id` : f ∘ id = f
- `Function.id_comp` : id ∘ f = f
- `Function.comp_assoc` : (f ∘ g) ∘ h = f ∘ (g ∘ h)
- `Set.image_subset` : f '' A ⊆ f '' B ← A ⊆ B （ただし今回は直接使わない）

### ヒント3（実装のポイント）
- `TowerHom.ext` を証明すると、以降の射の等式証明が楽になる
- 恒等射では `mapFun := id` とし、レベル保存は `Set.Subset.rfl` で示せる
- 合成のレベル保存は2つの包含関係の推移律
-/

open Set

namespace BourbakiLeanGuide

/-!
## 第0節: StructureTower の再掲
Section 0: StructureTower (reproduced from v0)
-/

/-- 構造塔: 前順序で添字づけられた集合の単調族
    Structure Tower: a monotone family of sets indexed by a preorder -/
structure StructureTower (ι α : Type*) [Preorder ι] : Type _ where
  level : ι → Set α
  monotone_level : ∀ ⦃i j⦄, i ≤ j → level i ⊆ level j

/-!
## 第1節: 構造塔の射（準同型）の定義
Section 1: Definition of Tower Morphisms (Homomorphisms)

構造塔の射とは、基礎集合間の写像であって、各レベルの構造を保存するものである。
Bourbaki的に言えば「構造と整合的な写像」(morphisme compatible avec la structure)。

集合論的定式化:
  T = (X, (Xᵢ)ᵢ∈I), T' = (Y, (Yᵢ)ᵢ∈I) が同じ添字集合 I の構造塔のとき、
  射 f : T → T' とは写像 f : X → Y であって、
  ∀ i ∈ I, f(Xᵢ) ⊆ Yᵢ （すなわち x ∈ Xᵢ ⇒ f(x) ∈ Yᵢ）を満たすもの。
-/

/-- 構造塔の射: 基礎集合間の写像で、各レベルを保存するもの
    A tower morphism: a map between base sets preserving each level -/
structure TowerHom {ι α β : Type*} [Preorder ι]
    (S : StructureTower ι α) (T : StructureTower ι β) where
  /-- 基礎集合間の写像 / The underlying map -/
  mapFun : α → β
  /-- レベル保存条件: 各添字 i について f(Sᵢ) ⊆ Tᵢ
      Level preservation: for each index i, f maps S.level i into T.level i -/
  level_preserving : ∀ (i : ι), ∀ x ∈ S.level i, mapFun x ∈ T.level i

namespace TowerHom

variable {ι α β γ : Type*} [Preorder ι]
variable {S : StructureTower ι α} {T : StructureTower ι β} {U : StructureTower ι γ}

/-!
### 課題 1.1: 射の外延性 (Extensionality)
Exercise 1.1: Extensionality of morphisms

二つの射が等しいことは、基礎写像が等しいことと同値である。
これは以降の証明の基盤となる重要な補題。

**方針**: `TowerHom` の構成子から、`mapFun` が等しければ全体が等しいことを導く。
-/

/-- 射の外延性: 基礎写像が等しければ射として等しい
    Extensionality: morphisms with equal underlying maps are equal -/
@[ext]
theorem ext (f g : TowerHom S T) (h : f.mapFun = g.mapFun) : f = g := by
  cases f
  cases g
  simp only [mk.injEq]
  exact h

/-!
### 課題 1.2: 恒等射 (Identity Morphism)
Exercise 1.2: Identity Morphism

任意の構造塔 T に対して恒等射 id_T : T → T を構成する。

集合論的定式化:
  id_T = (id_X, ∀ i, id_X(Xᵢ) ⊆ Xᵢ)
  id_X(x) = x なので id_X(Xᵢ) = Xᵢ ⊆ Xᵢ は自明。

**方針**: `mapFun := id` として、レベル保存は仮定そのものから従う。
-/

/-- 恒等射: 恒等写像は各レベルを保存する
    Identity morphism: the identity map preserves every level -/
def id (T : StructureTower ι α) : TowerHom T T where
  mapFun := _root_.id
  level_preserving := by
    intro i x hx
    simpa using hx

/-!
### 課題 1.3: 射の合成 (Composition)
Exercise 1.3: Composition of Morphisms

射 f : S → T と g : T → U の合成 g ∘ f : S → U を構成する。

集合論的定式化:
  f = (f₀, ∀ i, f₀(Sᵢ) ⊆ Tᵢ)
  g = (g₀, ∀ i, g₀(Tᵢ) ⊆ Uᵢ)
  g ∘ f = (g₀ ∘ f₀, ∀ i, (g₀ ∘ f₀)(Sᵢ) ⊆ Uᵢ)

  証明: x ∈ Sᵢ ⇒ f₀(x) ∈ Tᵢ ⇒ g₀(f₀(x)) ∈ Uᵢ

**方針**: f のレベル保存で中間結果を得て、g のレベル保存で結論を得る。
-/

/-- 射の合成: レベル保存条件は推移的に成立する
    Composition: level preservation composes transitively -/
def comp (g : TowerHom T U) (f : TowerHom S T) : TowerHom S U where
  mapFun := g.mapFun ∘ f.mapFun
  level_preserving := by
    intro i x hx
    exact g.level_preserving i (f.mapFun x) (f.level_preserving i x hx)

/-!
## 第2節: 圏の公理の検証
Section 2: Verifying the Category Axioms

圏 𝒞 は以下を満たす:
  (A1) 結合律: (h ∘ g) ∘ f = h ∘ (g ∘ f)
  (A2) 左単位律: id ∘ f = f
  (A3) 右単位律: f ∘ id = f

これらを StructureTower と TowerHom について検証する。
-/

/-!
### 課題 2.1: 合成の結合律 (Associativity)
Exercise 2.1: Associativity of Composition

射 f : R → S, g : S → T, h : T → U に対して
  (h ∘ g) ∘ f = h ∘ (g ∘ f)

**方針**: `TowerHom.ext` を使い、基礎写像のレベルで
`Function.comp_assoc` またはその定義展開で示す。
-/

variable {δ : Type*}
variable {R : StructureTower ι α} {S' : StructureTower ι β}
variable {T' : StructureTower ι γ} {U' : StructureTower ι δ}

theorem comp_assoc
    (f : TowerHom R S') (g : TowerHom S' T') (h : TowerHom T' U') :
    comp (comp h g) f = comp h (comp g f) := by
  apply TowerHom.ext
  rfl

/-!
### 課題 2.2: 左単位律 (Left Identity)
Exercise 2.2: Left Identity Law

任意の射 f : S → T に対して id_T ∘ f = f

**方針**: `ext` で基礎写像に帰着し、`Function.id_comp` を使う。
-/

theorem id_comp (f : TowerHom S T) :
    comp (TowerHom.id T) f = f := by
  apply TowerHom.ext
  rfl

/-!
### 課題 2.3: 右単位律 (Right Identity)
Exercise 2.3: Right Identity Law

任意の射 f : S → T に対して f ∘ id_S = f

**方針**: `ext` で基礎写像に帰着し、`Function.comp_id` を使う。
-/

theorem comp_id (f : TowerHom S T) :
    comp f (TowerHom.id S) = f := by
  apply TowerHom.ext
  rfl

end TowerHom

/-!
## 第3節: 具体例 — 自然数の構造塔間の射
Section 3: Concrete Example — A morphism between ℕ-towers

具体的な構造塔間の射を構成して、定義が正しく機能することを確認する。

考える構造塔:
- `natInitialSegments`: level n = {k | k ≤ n}
- `natDoubleSegments`: level n = {k | k ≤ 2 * n}

写像 f(k) = k は natInitialSegments から natDoubleSegments への射となる。
（∵ k ≤ n ⇒ k ≤ 2n）
-/

section ConcreteExample

/-- 自然数の初期区間による構造塔（再掲）-/
def natInitialSegments : StructureTower ℕ ℕ where
  level n := {k : ℕ | k ≤ n}
  monotone_level := by
    intro i j hij k hk
    exact Nat.le_trans hk hij

/-- 2倍の初期区間による構造塔 -/
def natDoubleSegments : StructureTower ℕ ℕ where
  level n := {k : ℕ | k ≤ 2 * n}
  monotone_level := by
    intro i j hij k hk
    calc k ≤ 2 * i := hk
    _ ≤ 2 * j := Nat.mul_le_mul_left 2 hij

/-!
### 課題 3.1: 具体的な射の構成
Exercise 3.1: Constructing a concrete morphism

恒等写像 id : ℕ → ℕ が natInitialSegments から natDoubleSegments への
射となることを示せ。

**方針**: k ≤ n ならば k ≤ 2 * n を示す。
-/

/-- 包含射: 初期区間は2倍区間に自然に埋め込まれる
    Inclusion morphism: initial segments embed into double segments -/
def inclusionHom : TowerHom natInitialSegments natDoubleSegments where
  mapFun := _root_.id
  level_preserving := by
    intro i x hx
    have hi : i ≤ 2 * i := by
      calc
        i = 1 * i := by simp
        _ ≤ 2 * i := Nat.mul_le_mul_right i (by decide : 1 ≤ 2)
    exact Nat.le_trans hx hi

/-!
### 課題 3.2: 恒等射との合成
Exercise 3.2: Composition with identity

`inclusionHom` に恒等射を合成しても変わらないことを確認する。
（第2節の一般的な定理の具体例としての検証）
-/

example : TowerHom.comp inclusionHom (TowerHom.id natInitialSegments)
    = inclusionHom := by
  simpa using TowerHom.comp_id (f := inclusionHom)

end ConcreteExample

/-!
## 発展課題（任意）/ Extensions (Optional)

以下は本課題の自然な拡張方向である。

### 拡張1: 忠実関手としての忘却
`TowerHom` から基礎写像を取り出す対応 U(f) = f.mapFun は、
構造塔の圏から Set（集合の圏）への忠実関手を定める。
これを Mathlib の `CategoryTheory.Functor` で形式化せよ。

### 拡張2: 同型射
射 f : S → T が同型 (isomorphism) であるための条件を定式化し、
逆射の存在と基礎写像の全単射性の関係を示せ。

### 拡張3: Mathlibとの接続
`Mathlib.Order.Category.Preord` や `Mathlib.CategoryTheory.ConcreteCategory`
を用いて、`StructureTower ι` を concrete category として登録せよ。

## 参考文献 / References

- Bourbaki, N. *Éléments de mathématique: Théorie des ensembles*, Ch. IV (Structures)
- Bourbaki, N. *Éléments de mathématique: Algèbre*, Ch. I §1 (Lois de composition)
- Mac Lane, S. *Categories for the Working Mathematician*, Ch. I (Categories, Functors, and Natural Transformations)
- Mathlib: `Mathlib.Order.Hom.Basic`, `Mathlib.CategoryTheory.Category.Basic`
- Lean 4 Documentation: https://lean-lang.org/lean4/doc/
-/

end BourbakiLeanGuide
