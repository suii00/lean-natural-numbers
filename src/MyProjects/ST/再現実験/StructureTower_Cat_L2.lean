import Mathlib.Data.Set.Lattice
import Mathlib.Order.Hom.Basic

/-!
# 課題: 構造塔の圏論的視点 — 中級編
# Task: Categorical Aspects of Structure Towers — Intermediate

## メタデータ / Metadata
- **課題番号**: ST-CAT-002
- **難易度**: レベル2（中級）
- **カテゴリ**: 圏論的視点 (Categorical Aspects)
- **推定所要時間**: 120–180 分
- **前提知識**:
  - ST-CAT-001（構造塔の射・圏の公理）の完了
  - 関手・自然変換の直観的理解
  - 積（直積）の普遍性の概念
  - Lean の `Subtype`, `Prod` の基本操作

## 導入 / Introduction

ST-CAT-001 では構造塔の圏 **TowerCat** の骨格——対象・射・合成・圏公理——
を構成した。本課題ではこの圏を3つの方向へ掘り下げる:

**A. 忘却関手と忠実性** (Forgetful Functor)
  構造塔から基礎集合への「構造を忘れる」対応が関手をなし、
  しかも射を区別する能力（忠実性）を持つことを示す。

**B. レベル制限と自然変換** (Level Restriction & Natural Transformations)
  各レベルへの制限写像が、添字間の包含と整合的（＝自然）であることを検証する。
  これは「局所的データが大域的に整合する」というBourbaki的主題の形式化である。

**C. 定値塔・引き戻し塔・積塔** (Constant, Pullback, Product Towers)
  圏論的構成——定値対象、引き戻し、積——を構造塔の文脈で実現し、
  それぞれの普遍性を証明する。これにより **TowerCat** が
  有限積を持つことが確認される。

## 学習目標 / Learning Objectives

1. 関手の公理（恒等射・合成の保存）を具体的に検証できる
2. Subtypeを用いたレベル制限写像を構成し、自然性を証明できる
3. 引き戻し塔 `f ⁻¹(Tᵢ)` の構成と、それが射を誘導することを示せる
4. 積塔の普遍性（射の存在と一意性）を完全に形式化できる

---

## ヒント総覧 / Hints Overview

### 全般
- `Subtype.ext` : Subtypeの等式は値の等式に帰着
- `Prod.ext` : ペアの等式は各成分の等式に帰着
- `Set.mem_preimage` : `x ∈ f ⁻¹' S ↔ f x ∈ S`
- `Set.preimage_mono` : `S ⊆ T → f ⁻¹' S ⊆ f ⁻¹' T`

### Part A
- 関手の公理は定義の展開で `rfl` になる場合が多い
- 忠実性は `TowerHom.ext` そのもの

### Part B
- `mapLevel` の定義ではSubtypeのパターンマッチ `⟨x, hx⟩` を使う
- 自然性は両辺を展開すると同じ値になることを `Subtype.ext` + `rfl` で示せる

### Part C
- `constTower` では `Set.mem_univ` が鍵
- `preimageTower` では `Set.preimage_mono` が単調性を与える
- 積塔のレベル保存は `And.intro` で2成分を同時に示す
- 普遍性の一意性は `TowerHom.ext` + `funext` + `Prod.ext`
-/

open Set

namespace BourbakiLeanGuide

/-!
## 第0節: ST-CAT-001 の結果（既証明）
Section 0: Results from ST-CAT-001 (proved)

以下は前回の課題で証明済みの定義と定理を再掲する。
-/

structure StructureTower (ι α : Type*) [Preorder ι] : Type _ where
  level : ι → Set α
  monotone_level : ∀ ⦃i j⦄, i ≤ j → level i ⊆ level j

structure TowerHom {ι α β : Type*} [Preorder ι]
    (S : StructureTower ι α) (T : StructureTower ι β) where
  mapFun : α → β
  level_preserving : ∀ (i : ι), ∀ x ∈ S.level i, mapFun x ∈ T.level i

namespace TowerHom

variable {ι α β γ δ : Type*} [Preorder ι]
variable {S : StructureTower ι α} {T : StructureTower ι β}
variable {U : StructureTower ι γ} {V : StructureTower ι δ}

@[ext]
theorem ext (f g : TowerHom S T) (h : f.mapFun = g.mapFun) : f = g := by
  cases f; cases g; simp only [mk.injEq]; exact h

def id (T : StructureTower ι α) : TowerHom T T where
  mapFun := _root_.id
  level_preserving := by intro i x hx; simpa using hx

def comp (g : TowerHom T U) (f : TowerHom S T) : TowerHom S U where
  mapFun := g.mapFun ∘ f.mapFun
  level_preserving := by
    intro i x hx
    exact g.level_preserving i (f.mapFun x) (f.level_preserving i x hx)

theorem comp_assoc (f : TowerHom S T) (g : TowerHom T U) (h : TowerHom U V) :
    comp (comp h g) f = comp h (comp g f) := by apply ext; rfl

theorem id_comp (f : TowerHom S T) : comp (TowerHom.id T) f = f := by
  apply ext; rfl

theorem comp_id (f : TowerHom S T) : comp f (TowerHom.id S) = f := by
  apply ext; rfl

end TowerHom

-- ═══════════════════════════════════════════════════════════════════
-- ██  Part A: 忘却関手と忠実性
-- ██  Forgetful Functor and Faithfulness
-- ═══════════════════════════════════════════════════════════════════

/-!
## 第1節: 忘却関手 (Forgetful Functor)

忘却関手 U : TowerCat → Type は次の対応である:
  - 対象: U(T) = α （構造塔 T : StructureTower ι α の基礎型）
  - 射:   U(f) = f.mapFun （射 f の基礎写像）

Lean では Type を値域とする関手を直接定義するのは型宇宙の問題があるため、
関手の **公理**（恒等射の保存・合成の保存）を個別の定理として検証する。
さらに、この関手が **忠実** (faithful) であることを示す。

集合論的定式化:
  忠実性: U(f) = U(g) ⇒ f = g
  すなわち、基礎写像が等しい射は射として等しい。
-/

section ForgetfulFunctor

variable {ι α β γ : Type*} [Preorder ι]
variable {S : StructureTower ι α} {T : StructureTower ι β} {U : StructureTower ι γ}

/-!
### 課題 A.1: 恒等射の保存 (Preservation of Identity)

U(id_T) = id_{U(T)} すなわち (TowerHom.id T).mapFun = id

**方針**: `TowerHom.id` の定義を展開するだけ。
-/

/-- 忘却関手は恒等射を保存する / The forgetful functor preserves identity -/
theorem forgetful_map_id (T : StructureTower ι α) :
    (TowerHom.id T).mapFun = _root_.id := by
  rfl

/-!
### 課題 A.2: 合成の保存 (Preservation of Composition)

U(g ∘ f) = U(g) ∘ U(f) すなわち (comp g f).mapFun = g.mapFun ∘ f.mapFun

**方針**: `TowerHom.comp` の定義を展開するだけ。
-/

/-- 忘却関手は合成を保存する / The forgetful functor preserves composition -/
theorem forgetful_map_comp (f : TowerHom S T) (g : TowerHom T U) :
    (TowerHom.comp g f).mapFun = g.mapFun ∘ f.mapFun := by
  rfl

/-!
### 課題 A.3: 忠実性 (Faithfulness)

忘却関手 U は **忠実** (faithful) である:
  U(f) = U(g) ⇒ f = g

これは射の外延性 `TowerHom.ext` の直接的な帰結であるが、
圏論的には「構造塔の射は基礎写像によって完全に決定される」
という重要な性質を表す。

**方針**: `TowerHom.ext` を適用する。
-/

/-- 忘却関手は忠実: 基礎写像が等しければ射として等しい
    The forgetful functor is faithful -/
theorem forgetful_faithful (f g : TowerHom S T)
    (h : f.mapFun = g.mapFun) : f = g := by
  exact TowerHom.ext f g h

end ForgetfulFunctor

-- ═══════════════════════════════════════════════════════════════════
-- ██  Part B: レベル制限と自然変換
-- ██  Level Restriction and Natural Transformations
-- ═══════════════════════════════════════════════════════════════════

/-!
## 第2節: レベル制限写像と自然変換

構造塔 T の各レベル T.level i は集合 α の部分集合である。
これを Lean の部分型 (Subtype) として扱うと:

  ↥(T.level i) = { x : α // x ∈ T.level i }

射 f : S → T は各レベルに **制限** (restriction) を誘導する:
  f|ᵢ : ↥(S.level i) → ↥(T.level i)
  f|ᵢ(⟨x, hx⟩) = ⟨f.mapFun x, f.level_preserving i x hx⟩

一方、添字 i ≤ j に対するレベル間の **包含写像** (inclusion) がある:
  ιᵢⱼ : ↥(T.level i) → ↥(T.level j)
  ιᵢⱼ(⟨x, hx⟩) = ⟨x, T.monotone_level hij hx⟩

**自然性** (naturality) とは、以下の図式が可換であること:

          f|ᵢ
  S.level i ────→ T.level i
      │                │
  ιᵢⱼˢ              ιᵢⱼᵀ
      │                │
      ▼                ▼
  S.level j ────→ T.level j
          f|ⱼ

すなわち: ιᵢⱼᵀ ∘ f|ᵢ = f|ⱼ ∘ ιᵢⱼˢ
-/

section NaturalTransformation

variable {ι α β γ : Type*} [Preorder ι]
variable {S : StructureTower ι α} {T : StructureTower ι β} {U : StructureTower ι γ}

/-!
### 課題 B.1: レベル間の包含写像 (Level Inclusion)

添字の順序 i ≤ j から、レベル間の包含写像を構成する。

**方針**: Subtypeのパターンマッチで元を取り出し、
`monotone_level` で上位レベルへの所属を示す。
-/

/-- レベル包含写像: i ≤ j のとき T.level i ↪ T.level j
    Level inclusion: the monotone embedding between levels -/
def StructureTower.levelInclusion (T : StructureTower ι α) {i j : ι}
    (hij : i ≤ j) : ↥(T.level i) → ↥(T.level j) :=
  fun ⟨x, hx⟩ => ⟨x, T.monotone_level hij hx⟩

/-!
### 課題 B.2: 射のレベル制限 (Level Restriction of a Morphism)

射 f : S → T を各レベルに制限した写像を構成する。

**方針**: Subtypeのパターンマッチで元 ⟨x, hx⟩ を取り出し、
`level_preserving` で像がターゲットレベルに属することを示す。
-/

/-- レベル制限: 射 f を添字 i のレベルに制限した写像
    Level restriction: the map induced by f on the i-th level -/
def TowerHom.mapLevel (f : TowerHom S T) (i : ι) :
    ↥(S.level i) → ↥(T.level i) :=
  fun ⟨x, hx⟩ => ⟨f.mapFun x, f.level_preserving i x hx⟩

/-!
### 課題 B.3: 自然性 (Naturality)

レベル包含とレベル制限が可換であることを示す。
これは圏論の言葉では「包含の族 (ι_ij) がレベル関手間の自然変換をなす」
ことの表明である。

集合論的に展開すると:
  左辺: ιᵢⱼᵀ(f|ᵢ(⟨x, hx⟩)) = ιᵢⱼᵀ(⟨f x, _⟩) = ⟨f x, _⟩
  右辺: f|ⱼ(ιᵢⱼˢ(⟨x, hx⟩)) = f|ⱼ(⟨x, _⟩)     = ⟨f x, _⟩
  両辺の値部分が一致する。

**方針**: `Subtype.ext` で値の等式に帰着し、`rfl` で閉じる。
ただし B.1, B.2 が `sorry` のままだと適用できないので、先にそちらを解くこと。
-/

/-- 自然性: レベル包含はレベル制限と可換
    Naturality: level inclusions commute with level restrictions -/
theorem mapLevel_natural (f : TowerHom S T) {i j : ι} (hij : i ≤ j)
    (x : ↥(S.level i)) :
    T.levelInclusion hij (f.mapLevel i x) =
    f.mapLevel j (S.levelInclusion hij x) := by
  apply Subtype.ext
  rfl

/-!
### 課題 B.4: 合成との整合性 (Compatibility with Composition)

射の合成のレベル制限は、レベル制限の合成に等しい:
  (g ∘ f)|ᵢ = g|ᵢ ∘ f|ᵢ

**方針**: 関数の外延性 (`funext`) + Subtype の外延性で示す。
-/

/-- レベル制限は合成と整合する: (g ∘ f)|ᵢ = g|ᵢ ∘ f|ᵢ
    Level restriction is compatible with composition -/
theorem mapLevel_comp (f : TowerHom S T) (g : TowerHom T U) (i : ι)
    (x : ↥(S.level i)) :
    (TowerHom.comp g f).mapLevel i x =
    g.mapLevel i (f.mapLevel i x) := by
  apply Subtype.ext
  rfl

end NaturalTransformation

-- ═══════════════════════════════════════════════════════════════════
-- ██  Part C: 定値塔と引き戻し塔
-- ██  Constant Tower and Pullback Tower
-- ═══════════════════════════════════════════════════════════════════

/-!
## 第3節: 標準的な塔の構成

圏論的構成の出発点として、2つの基本的な塔を導入する:

### 定値塔 (Constant Tower / Indiscrete Tower)
  constTower ι α : StructureTower ι α
  level i = Set.univ （すべてのレベルが全体集合）

これは「構造を一切区別しない」最も粗い塔であり、
任意の塔 T からの射 T → constTower が一意に存在する（終対象的性質）。

### 引き戻し塔 (Pullback / Preimage Tower)
  写像 f : α → β と塔 T : StructureTower ι β に対して
  preimageTower f T : StructureTower ι α
  level i = f ⁻¹'(T.level i) = {x : α | f(x) ∈ T.level i}

これは位相幾何学における逆像位相、代数における引き戻し構造の
構造塔版であり、Bourbaki的「構造の輸送」(transport de structure) に対応する。
-/

section Constructions

variable {ι α β γ : Type*} [Preorder ι]

/-!
### 課題 C.1: 定値塔の構成 (Constant Tower)

すべてのレベルが Set.univ である塔を構成する。
単調性は自明（univ ⊆ univ）。

**方針**: `level := fun _ => Set.univ`, 単調性は `Set.subset_univ` などで示す。
-/

/-- 定値塔: すべてのレベルが全体集合
    Constant tower: every level is the entire universe -/
def constTower (ι α : Type*) [Preorder ι] : StructureTower ι α where
  level := fun _ => Set.univ
  monotone_level := by
    intro i j hij
    exact Set.subset_univ _

/-!
### 課題 C.2: 定値塔の終対象的性質 (Terminal Property)

任意の塔 T : StructureTower ι α に対して、
恒等写像を基礎写像とする射 T → constTower ι α が存在する。

**方針**: mapFun := id, レベル保存は「任意の元は univ に属する」ことから従う。
-/

/-- 任意の塔から定値塔への標準射（終対象への射）
    The canonical morphism from any tower to the constant tower -/
def toConstTower (T : StructureTower ι α) :
    TowerHom T (constTower ι α) where
  mapFun := _root_.id
  level_preserving := by
    intro i x hx
    exact Set.mem_univ x

/-!
### 課題 C.3: 終対象的性質の一意性 (Uniqueness)

T から constTower ι α への射で mapFun = id であるものは一意である。

より正確には: 任意の射 f : T → constTower ι α で f.mapFun = id を
満たすものは `toConstTower T` に等しい。

**方針**: `TowerHom.ext` と仮定 `h` を使う。
-/

/-- 定値塔への id-射は一意 / The id-based morphism to constTower is unique -/
theorem toConstTower_unique (T : StructureTower ι α)
    (f : TowerHom T (constTower ι α)) (h : f.mapFun = _root_.id) :
    f = toConstTower T := by
  apply TowerHom.ext
  simpa [toConstTower] using h

/-!
### 課題 C.4: 引き戻し塔の構成 (Preimage Tower)

写像 f : α → β と塔 T : StructureTower ι β から、
α 上の塔 f*(T) を逆像によって構成する:
  f*(T).level i = f ⁻¹'(T.level i) = {x : α | f(x) ∈ T.level i}

単調性: i ≤ j ⇒ T.level i ⊆ T.level j ⇒ f⁻¹(T.level i) ⊆ f⁻¹(T.level j)

**方針**: `Set.preimage_mono` を使うか、直接元を追って示す。
-/

/-- 引き戻し塔: 写像の逆像でレベルを定義
    Preimage tower: levels defined by preimage under a map -/
def preimageTower (f : α → β) (T : StructureTower ι β) :
    StructureTower ι α where
  level i := f ⁻¹' (T.level i)
  monotone_level := by
    intro i j hij
    exact Set.preimage_mono (T.monotone_level hij)

/-!
### 課題 C.5: 引き戻し塔からの標準射 (Canonical Morphism from Pullback)

引き戻し塔 f*(T) から T への標準射が f 自身によって与えられる:
  f : preimageTower f T → T

これはまさに「逆像で定義したので、元の写像がレベルを保存する」という
トートロジカルだが重要な事実の形式化である。

**方針**: mapFun := f, レベル保存は逆像の定義そのもの。
-/

/-- 引き戻し塔から元の塔への標準射
    The canonical morphism from the preimage tower -/
def preimageTower.map (f : α → β) (T : StructureTower ι β) :
    TowerHom (preimageTower f T) T where
  mapFun := f
  level_preserving := by
    intro i x hx
    simpa using hx

end Constructions

-- ═══════════════════════════════════════════════════════════════════
-- ██  Part D: 積塔と圏論的極限
-- ██  Product Tower and Categorical Limits
-- ═══════════════════════════════════════════════════════════════════

/-!
## 第4節: 積塔 (Product Tower)

圏論における **積** (product) は普遍性によって特徴づけられる:

  塔 S : StructureTower ι α と T : StructureTower ι β の積とは、
  塔 S × T : StructureTower ι (α × β) であって、
  射影 π₁ : S × T → S, π₂ : S × T → T を持ち、
  以下の **普遍性** を満たすもの:

  任意の塔 R と射 f : R → S, g : R → T に対して、
  π₁ ∘ h = f かつ π₂ ∘ h = g を満たす射 h : R → S × T が
  **一意に** 存在する。

  ```
        f
    R ─────→ S
    │  ↗ π₁
    │h
    │  ↘ π₂
    ▼
   S×T ────→ T
        g
  ```

集合論的構成:
  (S × T).level i = {(a, b) : α × β | a ∈ S.level i ∧ b ∈ T.level i}
  π₁(a, b) = a,  π₂(a, b) = b
  h(x) = (f(x), g(x))
-/

section ProductTower

variable {ι α β γ : Type*} [Preorder ι]
variable (S : StructureTower ι α) (T : StructureTower ι β)

/-!
### 課題 D.1: 積塔の構成 (Product Tower Construction)

レベルを成分ごとの所属条件の連言 (∧) で定義する。
単調性は両成分の単調性から従う。

**方針**: `And.intro` で分解し、各成分に `S.monotone_level` / `T.monotone_level`
を適用する。
-/

/-- 積塔: レベルは成分ごとの条件の積
    Product tower: levels are componentwise -/
def prodTower : StructureTower ι (α × β) where
  level i := {p : α × β | p.1 ∈ S.level i ∧ p.2 ∈ T.level i}
  monotone_level := by
    intro i j hij p hp
    exact ⟨S.monotone_level hij hp.1, T.monotone_level hij hp.2⟩

/-!
### 課題 D.2: 第1射影 (First Projection)

π₁ : S × T → S を Prod.fst で定義する。
レベル保存: (a, b) ∈ (S × T).level i ⇒ a ∈ S.level i （連言の左成分）

**方針**: `hx.1` で連言の左側を取り出す。
-/

/-- 第1射影: 積塔から第1成分への射影
    First projection from the product tower -/
def prodTower.fst : TowerHom (prodTower S T) S where
  mapFun := Prod.fst
  level_preserving := by
    intro i x hx
    exact hx.1

/-!
### 課題 D.3: 第2射影 (Second Projection)

π₂ : S × T → T を Prod.snd で定義する。

**方針**: D.2 と対称的。`hx.2` で連言の右側を取り出す。
-/

/-- 第2射影: 積塔から第2成分への射影
    Second projection from the product tower -/
def prodTower.snd : TowerHom (prodTower S T) T where
  mapFun := Prod.snd
  level_preserving := by
    intro i x hx
    exact hx.2

/-!
### 課題 D.4: 普遍性 — 射の存在 (Universal Property: Existence)

任意の塔 R と射 f : R → S, g : R → T に対して、
h(x) = (f(x), g(x)) で定義される射 h : R → S × T を構成する。

レベル保存: x ∈ R.level i ⇒ f(x) ∈ S.level i ∧ g(x) ∈ T.level i

**方針**: `And.intro` で `f.level_preserving` と `g.level_preserving` を結合する。
-/

/-- 積への持ち上げ（普遍射）: 2つの射の対を積塔への射に持ち上げる
    Lift to product: the universal morphism into the product tower -/
def prodTower.lift {R : StructureTower ι γ}
    (f : TowerHom R S) (g : TowerHom R T) :
    TowerHom R (prodTower S T) where
  mapFun := fun x => (f.mapFun x, g.mapFun x)
  level_preserving := by
    intro i x hx
    exact ⟨f.level_preserving i x hx, g.level_preserving i x hx⟩

/-!
### 課題 D.5: 普遍性 — 射影との整合 (Computation Rules)

持ち上げた射が射影と正しく合成されることを検証する:
  π₁ ∘ lift(f, g) = f
  π₂ ∘ lift(f, g) = g

これらは積の「β-reduction 規則」に相当する。

**方針**: `TowerHom.ext` で基礎写像に帰着し、定義展開で `rfl`。
-/

/-- 第1射影との整合: π₁ ∘ ⟨f, g⟩ = f -/
theorem prodTower.fst_lift {R : StructureTower ι γ}
    (f : TowerHom R S) (g : TowerHom R T) :
    TowerHom.comp (prodTower.fst S T) (prodTower.lift S T f g) = f := by
  apply TowerHom.ext
  rfl

/-- 第2射影との整合: π₂ ∘ ⟨f, g⟩ = g -/
theorem prodTower.snd_lift {R : StructureTower ι γ}
    (f : TowerHom R S) (g : TowerHom R T) :
    TowerHom.comp (prodTower.snd S T) (prodTower.lift S T f g) = g := by
  apply TowerHom.ext
  rfl

/-!
### 課題 D.6: 普遍性 — 一意性 (Uniqueness)

射影との整合条件を満たす射は `lift` に限る:
  π₁ ∘ h = f かつ π₂ ∘ h = g ⇒ h = lift(f, g)

これが積の普遍性の「η-expansion 規則」に相当する。

**方針**:
  1. `TowerHom.ext` で基礎写像の等式に帰着
  2. `funext` で各点 x について示す
  3. `Prod.ext` でペアの等式を成分ごとに分解
  4. 仮定 hf, hg から `congrFun` で各成分を得る
-/

/-- 積の普遍性（一意性）: 射影条件を満たす射は lift に一致する
    Uniqueness of the universal morphism into the product -/
theorem prodTower.lift_unique {R : StructureTower ι γ}
    (f : TowerHom R S) (g : TowerHom R T)
    (h : TowerHom R (prodTower S T))
    (hf : TowerHom.comp (prodTower.fst S T) h = f)
    (hg : TowerHom.comp (prodTower.snd S T) h = g) :
    h = prodTower.lift S T f g := by
  apply TowerHom.ext
  funext x
  apply Prod.ext
  · have hfst : (TowerHom.comp (prodTower.fst S T) h).mapFun x = f.mapFun x := by
      exact congrArg (fun k : TowerHom R S => k.mapFun x) hf
    simpa [TowerHom.comp, prodTower.fst] using hfst
  · have hsnd : (TowerHom.comp (prodTower.snd S T) h).mapFun x = g.mapFun x := by
      exact congrArg (fun k : TowerHom R T => k.mapFun x) hg
    simpa [TowerHom.comp, prodTower.snd] using hsnd

end ProductTower

/-!
## 総括 / Summary

本課題で構成した内容の圏論的意味:

| 構成 | 圏論的概念 | 定理 |
|------|-----------|------|
| `TowerHom.mapFun` | 忘却関手 U | 関手公理 (A.1, A.2), 忠実性 (A.3) |
| `mapLevel` + `levelInclusion` | レベル関手族と自然変換 | 自然性 (B.3), 合成整合 (B.4) |
| `constTower` | 終対象（的構成） | 射の存在 (C.2), 一意性 (C.3) |
| `preimageTower` | 引き戻し / 逆像関手 | 構成 (C.4), 標準射 (C.5) |
| `prodTower` | 積 (Product) | 射影 (D.2,D.3), 普遍性 (D.4–D.6) |

## 発展課題（任意） / Extensions (Optional)

### 拡張1: 等化子 (Equalizer)
射 f, g : S → T の等化子を構成せよ:
  Eq(f,g) = (S, level i = {x ∈ S.level i | f(x) = g(x)})
普遍性を証明し、TowerCat が有限極限を持つことを示せ。

### 拡張2: 引き戻し塔の関手性
preimageTower が合成と恒等を保存する（反変関手をなす）ことを示せ:
  (f ∘ g)*(T) = g*(f*(T))

### 拡張3: Mathlib CategoryTheory との接続
`CategoryTheory.Category` インスタンスを StructureTower ι に登録し、
`CategoryTheory.Limits.HasBinaryProducts` を証明せよ。

## 参考文献 / References

- Bourbaki, N. *Théorie des ensembles*, Ch. IV §2 (Morphismes de structures)
- Mac Lane, S. *Categories for the Working Mathematician*, Ch. I–III
- Awodey, S. *Category Theory*, Ch. 5 (Limits and Colimits)
- Mathlib: `CategoryTheory.Category.Basic`, `CategoryTheory.Limits.Shapes.Products`
-/

end BourbakiLeanGuide
