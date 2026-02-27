import Mathlib.Data.Set.Lattice
import Mathlib.Order.Hom.Basic

/-!
# 課題: 等化子・始対象・零対象 — 有限完備性への道
# Task: Equalizers, Initial/Zero Objects — Road to Finite Completeness

## メタデータ / Metadata
- **課題番号**: ST-CAT-003
- **難易度**: レベル2–3（中級〜上級）
- **カテゴリ**: 圏論的視点 (Categorical Aspects)
- **推定所要時間**: 150–210 分
- **前提知識**:
  - ST-CAT-001（圏の骨格）
  - ST-CAT-002（積塔の普遍性）
  - ST-CAT-002-EX（終対象 unitTower）

## 導入 / Introduction

圏 𝒞 が **有限完備** (finitely complete) であるとは、
すべての有限図式の極限が存在することである。
これは以下の3条件と同値であることが知られている:

  (1) 終対象が存在する          ✓ ST-CAT-002-EX で証明済み
  (2) 任意の2対象の積が存在する  ✓ ST-CAT-002 Part D で証明済み
  (3) 任意の平行射対の等化子が存在する  ← 本課題 Part A

本課題では:

  **Part A** — 等化子 (Equalizer) を構成し普遍性を証明する
  **Part B** — 始対象 (Initial Object) を `Empty` 上の塔として構成する
  **Part C** — 零対象 (Zero Object) の存否を判定する
  **Part D** — 有限完備性の総括と、始対象との双対的比較

## 学習目標 / Learning Objectives

1. 等化子の部分集合的構成 `{x ∈ Sᵢ | f(x) = g(x)}` を形式化できる
2. 等化子の普遍性（存在・一意性）を完全に証明できる
3. `Empty.elim` を用いた始対象の構成に習熟する
4. 終対象と始対象の双対性、零対象の概念を理解する
5. 有限完備性の3条件の充足を確認できる

---

## ヒント総覧 / Hints Overview

### Part A (等化子)
- レベルの定義: `{x ∈ S.level i | f.mapFun x = g.mapFun x}` は
  `S.level i ∩ {x | f.mapFun x = g.mapFun x}` とも書ける
- `Set.sep_mono` や直接的な元の追跡で単調性を示す
- 普遍性の一意性は `TowerHom.ext` + 単射性（包含写像が単射）

### Part B (始対象)
- `Empty → α` は `Empty.elim` で一意に定まる
- `Empty.elim` の性質: 任意の `(a : Empty)` に対して任意の命題が成立
- `funext (fun x => Empty.elim x)` が鍵

### Part C (零対象)
- unitTower は終対象だが、始対象でもあるか？
- `Unit → α` は一意ではない（α に2元以上あれば）→ 反例構成
-/

open Set

namespace BourbakiLeanGuide

/-!
## 第0節: 既証明の結果
Section 0: Previously established results
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

/-- 終対象（ST-CAT-002-EX より）-/
def unitTower (ι : Type*) [Preorder ι] : StructureTower ι Unit where
  level := fun _ => Set.univ
  monotone_level := by intro i j _; exact Set.subset_univ _

def toUnitTower {ι α : Type*} [Preorder ι] (T : StructureTower ι α) :
    TowerHom T (unitTower ι) where
  mapFun := fun _ => ()
  level_preserving := by intro i x _; exact Set.mem_univ ()

theorem toUnitTower_unique {ι α : Type*} [Preorder ι]
    (T : StructureTower ι α) (f : TowerHom T (unitTower ι)) :
    f = toUnitTower T := by
  apply TowerHom.ext; funext x; exact Subsingleton.elim _ _

-- ═══════════════════════════════════════════════════════════════════════
-- ██  Part A: 等化子 (Equalizer)
-- ██  The key to finite completeness
-- ═══════════════════════════════════════════════════════════════════════

/-!
## 第1節: 等化子の構成

### 圏論的定義

射 f, g : S → T の **等化子** (equalizer) とは、
対象 E と射 ε : E → S の組 (E, ε) であって:

  (EQ1) f ∘ ε = g ∘ ε  （等化条件）
  (EQ2) 普遍性: 任意の h : R → S が f ∘ h = g ∘ h を満たすとき、
        ε ∘ ū = h なる射 ū : R → E が一意に存在する

  ```
            ε         f
    E ─────→ S ═══════⇉ T
    ▲               g
    │ū  (∃!)
    │
    R ─────→ S
          h
  ```

### 集合論的構成

  E.level i = {x ∈ S.level i | f(x) = g(x)}
  ε = 包含写像 (inclusion)

Bourbaki的に言えば、等化子は「2つの構造射が一致する部分構造」であり、
核 (kernel) の一般化にあたる。
-/

section Equalizer

variable {ι α β : Type*} [Preorder ι]
variable (S : StructureTower ι α) (T : StructureTower ι β)
variable (f g : TowerHom S T)

/-!
### 課題 A.1: 等化子塔の構成

レベルの定義:
  eqTower.level i = {x : α | x ∈ S.level i ∧ f.mapFun x = g.mapFun x}

単調性: i ≤ j, x ∈ eqTower.level i のとき
  x ∈ S.level i ∧ f(x) = g(x)
  ⇒ x ∈ S.level j ∧ f(x) = g(x)  （S の単調性 + 等式は不変）

**方針**: `And.intro` で分解し、左成分に `S.monotone_level`、右成分はそのまま。
-/

/-- 等化子塔: f と g が一致する元の部分塔
    Equalizer tower: the subtower where f and g agree -/
def eqTower : StructureTower ι α where
  level i := {x : α | x ∈ S.level i ∧ f.mapFun x = g.mapFun x}
  monotone_level := by
    intro i j hij x hx
    exact ⟨S.monotone_level hij hx.1, hx.2⟩

/-!
### 課題 A.2: 等化子からの包含射 (The Equalizing Map)

ε : eqTower → S は包含写像 id で、レベル保存は連言の左成分。

**方針**: `mapFun := id`, `hx.1` で S.level i への所属を取り出す。
-/

/-- 包含射: 等化子塔から元の塔への埋め込み
    The equalizing inclusion: eqTower ↪ S -/
def eqTower.incl : TowerHom (eqTower S T f g) S where
  mapFun := _root_.id
  level_preserving := by
    intro i x hx
    exact hx.1

/-!
### 課題 A.3: 等化条件 (Equalizing Condition)

f ∘ ε = g ∘ ε すなわち、包含射を経由すると f と g が一致する。

集合論的に: ε(x) = x かつ x ∈ eqTower ⇒ f(x) = g(x)
よって (f ∘ ε).mapFun x = f(x) = g(x) = (g ∘ ε).mapFun x

**方針**: `TowerHom.ext` + `funext` で各点 x : α に帰着。
ただし x は eqTower のレベルに属する必要はない（mapFun は α 全体で定義）。
注意: incl.mapFun = id なので comp f incl の mapFun = f.mapFun ∘ id = f.mapFun。
したがって f.mapFun = g.mapFun を示す必要は **ない**。
正しくは、comp の定義を展開すると両辺とも mapFun = f.mapFun (resp. g.mapFun) となり、
この等式は eqTower の元に制限して初めて成立する。

ここでの定式化を再考する:
comp f incl と comp g incl が TowerHom として等しいことは、
mapFun のレベルで f.mapFun ∘ id = g.mapFun ∘ id、つまり f.mapFun = g.mapFun を
要求してしまい、これは一般には偽。

正しい等化条件は **レベル上の制限** で述べる必要がある:
  ∀ i, ∀ x ∈ (eqTower S T f g).level i, f.mapFun x = g.mapFun x

これは等化子の定義から直接従う。
-/

/-- 等化条件: eqTower の元において f と g は一致する
    Equalizing condition: f and g agree on elements of eqTower -/
theorem eqTower.equalizes :
    ∀ (i : ι), ∀ x ∈ (eqTower S T f g).level i,
      f.mapFun x = g.mapFun x := by
  intro i x hx
  exact hx.2

/-!
### 課題 A.4: 普遍性 — 射の存在 (Universal Property: Existence)

任意の射 h : R → S が「f ∘ h と g ∘ h がレベル上で一致する」条件を満たすとき、
ū : R → eqTower で incl ∘ ū の mapFun = h.mapFun なるものを構成する。

集合論的に:
  ū.mapFun = h.mapFun  （基礎写像は同じ）
  レベル保存: x ∈ R.level i ⇒ h(x) ∈ S.level i ∧ f(h(x)) = g(h(x))
  前者は h.level_preserving、後者は仮定 heq から。

**方針**: `And.intro` で h.level_preserving と heq を結合。
-/

variable {γ : Type*}

/-- 普遍射の構成: h が等化条件を満たすなら eqTower へ持ち上がる
    Universal lift: if h equalizes f and g, it factors through eqTower -/
def eqTower.lift {R : StructureTower ι γ}
    (h : TowerHom R S)
    (heq : ∀ (i : ι), ∀ x ∈ R.level i,
      f.mapFun (h.mapFun x) = g.mapFun (h.mapFun x)) :
    TowerHom R (eqTower S T f g) where
  mapFun := h.mapFun
  level_preserving := by
    intro i x hx
    exact ⟨h.level_preserving i x hx, heq i x hx⟩

/-!
### 課題 A.5: 普遍性 — 包含射との整合 (Computation Rule)

incl ∘ ū の基礎写像 = h.mapFun

包含射の mapFun = id なので、(incl ∘ ū).mapFun = id ∘ h.mapFun = h.mapFun

**方針**: `TowerHom.ext` + `rfl`
-/

/-- 包含射との整合: ε ∘ ū = h（mapFun のレベルで）
    Computation rule: incl ∘ lift = h -/
theorem eqTower.incl_lift {R : StructureTower ι γ}
    (h : TowerHom R S)
    (heq : ∀ (i : ι), ∀ x ∈ R.level i,
      f.mapFun (h.mapFun x) = g.mapFun (h.mapFun x)) :
    TowerHom.comp (eqTower.incl S T f g) (eqTower.lift S T f g h heq) = h := by
  apply TowerHom.ext
  rfl

/-!
### 課題 A.6: 普遍性 — 一意性 (Uniqueness)

incl ∘ k の mapFun = h.mapFun を満たす k : R → eqTower は lift に一致する。

核心: incl.mapFun = id なので k.mapFun = h.mapFun が直接得られる。

**方針**: `TowerHom.ext` で帰着。仮定 hk から `congrArg ... hk` で
mapFun の等式を得る。
-/

/-- 等化子への射の一意性
    Uniqueness of the morphism into the equalizer -/
theorem eqTower.lift_unique {R : StructureTower ι γ}
    (h : TowerHom R S)
    (heq : ∀ (i : ι), ∀ x ∈ R.level i,
      f.mapFun (h.mapFun x) = g.mapFun (h.mapFun x))
    (k : TowerHom R (eqTower S T f g))
    (hk : TowerHom.comp (eqTower.incl S T f g) k = h) :
    k = eqTower.lift S T f g h heq := by
  apply TowerHom.ext
  simpa [TowerHom.comp, eqTower.incl, eqTower.lift] using
    congrArg TowerHom.mapFun hk

end Equalizer

-- ═══════════════════════════════════════════════════════════════════════
-- ██  Part B: 始対象 (Initial Object)
-- ██  The dual of the terminal object
-- ═══════════════════════════════════════════════════════════════════════

/-!
## 第2節: Empty 上の構造塔と始対象

### 圏論的定義

始対象 (initial object) I とは、任意の対象 T に対して
射 I → T が一意に存在するもの:
  ∀ T, ∃! (f : TowerHom I T), True

### 集合論的構成

基礎型を Empty（空集合 ∅）とする:
  emptyTower : StructureTower ι Empty
  level i = ∅  （Empty 型に元がないので Set.univ = ∅）

Empty → α の写像は `Empty.elim` で一意に定まる。
（空集合からの写像は空写像しかない——Bourbaki的に
 「空な対応は一意に定まる」(l'application vide est unique)）

### 終対象との双対性

| | 終対象 (unitTower) | 始対象 (emptyTower) |
|---|---|---|
| 基礎型 | Unit（一点集合 {*}） | Empty（空集合 ∅） |
| 射の方向 | T → unitTower（任意の T から） | emptyTower → T（任意の T へ） |
| 一意性の源泉 | α → Unit は一意 | Empty → α は一意 |
| Lean での鍵 | Subsingleton.elim | Empty.elim / funext |
-/

section InitialObject

variable {ι α : Type*} [Preorder ι]

/-!
### 課題 B.1: 空塔の構成

Empty 上の構造塔。すべてのレベルは空集合。
（Empty 型では Set.univ = ∅ が成り立つ）

単調性: ∅ ⊆ ∅ は自明。

**方針**: `level := fun _ => Set.univ`, 単調性は `Set.subset_univ`。
あるいは `level := fun _ => ∅` として `Set.empty_subset` でもよい。
-/

/-- 空塔: 基礎型が Empty の構造塔
    Empty tower: the structure tower over the empty type -/
def emptyTower (ι : Type*) [Preorder ι] : StructureTower ι Empty where
  level := fun _ => Set.univ
  monotone_level := by
    intro i j _
    exact Set.subset_univ _

/-!
### 課題 B.2: 空塔からの射の存在

任意の塔 T : StructureTower ι α に対して emptyTower → T の射を構成する。

mapFun : Empty → α は `Empty.elim` で定義する。
レベル保存: ∀ i, ∀ x ∈ emptyTower.level i, ... だが x : Empty なので空真。

**方針**: `intro i x`, x : Empty に対して `exact Empty.elim x` で即座に閉じる。
-/

/-- 空塔からの標準射（始対象からの射）
    The canonical morphism from the empty tower -/
def fromEmptyTower (T : StructureTower ι α) :
    TowerHom (emptyTower ι) T where
  mapFun := Empty.elim
  level_preserving := by
    intro i x hx
    exact Empty.elim x

/-!
### 課題 B.3: 空塔からの射の一意性

任意の射 f : emptyTower → T は fromEmptyTower T に等しい。

核心: Empty → α の写像は一意。
Lean では `funext (fun x => Empty.elim x)` または
`funext (fun x => absurd x ...)` で示せる。

**方針**: `TowerHom.ext` で mapFun の等式に帰着。
`funext` で各点 x : Empty について示すが、x : Empty なので即座に矛盾。
-/

/-- 空塔からの射は一意 -/
theorem fromEmptyTower_unique (T : StructureTower ι α)
    (f : TowerHom (emptyTower ι) T) :
    f = fromEmptyTower T := by
  apply TowerHom.ext
  funext x
  exact Empty.elim x

/-!
### 課題 B.4: 始対象の普遍性（∃!）
-/

/-- emptyTower は始対象: 任意の塔への射が一意に存在する
    emptyTower is initial: there exists a unique morphism to any tower -/
theorem emptyTower_initial (T : StructureTower ι α) :
    ∃! (_f : TowerHom (emptyTower ι) T), True := by
  refine ⟨fromEmptyTower T, trivial, ?_⟩
  intro g _hg
  exact fromEmptyTower_unique T g

end InitialObject

-- ═══════════════════════════════════════════════════════════════════════
-- ██  Part C: 零対象の存否 (Zero Object)
-- ██  Does TowerCat have a zero object?
-- ═══════════════════════════════════════════════════════════════════════

/-!
## 第3節: 零対象は存在するか？

### 定義

零対象 (zero object) とは、始対象かつ終対象であるもの。

### 候補の検討

| 候補 | 終対象? | 始対象? | 零対象? |
|------|---------|---------|---------|
| unitTower | ✓（α → Unit は一意）| ? | ? |
| emptyTower | ? | ✓（Empty → α は一意）| ? |

疑問: unitTower は始対象でもあるか？

unitTower → T の射 f は mapFun : Unit → α を持つ。
α に2元以上あれば Unit → α は一意でない:
  f₁(()) = a₁,  f₂(()) = a₂  （a₁ ≠ a₂）

したがって unitTower は始対象でない → 零対象でない。
対称的に、emptyTower は終対象でない（α → Empty は α = Empty のときしか存在しない）。

### 結論

TowerCat(ι) において **始対象と終対象は異なる対象** であり、
零対象は一般には存在しない。これは Set（集合の圏）と同じ状況である。

（ただし、ι = Empty や α が固定された部分圏では事情が異なりうる。）
-/

section ZeroObject

/-!
### 課題 C.1: unitTower は始対象でない — 反例

Bool 上の塔2つへの異なる射を構成する。

unitTower → constTower ℕ Bool の射を2つ作る:
  ψ₁ : mapFun () = true
  ψ₂ : mapFun () = false

**方針**: anyMapToConst パターンと同様、constTower のレベルが univ なので
任意の写像がレベルを保存する。
-/

/-- Bool 上の定値塔 -/
def boolConstTower : StructureTower ℕ Bool :=
  { level := fun _ => Set.univ
    monotone_level := by intro i j _; exact Set.subset_univ _ }

/-- 第1の射: () ↦ true -/
def ψ₁ : TowerHom (unitTower ℕ) boolConstTower where
  mapFun := fun _ => true
  level_preserving := by
    intro i x hx
    exact Set.mem_univ true

/-- 第2の射: () ↦ false -/
def ψ₂ : TowerHom (unitTower ℕ) boolConstTower where
  mapFun := fun _ => false
  level_preserving := by
    intro i x hx
    exact Set.mem_univ false

/-!
### 課題 C.2: 2つの射が異なることの証明

ψ₁.mapFun () = true ≠ false = ψ₂.mapFun ()

**方針**: `congrFun` で点 () に特化し、`Bool.noConfusion` で矛盾。
-/

/-- ψ₁ ≠ ψ₂ : unitTower は始対象でない -/
theorem ψ₁_ne_ψ₂ : ψ₁ ≠ ψ₂ := by
  intro h
  have hmap : ψ₁.mapFun = ψ₂.mapFun := congrArg TowerHom.mapFun h
  have hpoint : true = false := by
    simpa [ψ₁, ψ₂] using congrFun hmap ()
  exact Bool.false_ne_true hpoint.symm

/-!
### 課題 C.3: unitTower が始対象でないことの明示的な否定文

始対象の定義「∀ T, ∃! f, True」の否定:
  ∃ T, ¬ ∃! f, True
  ⟺ ∃ T, ∀ を satisfying, f と g が異なりうる

**方針**: T = boolConstTower を反例として、ψ₁ ≠ ψ₂ を使う。
-/

/-- unitTower は始対象でない
    unitTower is NOT initial -/
theorem unitTower_not_initial :
    ¬ (∀ (T : StructureTower ℕ Bool),
      ∃! (_f : TowerHom (unitTower ℕ) T), True) := by
  intro h
  rcases h boolConstTower with ⟨f, _hf, huniq⟩
  have h1 : ψ₁ = f := huniq ψ₁ trivial
  have h2 : ψ₂ = f := huniq ψ₂ trivial
  exact ψ₁_ne_ψ₂ (h1.trans h2.symm)

end ZeroObject

-- ═══════════════════════════════════════════════════════════════════════
-- ██  Part D: 有限完備性の総括
-- ██  Summary: Finite Completeness of TowerCat
-- ═══════════════════════════════════════════════════════════════════════

/-!
## 第4節: TowerCat の有限完備性

### 定理（非形式的）

固定された前順序 (ι, ≤) に対して、
添字型を ι とする構造塔とその射がなす圏を TowerCat(ι) と書く。

注意: 厳密には TowerCat(ι) の対象は Σ α, StructureTower ι α（基礎型も動く）
であるが、ここでは射が同一添字型の塔間でのみ定義されていることを踏まえて
「基礎型ごとのスライス」で議論している。

### 有限完備性の3条件

| 条件 | 構成 | 証明箇所 |
|------|------|---------|
| (1) 終対象 | unitTower ι | ST-CAT-002-EX: `unitTower_terminal` |
| (2) 二項積 | prodTower S T | ST-CAT-002: `prodTower.lift`, `lift_unique` |
| (3) 等化子 | eqTower S T f g | 本課題 Part A: `eqTower.lift`, `lift_unique` |

3条件がすべて満たされたので、TowerCat(ι) は **有限完備** である。

### 始対象・終対象の比較表

| 性質 | 終対象 (unitTower) | 始対象 (emptyTower) |
|------|-------------------|---------------------|
| 基礎型 | Unit = {*} | Empty = ∅ |
| レベル | ∀ i, univ (= {*}) | ∀ i, univ (= ∅) |
| 写像空間 | α → Unit ≅ {*} | Empty → α ≅ {*} |
| 一意性の根拠 | Subsingleton (α → Unit) | Subsingleton (Empty → α) |
| Lean の道具 | Subsingleton.elim | Empty.elim / funext |
| 零対象か | No（始対象でない） | No（終対象でない） |

### 双対性の原理 (Duality Principle)

終対象と始対象は圏論的双対 (categorical dual) の関係にある:
- 終対象: 射が **入ってくる** 方向で一意
- 始対象: 射が **出ていく** 方向で一意

TowerCat では:
- 終対象の一意性は **値域の型** (Unit) が一点であることに由来
- 始対象の一意性は **定義域の型** (Empty) が空であることに由来

零対象が存在しないのは、「一点集合」と「空集合」が異なるためであり、
これは集合の圏 Set の性質を反映している。

## 発展課題 / Extensions

### 拡張1: 余等化子 (Coequalizer)
等化子の双対として余等化子を構成せよ。商集合を用いた構成が必要になる。

### 拡張2: 引き戻し (Pullback) を積と等化子から構成
一般的定理: 積と等化子を持つ圏は引き戻しを持つ。
  Pullback(f, g) = Eq(f ∘ π₁, g ∘ π₂) where π₁, π₂ are projections of S × T
これを TowerCat で具体的に実行せよ。

### 拡張3: 有限余完備性
TowerCat は有限余完備か？ 余積、余等化子、始対象を構成せよ。
（余積は直和型 α ⊕ β 上の塔として構成可能）

### 拡張4: Mathlib の HasFiniteLimits
`CategoryTheory.Limits.HasFiniteLimits` インスタンスを TowerCat に登録せよ。

## 参考文献 / References

- Bourbaki, N. *Théorie des ensembles*, Ch. IV (Structures)
- Mac Lane, S. *Categories for the Working Mathematician*, Ch. V (Limits)
- Awodey, S. *Category Theory*, Ch. 5 §5.5 (Completeness)
- Borceux, F. *Handbook of Categorical Algebra I*, Ch. 2.8 (Equalizers)
- Mathlib: `CategoryTheory.Limits.Shapes.Equalizers`,
  `CategoryTheory.Limits.HasLimits`
-/

-- ═══════════════════════════════════════════════════════════════════════
-- ██  Extension 1: Coequalizer
-- ═══════════════════════════════════════════════════════════════════════

section Coequalizer

variable {ι α β : Type*} [Preorder ι]
variable (S : StructureTower ι α) (T : StructureTower ι β)
variable (f g : TowerHom S T)

/-- The generating relation for the coequalizer of `f,g`. -/
def coeqRelBase : β → β → Prop :=
  fun b b' => ∃ x : α, f.mapFun x = b ∧ g.mapFun x = b'

/-- Setoid generated by the pairs `f x ~ g x`. -/
def coeqSetoid : Setoid β where
  r := Relation.EqvGen (coeqRelBase S T f g)
  iseqv := Relation.EqvGen.is_equivalence _

/-- Coequalizer tower: quotient of the codomain tower by `coeqSetoid`. -/
def coeqTower : StructureTower ι (Quotient (coeqSetoid S T f g)) where
  level i := (fun b : β => (⟦b⟧ : Quotient (coeqSetoid S T f g))) '' T.level i
  monotone_level := by
    intro i j hij q hq
    rcases hq with ⟨y, hy, rfl⟩
    exact ⟨y, T.monotone_level hij hy, rfl⟩

/-- Quotient projection `T ⟶ coeqTower`. -/
def coeqProj : TowerHom T (coeqTower S T f g) where
  mapFun := fun x => (⟦x⟧ : Quotient (coeqSetoid S T f g))
  level_preserving := by
    intro i x hx
    exact ⟨x, hx, rfl⟩

/-- Coequalizing equation for the projection map. -/
theorem coeqProj_coequalizes (x : α) :
    (TowerHom.comp (coeqProj S T f g) f).mapFun x =
    (TowerHom.comp (coeqProj S T f g) g).mapFun x := by
  change
      ((⟦f.mapFun x⟧ : Quotient (coeqSetoid S T f g)) =
        (⟦g.mapFun x⟧ : Quotient (coeqSetoid S T f g)))
  exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨x, rfl, rfl⟩)

variable {ρ : Type*}

/-- Under the coequalizing hypothesis, define the induced map on the quotient type. -/
def coeqDescFun {R : StructureTower ι ρ}
    (h : TowerHom T R)
    (heq : ∀ x : α, h.mapFun (f.mapFun x) = h.mapFun (g.mapFun x)) :
    Quotient (coeqSetoid S T f g) → ρ :=
  Quotient.lift h.mapFun (by
    intro b b' hb
    induction hb with
    | rel b b' hbase =>
        rcases hbase with ⟨x, rfl, rfl⟩
        exact heq x
    | refl b =>
        rfl
    | symm b b' _ ih =>
        exact ih.symm
    | trans b b' c _ _ ih₁ ih₂ =>
        exact ih₁.trans ih₂)

/-- Universal morphism from the coequalizer tower. -/
def coeqDesc {R : StructureTower ι ρ}
    (h : TowerHom T R)
    (heq : ∀ x : α, h.mapFun (f.mapFun x) = h.mapFun (g.mapFun x)) :
    TowerHom (coeqTower S T f g) R where
  mapFun := coeqDescFun S T f g h heq
  level_preserving := by
    intro i q hq
    rcases hq with ⟨y, hy, rfl⟩
    simpa [coeqDescFun] using h.level_preserving i y hy

/-- Factorization equation `coeqDesc ≫ coeqProj = h`. -/
theorem coeqDesc_comp_proj {R : StructureTower ι ρ}
    (h : TowerHom T R)
    (heq : ∀ x : α, h.mapFun (f.mapFun x) = h.mapFun (g.mapFun x)) :
    TowerHom.comp (coeqDesc S T f g h heq) (coeqProj S T f g) = h := by
  apply TowerHom.ext
  funext x
  rfl

/-- Uniqueness of morphisms out of the coequalizer. -/
theorem coeqDesc_unique {R : StructureTower ι ρ}
    (h : TowerHom T R)
    (heq : ∀ x : α, h.mapFun (f.mapFun x) = h.mapFun (g.mapFun x))
    (k : TowerHom (coeqTower S T f g) R)
    (hk : TowerHom.comp k (coeqProj S T f g) = h) :
    k = coeqDesc S T f g h heq := by
  apply TowerHom.ext
  funext q
  refine Quotient.inductionOn q ?_
  intro b
  have hkb : k.mapFun ((⟦b⟧ : Quotient (coeqSetoid S T f g))) = h.mapFun b := by
    have hk' : (TowerHom.comp k (coeqProj S T f g)).mapFun b = h.mapFun b := by
      exact congrArg (fun m : TowerHom T R => m.mapFun b) hk
    simpa [TowerHom.comp, coeqProj] using hk'
  have hdb : (coeqDesc S T f g h heq).mapFun
      ((⟦b⟧ : Quotient (coeqSetoid S T f g))) = h.mapFun b := by
    rfl
  exact hkb.trans hdb.symm

/-- Universal property of coequalizer (`∃!`). -/
theorem coeq_universal {R : StructureTower ι ρ}
    (h : TowerHom T R)
    (heq : ∀ x : α, h.mapFun (f.mapFun x) = h.mapFun (g.mapFun x)) :
    ∃! (u : TowerHom (coeqTower S T f g) R),
      TowerHom.comp u (coeqProj S T f g) = h := by
  refine ⟨coeqDesc S T f g h heq, coeqDesc_comp_proj S T f g h heq, ?_⟩
  intro u hu
  exact coeqDesc_unique S T f g h heq u hu

end Coequalizer

-- ═══════════════════════════════════════════════════════════════════════
-- ██  Extension 2: Pullback from Product + Equalizer
-- ═══════════════════════════════════════════════════════════════════════

section PullbackViaEqualizer

variable {ι α β γ : Type*} [Preorder ι]
variable (S : StructureTower ι α) (T : StructureTower ι β)

/-- Binary product tower used in pullback construction. -/
def prodTower : StructureTower ι (α × β) where
  level i := {p : α × β | p.1 ∈ S.level i ∧ p.2 ∈ T.level i}
  monotone_level := by
    intro i j hij p hp
    exact ⟨S.monotone_level hij hp.1, T.monotone_level hij hp.2⟩

/-- First projection from `prodTower`. -/
def prodTower.fst : TowerHom (prodTower S T) S where
  mapFun := Prod.fst
  level_preserving := by
    intro i x hx
    exact hx.1

/-- Second projection from `prodTower`. -/
def prodTower.snd : TowerHom (prodTower S T) T where
  mapFun := Prod.snd
  level_preserving := by
    intro i x hx
    exact hx.2

variable {δ : Type*}

/-- Pairing map into the product tower. -/
def prodTower.lift {R : StructureTower ι δ}
    (p : TowerHom R S) (q : TowerHom R T) :
    TowerHom R (prodTower S T) where
  mapFun := fun x => (p.mapFun x, q.mapFun x)
  level_preserving := by
    intro i x hx
    exact ⟨p.level_preserving i x hx, q.level_preserving i x hx⟩

variable (U : StructureTower ι γ)
variable (f : TowerHom S U) (g : TowerHom T U)

/-- Pullback tower as equalizer of `f ∘ π₁` and `g ∘ π₂`. -/
def pullbackTower : StructureTower ι (α × β) :=
  eqTower (prodTower S T) U
    (TowerHom.comp f (prodTower.fst S T))
    (TowerHom.comp g (prodTower.snd S T))

/-- Pullback projection to the left leg. -/
def pullback.fst : TowerHom (pullbackTower S T U f g) S :=
  TowerHom.comp (prodTower.fst S T)
    (eqTower.incl (prodTower S T) U
      (TowerHom.comp f (prodTower.fst S T))
      (TowerHom.comp g (prodTower.snd S T)))

/-- Pullback projection to the right leg. -/
def pullback.snd : TowerHom (pullbackTower S T U f g) T :=
  TowerHom.comp (prodTower.snd S T)
    (eqTower.incl (prodTower S T) U
      (TowerHom.comp f (prodTower.fst S T))
      (TowerHom.comp g (prodTower.snd S T)))

/-- Pullback commutativity condition on each level. -/
theorem pullback.condition :
    ∀ (i : ι), ∀ x ∈ (pullbackTower S T U f g).level i,
      f.mapFun x.1 = g.mapFun x.2 := by
  intro i x hx
  simpa [pullbackTower, TowerHom.comp, prodTower.fst, prodTower.snd] using
    (eqTower.equalizes
      (S := prodTower S T) (T := U)
      (f := TowerHom.comp f (prodTower.fst S T))
      (g := TowerHom.comp g (prodTower.snd S T))
      i x hx)

/-- Universal morphism into `pullbackTower`. -/
def pullback.lift {R : StructureTower ι δ}
    (p : TowerHom R S) (q : TowerHom R T)
    (hcomm : ∀ (i : ι), ∀ x ∈ R.level i,
      f.mapFun (p.mapFun x) = g.mapFun (q.mapFun x)) :
    TowerHom R (pullbackTower S T U f g) :=
  eqTower.lift
    (S := prodTower S T) (T := U)
    (f := TowerHom.comp f (prodTower.fst S T))
    (g := TowerHom.comp g (prodTower.snd S T))
    (h := prodTower.lift S T p q)
    (by
      intro i x hx
      simpa [TowerHom.comp, prodTower.fst, prodTower.snd, prodTower.lift] using
        hcomm i x hx)

/-- First pullback projection computes on `pullback.lift`. -/
theorem pullback.fst_lift {R : StructureTower ι δ}
    (p : TowerHom R S) (q : TowerHom R T)
    (hcomm : ∀ (i : ι), ∀ x ∈ R.level i,
      f.mapFun (p.mapFun x) = g.mapFun (q.mapFun x)) :
    TowerHom.comp (pullback.fst S T U f g) (pullback.lift S T U f g p q hcomm) = p := by
  apply TowerHom.ext
  rfl

/-- Second pullback projection computes on `pullback.lift`. -/
theorem pullback.snd_lift {R : StructureTower ι δ}
    (p : TowerHom R S) (q : TowerHom R T)
    (hcomm : ∀ (i : ι), ∀ x ∈ R.level i,
      f.mapFun (p.mapFun x) = g.mapFun (q.mapFun x)) :
    TowerHom.comp (pullback.snd S T U f g) (pullback.lift S T U f g p q hcomm) = q := by
  apply TowerHom.ext
  rfl

/-- Uniqueness of morphisms into `pullbackTower`. -/
theorem pullback.lift_unique {R : StructureTower ι δ}
    (p : TowerHom R S) (q : TowerHom R T)
    (hcomm : ∀ (i : ι), ∀ x ∈ R.level i,
      f.mapFun (p.mapFun x) = g.mapFun (q.mapFun x))
    (k : TowerHom R (pullbackTower S T U f g))
    (hkfst : TowerHom.comp (pullback.fst S T U f g) k = p)
    (hksnd : TowerHom.comp (pullback.snd S T U f g) k = q) :
    k = pullback.lift S T U f g p q hcomm := by
  apply TowerHom.ext
  funext x
  have hx1 : (k.mapFun x).1 = p.mapFun x := by
    have h1 : (TowerHom.comp (pullback.fst S T U f g) k).mapFun x = p.mapFun x := by
      exact congrArg (fun m : TowerHom R S => m.mapFun x) hkfst
    simpa [pullback.fst, TowerHom.comp, prodTower.fst] using h1
  have hx2 : (k.mapFun x).2 = q.mapFun x := by
    have h2 : (TowerHom.comp (pullback.snd S T U f g) k).mapFun x = q.mapFun x := by
      exact congrArg (fun m : TowerHom R T => m.mapFun x) hksnd
    simpa [pullback.snd, TowerHom.comp, prodTower.snd] using h2
  have hpair : k.mapFun x = (p.mapFun x, q.mapFun x) := Prod.ext hx1 hx2
  simpa [pullback.lift, prodTower.lift] using hpair

end PullbackViaEqualizer

-- ═══════════════════════════════════════════════════════════════════════
-- ██  Extension 3: Binary Coproduct + Cocomplete Spine
-- ═══════════════════════════════════════════════════════════════════════

section Coproduct

variable {ι α β : Type*} [Preorder ι]
variable (S : StructureTower ι α) (T : StructureTower ι β)

/-- Binary coproduct tower over `Sum α β`. -/
def coprodTower : StructureTower ι (Sum α β) where
  level i := {x : Sum α β |
    match x with
    | Sum.inl a => a ∈ S.level i
    | Sum.inr b => b ∈ T.level i}
  monotone_level := by
    intro i j hij x hx
    cases x with
    | inl a =>
        exact S.monotone_level hij hx
    | inr b =>
        exact T.monotone_level hij hx

/-- Left injection into `coprodTower`. -/
def coprod.inl : TowerHom S (coprodTower S T) where
  mapFun := Sum.inl
  level_preserving := by
    intro i x hx
    simpa [coprodTower]

/-- Right injection into `coprodTower`. -/
def coprod.inr : TowerHom T (coprodTower S T) where
  mapFun := Sum.inr
  level_preserving := by
    intro i x hx
    simpa [coprodTower]

variable {ρ : Type*}

/-- Copairing map from `coprodTower`. -/
def coprod.desc {R : StructureTower ι ρ}
    (f : TowerHom S R) (g : TowerHom T R) :
    TowerHom (coprodTower S T) R where
  mapFun := Sum.elim f.mapFun g.mapFun
  level_preserving := by
    intro i x hx
    cases x with
    | inl a =>
        simpa using f.level_preserving i a hx
    | inr b =>
        simpa using g.level_preserving i b hx

/-- `coprod.desc` reduces on the left injection. -/
theorem coprod.desc_inl {R : StructureTower ι ρ}
    (f : TowerHom S R) (g : TowerHom T R) :
    TowerHom.comp (coprod.desc S T f g) (coprod.inl S T) = f := by
  apply TowerHom.ext
  rfl

/-- `coprod.desc` reduces on the right injection. -/
theorem coprod.desc_inr {R : StructureTower ι ρ}
    (f : TowerHom S R) (g : TowerHom T R) :
    TowerHom.comp (coprod.desc S T f g) (coprod.inr S T) = g := by
  apply TowerHom.ext
  rfl

/-- Uniqueness of morphisms out of the binary coproduct. -/
theorem coprod.desc_unique {R : StructureTower ι ρ}
    (f : TowerHom S R) (g : TowerHom T R)
    (h : TowerHom (coprodTower S T) R)
    (hinl : TowerHom.comp h (coprod.inl S T) = f)
    (hinr : TowerHom.comp h (coprod.inr S T) = g) :
    h = coprod.desc S T f g := by
  apply TowerHom.ext
  funext x
  cases x with
  | inl a =>
      have hl : (TowerHom.comp h (coprod.inl S T)).mapFun a = f.mapFun a := by
        exact congrArg (fun m : TowerHom S R => m.mapFun a) hinl
      simpa [TowerHom.comp, coprod.inl, coprod.desc] using hl
  | inr b =>
      have hr : (TowerHom.comp h (coprod.inr S T)).mapFun b = g.mapFun b := by
        exact congrArg (fun m : TowerHom T R => m.mapFun b) hinr
      simpa [TowerHom.comp, coprod.inr, coprod.desc] using hr

/-- Universal property of binary coproduct (`∃!`). -/
theorem coprod.universal {R : StructureTower ι ρ}
    (f : TowerHom S R) (g : TowerHom T R) :
    ∃! (u : TowerHom (coprodTower S T) R),
      TowerHom.comp u (coprod.inl S T) = f ∧
      TowerHom.comp u (coprod.inr S T) = g := by
  refine ⟨coprod.desc S T f g, ?_, ?_⟩
  · exact ⟨coprod.desc_inl S T f g, coprod.desc_inr S T f g⟩
  · intro u hu
    exact coprod.desc_unique S T f g u hu.1 hu.2

end Coproduct

section FiniteCocompleteSpine

variable {ι : Type*} [Preorder ι]

/-- A finite-cocompleteness spine:
initial object, binary coproducts, and coequalizers. -/
theorem towercat_finite_cocomplete_spine :
    (∀ {α : Type*} (T : StructureTower ι α),
      ∃! (_f : TowerHom (emptyTower ι) T), True) ∧
    (∀ {α β ρ : Type*}
      (S : StructureTower ι α) (T : StructureTower ι β) (R : StructureTower ι ρ)
      (f : TowerHom S R) (g : TowerHom T R),
      ∃! (u : TowerHom (coprodTower S T) R),
        TowerHom.comp u (coprod.inl S T) = f ∧
        TowerHom.comp u (coprod.inr S T) = g) ∧
    (∀ {α β ρ : Type*}
      (S : StructureTower ι α) (T : StructureTower ι β)
      (f g : TowerHom S T) (R : StructureTower ι ρ)
      (h : TowerHom T R),
      ((∀ x : α, h.mapFun (f.mapFun x) = h.mapFun (g.mapFun x)) →
        ∃! (u : TowerHom (coeqTower S T f g) R),
          TowerHom.comp u (coeqProj S T f g) = h)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro α T
    simpa using emptyTower_initial (ι := ι) (α := α) T
  · intro α β ρ S T R f g
    exact coprod.universal (S := S) (T := T) (R := R) f g
  · intro α β ρ S T f g R h heq
    exact coeq_universal (S := S) (T := T) (f := f) (g := g) (R := R) h heq

end FiniteCocompleteSpine

end BourbakiLeanGuide
