import Mathlib.Data.Set.Lattice
import Mathlib.Order.Hom.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# 補題課題: 定値塔は終対象ではない
# Challenge: constTower is NOT a terminal object

## メタデータ / Metadata
- **課題番号**: ST-CAT-002-EX
- **難易度**: レベル2（中級）— 反例構成
- **前提**: ST-CAT-002 Part C の完了

## 動機 / Motivation

ST-CAT-002 の C.2–C.3 では以下を示した:

  (C.2) 任意の T に対して、射 T → constTower で mapFun = id であるものが存在する
  (C.3) そのような射は一意である

これは一見「終対象」(terminal object) の普遍性に見えるが、
圏論的な終対象の定義は **射の一意的存在** (∃!) であり、
mapFun に制約を課さない:

  終対象 Z : ∀ T, ∃! (f : TowerHom T Z), True

問題: constTower ι α はこの意味での終対象か？

答え: **否**。constTower のレベルはすべて Set.univ なので、
**任意の** 写像 f : α → α がレベル保存条件を自明に満たしてしまう。
α に2元以上あれば、id 以外の射も構成でき、一意性が崩れる。

この課題では反例を構成してこれを形式的に証明する。
-/

open Set

namespace BourbakiLeanGuide

/-! ## 既知の定義（再掲）-/

structure StructureTower (ι α : Type*) [Preorder ι] : Type _ where
  level : ι → Set α
  monotone_level : ∀ ⦃i j⦄, i ≤ j → level i ⊆ level j

structure TowerHom {ι α β : Type*} [Preorder ι]
    (S : StructureTower ι α) (T : StructureTower ι β) where
  mapFun : α → β
  level_preserving : ∀ (i : ι), ∀ x ∈ S.level i, mapFun x ∈ T.level i

namespace TowerHom

variable {ι α β : Type*} [Preorder ι]
variable {S : StructureTower ι α} {T : StructureTower ι β}

@[ext]
theorem ext (f g : TowerHom S T) (h : f.mapFun = g.mapFun) : f = g := by
  cases f; cases g; simp only [mk.injEq]; exact h

end TowerHom

def constTower (ι α : Type*) [Preorder ι] : StructureTower ι α where
  level := fun _ => Set.univ
  monotone_level := by intro i j _; exact Set.subset_univ _

def toConstTower {ι α : Type*} [Preorder ι] (T : StructureTower ι α) :
    TowerHom T (constTower ι α) where
  mapFun := _root_.id
  level_preserving := by intro i x _; exact Set.mem_univ x

-- ═══════════════════════════════════════════════════════════════════
-- ██  Part 1: 任意の写像から射が作れることの証明
-- ██  Any map α → α yields a morphism to constTower
-- ═══════════════════════════════════════════════════════════════════

/-!
### 課題 1: constTower への「自由な」射の構成

constTower のレベルが Set.univ であることから、
**任意の** 写像 f : α → α に対して T → constTower ι α の射が構成できる。

これが終対象の一意性を破壊する元凶である。

集合論的に:
  ∀ f : α → α, ∀ i, ∀ x ∈ T.level i, f(x) ∈ Set.univ
  これは Set.mem_univ から自明。

**方針**: `toConstTower` と同様だが、mapFun を任意の f にする。
-/

/-- 任意の写像から constTower への射を構成する
    Any map yields a valid morphism into constTower -/
def anyMapToConst {ι α : Type*} [Preorder ι]
    (T : StructureTower ι α) (f : α → α) :
    TowerHom T (constTower ι α) where
  mapFun := f
  level_preserving := by
    intro i x hx
    exact Set.mem_univ (f x)

/-- 一般化版: 任意の `f : α → β` から `T ⟶ constTower ι β` を作る。 -/
def homToConst {ι α β : Type*} [Preorder ι]
    (T : StructureTower ι α) (f : α → β) :
    TowerHom T (constTower ι β) where
  mapFun := f
  level_preserving := by
    intro i x _
    exact Set.mem_univ (f x)

theorem not_terminal_constTower {ι α β : Type*} [Preorder ι]
    (T : StructureTower ι α) [Nonempty α] [Nontrivial β] :
    ¬ (∃! (_h : TowerHom T (constTower ι β)), True) := by
  classical
  obtain ⟨b₁, b₂, hb⟩ := exists_pair_ne β
  let f : α → β := fun _ => b₁
  let g : α → β := fun _ => b₂

  let hf : TowerHom T (constTower ι β) := homToConst (ι:=ι) (T:=T) f
  let hg : TowerHom T (constTower ι β) := homToConst (ι:=ι) (T:=T) g

  have hne : hf ≠ hg := by
    intro hEq
    -- ここは TowerHom.ext があればもっと綺麗にできる
    have hm : hf.mapFun = hg.mapFun := congrArg TowerHom.mapFun hEq
    let a0 : α := Classical.choice (inferInstance : Nonempty α)
    have : f a0 = g a0 := congrArg (fun u => u a0) hm
    exact hb (by simpa [f, g] using this)

  intro hex
  rcases hex with ⟨u, _, hu⟩
  have : hf = hg := by
    have hfu : hf = u := hu hf trivial
    have hgu : hg = u := hu hg trivial
    exact hfu.trans hgu.symm
  exact hne this

-- 反例専用：α と β を具体的に固定
example {ι : Type*} [Preorder ι] (someTower : StructureTower ι Bool) :
    ¬ (∃! (_h : TowerHom someTower (constTower ι Bool)), True) := by
  simpa using
    (not_terminal_constTower (ι := ι) (α := Bool) (β := Bool) (T := someTower))

-- ═══════════════════════════════════════════════════════════════════
-- ██  Part 2: Bool 上の具体的反例
-- ██  Concrete counterexample on Bool
-- ═══════════════════════════════════════════════════════════════════

/-!
### 具体的な舞台設定

基礎型 α = Bool, 添字型 ι = ℕ とする。

Bool 上の定値塔 constTower ℕ Bool を考える。
Bool には2元 true, false があり、以下の2つの射を構成できる:

  φ₁ = toConstTower T     （mapFun = id）
  φ₂ = anyMapToConst T f  （mapFun = Bool.not, すなわち ¬）

φ₁.mapFun true  = true
φ₂.mapFun true  = false
よって φ₁ ≠ φ₂。
-/

section BoolCounterexample

/-- Bool 上の自明な構造塔（全レベルが univ）-/
def boolTower : StructureTower ℕ Bool := constTower ℕ Bool

/-!
### 課題 2: 恒等射 — 第1の射の構成

mapFun = id による標準射。
-/

/-- 第1の射: 恒等写像による射 -/
def φ₁ : TowerHom boolTower (constTower ℕ Bool) :=
  toConstTower boolTower

/-!
### 課題 3: 否定射 — 第2の射の構成

mapFun = Bool.not （true ↦ false, false ↦ true）による射。

**方針**: `anyMapToConst` を Bool.not に適用するか、直接構成する。
-/

/-- 第2の射: 否定写像による射 -/
def φ₂ : TowerHom boolTower (constTower ℕ Bool) :=
  anyMapToConst boolTower Bool.not

/-!
### 課題 4: 二つの射が異なることの証明

φ₁.mapFun ≠ φ₂.mapFun を示す。
具体的には、ある点（例えば true）で値が異なることを示せばよい。

集合論的に:
  φ₁.mapFun true = id true = true
  φ₂.mapFun true = Bool.not true = false
  true ≠ false

**方針**: `fun h => ...` で mapFun の等式を仮定し、
`congrFun h true` で点ごとの等式に落として矛盾を導く。
-/

/-- 二つの射の基礎写像は異なる -/
theorem φ₁_ne_φ₂_mapFun : φ₁.mapFun ≠ φ₂.mapFun := by
  intro h
  have htrue : φ₁.mapFun true = φ₂.mapFun true := congrFun h true
  simp [φ₁, φ₂, toConstTower, anyMapToConst] at htrue

/-- 二つの射は射として異なる -/
theorem φ₁_ne_φ₂ : φ₁ ≠ φ₂ := by
  intro h
  exact φ₁_ne_φ₂_mapFun (congrArg (fun k => k.mapFun) h)

end BoolCounterexample

-- ═══════════════════════════════════════════════════════════════════
-- ██  Part 3: 終対象の正しい定式化
-- ██  Correct formulation of the terminal object
-- ═══════════════════════════════════════════════════════════════════

/-!
## 第3節: 真の終対象とは何か

上の反例は「constTower ι α は TowerCat(ι, α → α) の終対象ではない」ことを示した。

では TowerCat に終対象は存在するか？ 答えは **Yes** — ただし基礎型を
`Unit`（一点集合）にする必要がある:

  unitTower : StructureTower ι Unit
  level i = {()}  = Set.univ  （Unit は一点集合なので自動的に univ）

任意の塔 T : StructureTower ι α からの射は一意:
  f.mapFun は α → Unit = fun _ => () しかない。

これは集合の圏における終対象 {*} の構造塔版である。
Bourbaki的に言えば「構造を保存する写像の値域が一点集合であれば、
写像自体が一意に定まる」という原理の具現化。
-/

section TerminalObject

variable {ι α : Type*} [Preorder ι]

/-!
### 課題 5: Unit 上の構造塔（真の終対象候補）
-/

/-- Unit 上の構造塔 -/
def unitTower (ι : Type*) [Preorder ι] : StructureTower ι Unit where
  level := fun _ => Set.univ
  monotone_level := by intro i j _; exact Set.subset_univ _

/-!
### 課題 6: 任意の塔から unitTower への射の存在

mapFun は唯一の写像 fun _ => () である。

**方針**: mapFun := fun _ => (), レベル保存は mem_univ。
-/

/-- unitTower への標準射（存在） -/
def toUnitTower (T : StructureTower ι α) :
    TowerHom T (unitTower ι) where
  mapFun := fun _ => ()
  level_preserving := by
    intro i x hx
    exact Set.mem_univ ()

/-!
### 課題 7: unitTower への射の一意性

任意の射 f : T → unitTower ι は toUnitTower T に等しい。

核心: α → Unit の写像は fun _ => () しかない。
Lean では `Subsingleton (α → Unit)` や `funext` + `Unit.ext` で示せる。

**方針**:
  1. `TowerHom.ext` で基礎写像の等式に帰着
  2. `funext` で各点 x について示す
  3. Unit 型の値は () しかないので両辺が一致
-/

/-- unitTower への射は一意 -/
theorem toUnitTower_unique (T : StructureTower ι α)
    (f : TowerHom T (unitTower ι)) :
    f = toUnitTower T := by
  apply TowerHom.ext
  funext x
  exact Subsingleton.elim _ _

/-!
### 課題 8: 終対象の普遍性（存在と一意性の統合）

∃! を用いた完全な定式化。

**方針**: `⟨toUnitTower T, fun g => (toUnitTower_unique T g).symm⟩` の形。
-/

/-- unitTower は終対象: 任意の塔からの射が一意に存在する
    unitTower is terminal: there exists a unique morphism from any tower -/
theorem unitTower_terminal (T : StructureTower ι α) :
    ∃! (_f : TowerHom T (unitTower ι)), True := by
  refine ⟨toUnitTower T, trivial, ?_⟩
  intro g hg
  exact toUnitTower_unique T g

end TerminalObject

-- ═══════════════════════════════════════════════════════════════════
-- ██  Part 4: 教訓の形式化
-- ██  Formalizing the Lesson
-- ═══════════════════════════════════════════════════════════════════

/-!
## 第4節: constTower と unitTower の対比

| 性質 | constTower ι α | unitTower ι |
|------|---------------|-------------|
| 基礎型 | α（任意） | Unit（一点） |
| レベル | すべて univ | すべて univ |
| 射の存在 | ✓ (任意の f : α → α) | ✓ (唯一の α → Unit) |
| 射の一意性 | ✗ (α に2元以上あれば) | ✓ |
| 終対象か | **No** | **Yes** |

### 教訓 (Bourbaki的視点)

constTower は「各レベルでの制約を完全に緩めた」構造であり、
射の存在は保証するが一意性は失われる。

終対象性は **値域の型** (codomain type) の性質に依存する:
- 値域が一点集合 ⇒ 写像空間が一点 ⇒ 一意性が保証される
- 値域に複数の元 ⇒ 複数の写像が可能 ⇒ 一意性が崩れる

これは集合の圏 Set における終対象 {*} と、
任意の集合 X に対する「X へのsurjection の非一意性」の構造塔版である。

## 発展方向

### 始対象 (Initial Object)
空型 Empty 上の構造塔 emptyTower が始対象をなすことを示せ:
  ∀ T, ∃! (f : TowerHom (emptyTower ι) T), True

### 零対象 (Zero Object)
TowerCat(ι) は零対象（始対象かつ終対象）を持つか？
（ヒント: Unit 上の塔は始対象でもあるか？）

### Mathlibとの接続
`CategoryTheory.Limits.IsTerminal` を用いて unitTower の
終対象性を Mathlib の言葉で登録せよ。
-/

/-- 空型上の構造塔。像判定が自明になるため始対象候補になる。 -/
def emptyTower (ι : Type*) [Preorder ι] : StructureTower ι Empty where
  level := fun _ => Set.univ
  monotone_level := by intro i j _; exact Set.subset_univ _

section InitialObject

variable {ι α : Type*} [Preorder ι]

/-- 任意の塔への標準射 `emptyTower ⟶ T`。空型からの関数は `Empty.elim` で一意。 -/
def fromEmptyTower (T : StructureTower ι α) :
    TowerHom (emptyTower ι) T where
  mapFun := Empty.elim
  level_preserving := by
    intro i x hx
    cases x

/-- `emptyTower` から任意の塔への射は一意。技法: `TowerHom.ext` と `cases x`. -/
theorem fromEmptyTower_unique (T : StructureTower ι α)
    (f : TowerHom (emptyTower ι) T) :
    f = fromEmptyTower T := by
  apply TowerHom.ext
  funext x
  cases x

/-- `emptyTower` は始対象: 任意の `T` への射が一意に存在。 -/
theorem emptyTower_initial (T : StructureTower ι α) :
    ∃! (_f : TowerHom (emptyTower ι) T), True := by
  refine ⟨fromEmptyTower T, trivial, ?_⟩
  intro g _hg
  exact fromEmptyTower_unique T g

end InitialObject

section MathlibConnection

open CategoryTheory
open CategoryTheory.Limits

variable (ι : Type*) [Preorder ι]

/-- `ι` を固定し、基礎型を可変にした構造塔の対象。 -/
structure TowerObj where
  α : Type
  tower : StructureTower ι α

namespace TowerObj

instance : Category (TowerObj ι) where
  Hom X Y := TowerHom X.tower Y.tower
  id X := by
    refine
      { mapFun := _root_.id
        level_preserving := ?_ }
    intro i x hx
    simpa using hx
  comp f g := by
    refine
      { mapFun := g.mapFun ∘ f.mapFun
        level_preserving := ?_ }
    intro i x hx
    exact g.level_preserving i (f.mapFun x) (f.level_preserving i x hx)
  id_comp := by
    intro X Y f
    apply TowerHom.ext
    rfl
  comp_id := by
    intro X Y f
    apply TowerHom.ext
    rfl
  assoc := by
    intro W X Y Z f g h
    apply TowerHom.ext
    rfl

/-- `Unit` を基礎型に持つ対象。`unitTower` の圏論的実体。 -/
def unitObj : TowerObj ι := ⟨Unit, unitTower ι⟩

/-- `Empty` を基礎型に持つ対象。`emptyTower` の圏論的実体。 -/
def emptyObj : TowerObj ι := ⟨Empty, emptyTower ι⟩

/-- `Bool` 上の定値塔対象。始対象性反例に使う。 -/
def boolObj : TowerObj ι := ⟨Bool, constTower ι Bool⟩

/-- `unitObj ⟶ boolObj` の第1射（定値 `true`）。 -/
def unitToBoolTrue : unitObj ι ⟶ boolObj ι where
  mapFun := fun _ => true
  level_preserving := by
    intro i x hx
    exact Set.mem_univ true

/-- `unitObj ⟶ boolObj` の第2射（定値 `false`）。 -/
def unitToBoolFalse : unitObj ι ⟶ boolObj ι where
  mapFun := fun _ => false
  level_preserving := by
    intro i x hx
    exact Set.mem_univ false

/-- `unitObj ⟶ boolObj` の2射は異なる（`()` での値比較）。 -/
theorem unitToBoolTrue_ne_unitToBoolFalse :
    unitToBoolTrue ι ≠ unitToBoolFalse ι := by
  intro h
  have hpoint : (unitToBoolTrue ι).mapFun () = (unitToBoolFalse ι).mapFun () :=
    congrArg (fun k => k.mapFun ()) h
  simp [unitToBoolTrue, unitToBoolFalse] at hpoint

/-- Mathlib形式: `unitObj` は終対象 (`IsTerminal`)。 -/
def unitObj_isTerminal : IsTerminal (unitObj ι) := by
  refine IsTerminal.ofUniqueHom (Y := unitObj ι) ?_ ?_
  · intro X
    exact toUnitTower X.tower
  · intro X f
    exact toUnitTower_unique X.tower f

/-- `unitObj` は始対象ではない。反例は `boolObj` への2本の異なる射。 -/
theorem unitObj_not_initial : ¬ Nonempty (IsInitial (unitObj ι)) := by
  intro hInit
  rcases hInit with ⟨hInit⟩
  have hEq : unitToBoolTrue ι = unitToBoolFalse ι := hInit.hom_ext _ _
  exact unitToBoolTrue_ne_unitToBoolFalse ι hEq

/-- `emptyObj` は始対象 (`IsInitial`)。 -/
def emptyObj_isInitial : IsInitial (emptyObj ι) := by
  refine IsInitial.ofUniqueHom (X := emptyObj ι) ?_ ?_
  · intro Y
    exact fromEmptyTower Y.tower
  · intro Y f
    exact fromEmptyTower_unique Y.tower f

/-- 構造塔圏には零対象（始対象かつ終対象）は存在しない。 -/
theorem no_zero_object :
    ¬ ∃ Z : TowerObj ι, Nonempty (IsInitial Z) ∧ Nonempty (IsTerminal Z) := by
  intro h
  rcases h with ⟨Z, ⟨hInit⟩, ⟨hTerm⟩⟩
  let f : unitObj ι ⟶ Z := hTerm.from (unitObj ι)
  let g : Z ⟶ emptyObj ι := hInit.to (emptyObj ι)
  have hEmpty : Empty := (f ≫ g).mapFun ()
  exact Empty.elim hEmpty

end TowerObj

end MathlibConnection

end BourbakiLeanGuide
