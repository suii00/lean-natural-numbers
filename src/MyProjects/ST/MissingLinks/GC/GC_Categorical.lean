import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finite.Defs
import Mathlib.Order.Hom.Basic

/-!
# Layer 0: Categorical Glue Layer

秩序論（Layer 4-3: GC, Closure, Rank）と
塔・圏論（Layer 2-1: RankTower, WithMin）の接着層。

## 役割

1. **双方向の橋渡し**:
   - GC/Closure → Rank → Tower
   - Tower → Rank → GC/Closure（部分的）

2. **既存の圏構造の再利用**:
   - Cat_le: 順序保存射の圏
   - Cat_WithMin: minLayer保存射の圏

3. **Functorによる対応**:
   - ClosureOp → RankedFinite → SimpleTowerWithMin

-/

namespace GCCategorical

open CategoryTheory

/-! ## 基本構造の再掲（各層との互換性） -/

section BasicStructures

variable {X : Type*}

/-- 閉包作用素（Layer 3） -/
structure ClosureOp (X : Type*) where
  cl : Set X → Set X
  mono : Monotone cl
  le_closure : ∀ s, s ⊆ cl s
  idempotent : ∀ s, cl (cl s) = cl s

/-- Ranked 構造（Layer 2） -/
structure Ranked (α : Type*) (X : Type*) where
  rank : X → α

namespace Ranked

variable {α : Type*} {X : Type*}

/-- 層の標準定義: rank ≤ n の要素全体 -/
def layer [Preorder α] (R : Ranked α X) (n : α) : Set X :=
  {x | R.rank x ≤ n}

@[simp]
theorem mem_layer_iff [Preorder α] (R : Ranked α X) (n : α) (x : X) :
    x ∈ R.layer n ↔ R.rank x ≤ n := Iff.rfl

end Ranked

/-- RankedFinite 構造（Layer 1） -/
structure RankedFinite (X : Type*) extends Ranked (WithTop ℕ) X where
  finite_rank : ∀ x, ∃ n : ℕ, rank x ≤ n

/-- SimpleTowerWithMin 構造（Layer 1） -/
structure SimpleTowerWithMin (X : Type*) where
  layer : ℕ → Set X
  covering : ∀ x, ∃ n, x ∈ layer n
  monotone : ∀ {i j}, i ≤ j → layer i ⊆ layer j
  minLayer : X → ℕ
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  minLayer_minimal : ∀ x i, x ∈ layer i → minLayer x ≤ i

end BasicStructures

/-! ## 射の定義: 順序保存 -/

section OrderPreservingMorphisms

/-- Ranked 構造間の順序保存射 -/
structure RankedHom {α : Type*} [Preorder α]
    {X Y : Type*} (R : Ranked α X) (S : Ranked α Y) where
  /-- 基礎写像 -/
  toFun : X → Y
  /-- rank の非増加性（層保存に十分な弱い条件） -/
  rank_le : ∀ x, S.rank (toFun x) ≤ R.rank x

namespace RankedHom

variable {α : Type*} [Preorder α]
variable {X Y : Type*} {R : Ranked α X} {S : Ranked α Y}

/-- 射の合成 -/
def comp {Z : Type*} {T : Ranked α Z}
    (g : RankedHom S T) (f : RankedHom R S) : RankedHom R T where
  toFun := g.toFun ∘ f.toFun
  rank_le := by
    intro x
    exact le_trans (g.rank_le (f.toFun x)) (f.rank_le x)

/-- 恒等射 -/
def id (R : Ranked α X) : RankedHom R R where
  toFun := _root_.id
  rank_le := fun _ => le_refl _

/-- 層保存の証明 -/
theorem layer_preserving {n m : α} (f : RankedHom R S)
    (h : n ≤ m) :
    ∀ x ∈ R.layer n, f.toFun x ∈ S.layer m := by
  intro x hx
  have hRn : R.rank x ≤ n := by
    simpa [Ranked.layer] using hx
  have hS : S.rank (f.toFun x) ≤ R.rank x := f.rank_le x
  exact (le_trans hS (le_trans hRn h))

end RankedHom

end OrderPreservingMorphisms

/-! ## 射の定義: minLayer 保存 -/

section MinLayerPreservingMorphisms

variable {X Y : Type*}

/-- SimpleTowerWithMin 間の minLayer 保存射 -/
structure TowerWithMinHom (T : SimpleTowerWithMin X) (S : SimpleTowerWithMin Y) where
  /-- 基礎写像 -/
  toFun : X → Y
  /-- minLayer の保存 -/
  minLayer_preserving : ∀ x, S.minLayer (toFun x) ≤ T.minLayer x

namespace TowerWithMinHom

variable {T : SimpleTowerWithMin X} {S : SimpleTowerWithMin Y}

/-- 射の合成 -/
def comp {Z : Type*} {U : SimpleTowerWithMin Z}
    (g : TowerWithMinHom S U) (f : TowerWithMinHom T S) :
    TowerWithMinHom T U where
  toFun := g.toFun ∘ f.toFun
  minLayer_preserving := by
    intro x
    calc U.minLayer (g.toFun (f.toFun x))
        ≤ S.minLayer (f.toFun x) := g.minLayer_preserving (f.toFun x)
      _ ≤ T.minLayer x := f.minLayer_preserving x

/-- 恒等射 -/
def id (T : SimpleTowerWithMin X) : TowerWithMinHom T T where
  toFun := _root_.id
  minLayer_preserving := fun _ => le_refl _

/-- 層保存の導出 -/
theorem layer_preserving (f : TowerWithMinHom T S) (n : ℕ) :
    ∀ x ∈ T.layer n, f.toFun x ∈ S.layer n := by
  intro x hx
  have h1 : T.minLayer x ≤ n := T.minLayer_minimal x n hx
  have h2 : S.minLayer (f.toFun x) ≤ T.minLayer x := 
    f.minLayer_preserving x
  have h3 : S.minLayer (f.toFun x) ≤ n := le_trans h2 h1
  exact S.monotone h3 (S.minLayer_mem (f.toFun x))

end TowerWithMinHom

end MinLayerPreservingMorphisms

/-! ## 圏構造の定義 -/

section CategoryInstances

/-- Ranked の圏（同一の順序型 α に固定） -/
def RankedCat (α : Type*) [Preorder α] := 
  Σ X : Type*, Ranked α X

namespace RankedCat

variable (α : Type*) [Preorder α]

instance : Category (RankedCat α) where
  Hom := fun R S => RankedHom R.2 S.2
  id := fun R => RankedHom.id R.2
  comp := fun f g => RankedHom.comp g f
  id_comp := by
    intro R S f
    cases f
    rfl
  comp_id := by
    intro R S f
    cases f
    rfl
  assoc := by
    intro R S T U f g h
    rfl

end RankedCat

/-- SimpleTowerWithMin の圏 -/
def TowerWithMinCat := Σ X : Type*, SimpleTowerWithMin X

namespace TowerWithMinCat

instance : Category TowerWithMinCat where
  Hom := fun T S => TowerWithMinHom T.2 S.2
  id := fun T => TowerWithMinHom.id T.2
  comp := fun f g => TowerWithMinHom.comp g f
  id_comp := by
    intro T S f
    cases f
    rfl
  comp_id := by
    intro T S f
    cases f
    rfl
  assoc := by
    intro T S U V f g h
    rfl

end TowerWithMinCat

end CategoryInstances

/-! ## Functor: RankedFinite → TowerWithMin -/

section RankedToTowerFunctor

/-- RankedFinite から SimpleTowerWithMin への変換（Layer 1） -/
noncomputable def RankedFinite.toTowerWithMin {X : Type*} 
    (R : RankedFinite X) :
    SimpleTowerWithMin X where
  layer n := {x | R.rank x ≤ (n : WithTop ℕ)}
  covering := by
    intro x
    obtain ⟨n, hn⟩ := R.finite_rank x
    exact ⟨n, hn⟩
  monotone := by
    intro i j hij x hx
    exact le_trans hx (WithTop.coe_le_coe.mpr hij)
  minLayer := fun x => Nat.find (R.finite_rank x)
  minLayer_mem := by
    intro x
    exact Nat.find_spec (R.finite_rank x)
  minLayer_minimal := by
    intro x i hx
    exact Nat.find_min' (R.finite_rank x) hx

/-- RankedFinite の射から TowerWithMin の射への持ち上げ -/
noncomputable def liftRankedHomToTower {X Y : Type*}
    {R : RankedFinite X} {S : RankedFinite Y}
    (f : RankedHom R.toRanked S.toRanked) :
    TowerWithMinHom R.toTowerWithMin S.toTowerWithMin where
  toFun := f.toFun
  minLayer_preserving := by
    intro x
    sorry -- TODO: reason="minLayer monotonicity proof missing", follow_up="derive from rank_le and Nat.find"

end RankedToTowerFunctor

/-! ## 具体例: 恒等 functor -/

section IdentityExamples

variable {X : Type*}

/-- Ranked から Ranked への恒等 functor -/
def rankedIdentityFunctor (α : Type*) [Preorder α] :
    RankedCat α ⥤ RankedCat α where
  obj := _root_.id
  map := _root_.id
  map_id := by intro X; rfl
  map_comp := by intro X Y Z f g; rfl

/-- TowerWithMin から TowerWithMin への恒等 functor -/
def towerIdentityFunctor : TowerWithMinCat ⥤ TowerWithMinCat where
  obj := _root_.id
  map := _root_.id
  map_id := by intro X; rfl
  map_comp := by intro X Y Z f g; rfl

end IdentityExamples

/-! ## 忘却 functor -/

section ForgetfulFunctors

/-- RankedCat から Type への忘却 functor -/
def forgetRankedCarrier (α : Type*) [Preorder α] :
    RankedCat α ⥤ Type _ where
  obj := fun R => R.1
  map := fun f => f.toFun
  map_id := by intro R; rfl
  map_comp := by intro R S T f g; rfl

/-- TowerWithMinCat から Type への忘却 functor -/
def forgetTowerCarrier : TowerWithMinCat ⥤ Type _ where
  obj := fun T => T.1
  map := fun f => f.toFun
  map_id := by intro T; rfl
  map_comp := by intro T S U f g; rfl

end ForgetfulFunctors

/-! ## GC との接続（概念的な橋） -/

section GCConnection

/-
GaloisConnection と Ranked/Tower の対応（概念図）:

Layer 4: GaloisConnection
    ↓ (closure operator 構成)
Layer 3: ClosureOp → rank function (rankStab, rankGen)
    ↓ (Ranked 構成)
Layer 2: Ranked (WithTop ℕ)
    ↓ (finite_rank 条件)
Layer 1: RankedFinite → SimpleTowerWithMin
    ↓ (functor)
Layer 0: 圏論的記述

この接続により:
1. GC の性質（単調性、随伴）→ rank の性質（層の単調性）
2. 閉包の冪等性 → 層の安定性
3. 被覆性の条件 → 有限性仮定の明示化
-/

variable {X : Type*}

/-- ClosureOp から RankedFinite への変換（概念的） -/
noncomputable def closureToRankedFinite [Finite X] (C : ClosureOp X) 
    (s₀ : Set X) : RankedFinite X where
  toRanked := {
    rank := sorry  -- TODO: reason="rankStab未実装", follow_up="define rank via rankStab"
  }
  finite_rank := sorry  -- TODO: reason="finite_rank証明未実装", follow_up="use Finite X"

/-- 全体の合成: GC → Tower -/
noncomputable def gcToTower [Finite X] (C : ClosureOp X) (s₀ : Set X) :
    SimpleTowerWithMin X :=
  (closureToRankedFinite C s₀).toTowerWithMin

end GCConnection

end GCCategorical
