import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Closure
import Mathlib.Data.Set.Lattice
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Topology.Sets.Closeds

/-!
# Layer 4: Galois Connection → Closure Operator

Galois接続（随伴）から閉包作用素を導出する理論的基礎。

## 主要構成

1. **設計案A**: 同一束上のGC (Gen: β → α, Cl: α → β, Cl ⊣ Gen)
2. **設計案B**: `Set X` と閉集合型 `C` のGC（`C` は `SetLike` + `CompleteLattice`）

## 核心定理

GaloisConnection ⇒ ClosureOperator への導出
- Monotone (単調性)
- Extensivity (拡大性: s ⊆ cl s)
- Idempotency (冪等性: cl ∘ cl = cl)

## 小例

```lean
example {α β : Type*} [CompleteLattice α] [CompleteLattice β]
    (G : GaloisClosure.GCClosureA α β) (x : α) :
    G.closure (G.closure x) = G.closure x :=
  G.closure_idempotent x
```
-/

namespace GaloisClosure

/-! ## 設計案A: 同一束上のGalois接続 -/

section SameLattice

variable {α β : Type*} [CompleteLattice α] [CompleteLattice β]

/-- 設計案A: Gen と Cl が随伴を成す場合の閉包作用素 -/
structure GCClosureA (α β : Type*) [CompleteLattice α] [CompleteLattice β] where
  /-- 生成関数: β → α -/
  Gen : β → α
  /-- 閉包関数: α → β -/
  Cl : α → β
  /-- Galois接続: Cl ⊣ Gen -/
  gc : GaloisConnection Cl Gen

namespace GCClosureA

variable (G : GCClosureA α β)

/-- 閉包作用素: α → α を Gen ∘ Cl として定義 -/
def closure : α → α := G.Gen ∘ G.Cl

/-- 双対閉包: β → β を Cl ∘ Gen として定義 -/
def coclosure : β → β := G.Cl ∘ G.Gen

/-! ### 3つの基本性質の導出 -/

/-- (1) 単調性: GC から直接従う -/
theorem closure_mono : Monotone G.closure := by
  intro x y hxy
  unfold closure
  simp only [Function.comp_apply]
  exact G.gc.monotone_u (G.gc.monotone_l hxy)

/-- (2) 拡大性: x ≤ Gen (Cl x) -/
theorem closure_le_self (x : α) : x ≤ G.closure x := by
  unfold closure
  simp only [Function.comp_apply]
  exact G.gc.le_u_l x

/-- (3) 冪等性: Gen (Cl (Gen (Cl x))) = Gen (Cl x) -/
theorem closure_idempotent (x : α) : G.closure (G.closure x) = G.closure x := by
  simpa [closure, Function.comp_apply] using
    (G.gc.u_l_u_eq_u (b := G.Cl x))

/-- 双対閉包の単調性 -/
theorem coclosure_mono : Monotone G.coclosure := by
  intro x y hxy
  unfold coclosure
  simp only [Function.comp_apply]
  exact G.gc.monotone_l (G.gc.monotone_u hxy)

/-- 双対閉包の縮小性: Cl (Gen x) ≤ x -/
theorem self_le_coclosure (x : β) : G.coclosure x ≤ x := by
  unfold coclosure
  simp only [Function.comp_apply]
  exact G.gc.l_u_le x

/-- 簡単な動作確認 -/
example (x : α) : G.closure (G.closure x) = G.closure x := by
  simpa using G.closure_idempotent x

end GCClosureA

end SameLattice

/-! ## 設計案B: Set X と閉集合束のGC -/

section SetClosed

variable {X : Type*} {C : Type*} [CompleteLattice C] [SetLike C X]

/-- 設計案B: Set X と閉集合型 C の間のGC -/
structure GCClosureB (X : Type*) (C : Type*) [CompleteLattice C] [SetLike C X] where
  /-- 生成関数: Set X → C（包含による最小閉集合） -/
  genClosed : Set X → C
  /-- 随伴性: genClosed ⊣ (↑) -/
  gc : GaloisConnection genClosed (fun c => (c : Set X))

namespace GCClosureB

variable {X C : Type*} [CompleteLattice C] [SetLike C X] (G : GCClosureB X C)

/-- Set X 上の閉包作用素 -/
def setClosure : Set X → Set X := fun s => (G.genClosed s : Set X)

/-- 閉包の単調性 -/
theorem setClosure_mono : Monotone G.setClosure := by
  intro s t hst
  exact G.gc.monotone_u (G.gc.monotone_l hst)

/-- 閉包の拡大性 -/
theorem subset_setClosure (s : Set X) : s ⊆ G.setClosure s := by
  simpa [setClosure] using (G.gc.le_u_l s)

/-- 閉包の冪等性 -/
theorem setClosure_idempotent (s : Set X) :
    G.setClosure (G.setClosure s) = G.setClosure s := by
  simpa [setClosure] using (G.gc.u_l_u_eq_u (b := G.genClosed s))

/-- 簡単な動作確認 -/
example (s : Set X) : s ⊆ G.setClosure s := G.subset_setClosure s

end GCClosureB

end SetClosed

/-! ## 具体例: 線形包 (Span) -/

section LinearSpan

variable {K : Type*} [Semiring K] {V : Type*} [AddCommMonoid V] [Module K V]

/-- 線形包による閉包作用素の例（閉集合型は `Submodule K V`）。 -/
def spanClosure : GCClosureB V (Submodule K V) where
  genClosed := Submodule.span K
  gc := (Submodule.gi K V).gc

end LinearSpan

/-! ## 具体例: 位相的閉包 -/

section TopologicalClosure

variable {X : Type*} [TopologicalSpace X]

/-- 位相的閉包による閉包作用素の例（閉集合型は `TopologicalSpace.Closeds X`）。 -/
def topologicalClosure : GCClosureB X (TopologicalSpace.Closeds X) where
  genClosed := TopologicalSpace.Closeds.closure
  gc := TopologicalSpace.Closeds.gc

end TopologicalClosure

end GaloisClosure
