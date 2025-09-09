-- Suspension–loop scaffold in ContinuousMap-land (apply-only, pointwise `@[simp]`).
-- No TopCat mixing; rfl/ext proofs; snapshot-tolerant.

import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.CompactOpen

noncomputable section

open scoped Topology

namespace MyProjects.Topology.B

/-! # Based spaces and based maps (thin wrappers) -/

structure Based (X : Type*) [TopologicalSpace X] : Type* where
  base : X

@[simp] theorem Based.base_coe {X} [TopologicalSpace X] (B : Based X) : B.base = B.base := rfl

/-- Build a based space from a point. -/
def Based.of {X : Type*} [TopologicalSpace X] (x0 : X) : Based X := ⟨x0⟩

/-- Based maps `A ⟶₍*₎ B` as continuous maps preserving basepoints. -/
def BasedMap {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
  (BA : Based A) (BB : Based B) : Type* :=
  { f : C(A, B) // f BA.base = BB.base }

/-! # Generic segment with endpoints -/

structure Segment (I : Type*) [TopologicalSpace I] [LocallyCompactSpace I] : Type* where
  left  : I
  right : I

/-! # Loop space Ω (as endpoint-constrained maps) -/

def Loop {I Y : Type*} [TopologicalSpace I] [LocallyCompactSpace I]
  [TopologicalSpace Y]
  (Seg : Segment I) (B : Based Y) : Type* :=
  { γ : C(I, Y) // γ Seg.left = B.base ∧ γ Seg.right = B.base }

namespace Loop

variable {I A Y : Type*}
variable [TopologicalSpace I] [LocallyCompactSpace I]
variable [TopologicalSpace A] [TopologicalSpace Y]

@[simp] lemma coe_left {Seg : Segment I} {B : Based Y}
  (γ : Loop (Seg:=Seg) (B:=B)) : (γ.1) Seg.left = B.base := γ.2.1

@[simp] lemma coe_right {Seg : Segment I} {B : Based Y}
  (γ : Loop (Seg:=Seg) (B:=B)) : (γ.1) Seg.right = B.base := γ.2.2

end Loop

/-! # Cylinder-level maps with endpoint conditions -/

def CylinderMap {I A Y : Type*}
  [TopologicalSpace I] [LocallyCompactSpace I]
  [TopologicalSpace A] [TopologicalSpace Y]
  (Seg : Segment I) (B : Based Y) : Type* :=
  { f : C(A × I, Y) // ∀ a : A, f (a, Seg.left) = B.base ∧ f (a, Seg.right) = B.base }

/-! # Curry/uncurry skeleton between cylinder maps and loops -/

variable {I A Y : Type*}
variable [TopologicalSpace I] [LocallyCompactSpace I]
variable [TopologicalSpace A] [TopologicalSpace Y]

/-- Curry: `C(A×I, Y)` with endpoint conditions → `C(A, ΩSeg B)` -/
def curryToLoop (Seg : Segment I) (B : Based Y)
  (F : CylinderMap (Seg:=Seg) (B:=B) (A:=A) (I:=I) (Y:=Y)) :
  C(A, Loop (Seg:=Seg) (B:=B)) := by
  -- underlying `C(A, C(I, Y))`
  let g : C(A, C(I, Y)) := ContinuousMap.curry F.1
  -- build into the subtype by endpoint constraints
  refine ⟨(fun a => ⟨g a, ?h₁ a, ?h₂ a⟩), ?hc⟩
  · intro a; simpa using (F.2 a).1
  · intro a; simpa using (F.2 a).2
  · -- continuity into the subtype
    have hprop : ∀ a, (g a) Seg.left = B.base ∧ (g a) Seg.right = B.base := by
      intro a; exact And.intro (by simpa using (F.2 a).1) (by simpa using (F.2 a).2)
    exact Continuous.subtype_mk g.continuous hprop

/-- Uncurry: `C(A, ΩSeg B)` → `C(A×I, Y)` -/
def uncurryFromLoop (Seg : Segment I) (B : Based Y)
  (h : C(A, Loop (Seg:=Seg) (B:=B))) :
  C(A × I, Y) := by
  -- underlying `C(A, C(I, Y))` by forgetting subtype
  let g : C(A, C(I, Y)) := ⟨fun a => (h a).1, by
    -- continuity follows from `h.continuous` and evaluation into subtype
    simpa using h.continuous⟩
  exact ContinuousMap.uncurry g

/-! # Pointwise β/η identities (triangles) -/

@[simp] lemma uncurry_curry_pointwise (Seg : Segment I) (B : Based Y)
  (F : CylinderMap (Seg:=Seg) (B:=B) (A:=A) (I:=I) (Y:=Y)) :
  uncurryFromLoop (Seg:=Seg) (B:=B) (curryToLoop (Seg:=Seg) (B:=B) F) = F.1 := by
  ext a t; rfl

@[simp] lemma curry_uncurry_pointwise (Seg : Segment I) (B : Based Y)
  (h : C(A, Loop (Seg:=Seg) (B:=B))) :
  curryToLoop (Seg:=Seg) (B:=B)
    ⟨uncurryFromLoop (Seg:=Seg) (B:=B) h, fun a =>
        And.intro (by simpa using Loop.coe_left (h a)) (by simpa using Loop.coe_right (h a))⟩
  = h := by
  ext a; -- equality in the subtype by underlying functions
  -- compare underlying continuous maps `I → Y`
  change (ContinuousMap.curry (uncurryFromLoop (Seg:=Seg) (B:=B) h)) a = (h a).1
  -- `curry ∘ uncurry` acts as identity pointwise
  ext t; rfl

/-! # Suspension setup interface (skeletal) -/

structure SuspensionSetup {I Y : Type*}
  [TopologicalSpace I] [LocallyCompactSpace I]
  [TopologicalSpace Y]
  (Seg : Segment I) (B : Based Y) : Type* where
  S : Type*
  [tS : TopologicalSpace S]
  baseS : S
  coev : C(Y × I, S)
  coev_left  : ∀ y : Y, coev (y, Seg.left) = baseS
  coev_right : ∀ y : Y, coev (y, Seg.right) = baseS

attribute [instance] SuspensionSetup.tS

/-- Unit (coevaluation): `Y ⟶ Ω Seg (S)` obtained by currying `coev`. -/
def SuspensionSetup.unit
  {I Y : Type*} [TopologicalSpace I] [LocallyCompactSpace I]
  [TopologicalSpace Y]
  {Seg : Segment I} {B : Based Y}
  (setup : SuspensionSetup (Seg:=Seg) (B:=B)) :
  C(Y, Loop (Seg:=Seg) (B:=(Based.of setup.baseS))) := by
  -- package `coev` as a cylinder map in the A := Y slot
  let cyl : CylinderMap (Seg:=Seg) (B:=(Based.of setup.baseS)) (A:=Y) (I:=I) (Y:=setup.S) :=
    ⟨setup.coev, fun y => And.intro (setup.coev_left y) (setup.coev_right y)⟩
  -- curry into loops
  simpa using curryToLoop (I:=I) (A:=Y) (Y:=setup.S) (Seg:=Seg)
    (B:=(Based.of setup.baseS)) cyl

end MyProjects.Topology.B
