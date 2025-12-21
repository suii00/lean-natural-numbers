import Mathlib.Topology.Basic
import MyProjects.ST.RankCore.Basic

/-!
# OpenSetTower (A4 skeleton)

A computable "open-set tower" variant by *syntax* (finite unions of basic opens).

Instead of ranking *all* open sets (which tends to require `Nat.find` / noncomputable minimality),
we represent an open set by a `Finset` of basis indices, interpreted as a finite union.

Carrier: `Finset ι`
Evaluation: `U(s) = ⋃ i ∈ s, b i`
Rank: `s.card`

This keeps the example lightweight and stable; you can later connect it to your existing
`openSetTower` assets by exhibiting a basis and an interpretation map.
-/

namespace ST

universe u v

namespace OpenSetTower

variable {X : Type u} [TopologicalSpace X]
variable {ι : Type v}

/-- A family of basic open sets. -/
structure BasicOpenFamily where
  b : ι → Set X
  isOpen_b : ∀ i, IsOpen (b i)

variable (B : BasicOpenFamily (X := X) (ι := ι))

/-- Finite-union expressions of basic opens. -/
abbrev OpenExpr : Type (max u v) := Finset ι

/-- Interpret an expression as an open set (a union over the chosen basis). -/
def eval (s : OpenExpr (ι := ι)) : Set X :=
  ⋃ i, ⋃ (_ : i ∈ s), B.b i

lemma isOpen_eval (s : OpenExpr (ι := ι)) : IsOpen (eval (B := B) s) := by
  classical
  -- Union of open sets is open (even infinite unions); membership-index union is harmless.
  refine isOpen_iUnion ?_
  intro i
  refine isOpen_iUnion ?_
  intro hi
  simpa using B.isOpen_b i

/-- Ranked structure on `OpenExpr`: rank = number of basis pieces. -/
def openExprRanked : Ranked Nat (OpenExpr (ι := ι)) where
  rank := fun s => s.card

@[simp] lemma rank_def (s : OpenExpr (ι := ι)) :
    (openExprRanked (ι := ι)).rank s = s.card := rfl

end OpenSetTower

end ST
