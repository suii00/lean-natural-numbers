/-
# Set-Theoretic Exercises in the Spirit of Bourbaki

This module collects elementary order-, algebra-, and topology-flavoured lemmas
motivated by Bourbaki's *Éléments de mathématique*.  Each section restates a
classical fact in Lean and gives a short example demonstrating its use:

* `preorder_transitivity` rephrases the transitivity axiom of a preorder.
* `supremum_unique` and `sSup_unique` establish the uniqueness of least upper bounds.
* `lattice_subdistributive` and its companions record distributive laws in lattices.
* `imageSubgroup` packages the image of a group homomorphism as a subgroup and
  supplies basic membership facts.
* `compact_is_closed` shows that compact subsets of Hausdorff spaces are closed,
  while `exists_open_nhds_disjoint_of_not_mem_compact` separates a point from a
  compact set.
* `compact_prod`, `compact_pi_finite`, and `compact_prod3` revisit finite products
  of compact spaces.
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Lattice
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Hausdorff

open Set

section Preorder

variable {E : Type*} [Preorder E]

/-- Transitivity for a preorder, restated explicitly. -/
theorem preorder_transitivity (x y z : E)
    (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z :=
  le_trans h₁ h₂

example : (2 : ℕ) ≤ 4 := by
  have h₁ : (2 : ℕ) ≤ 3 := by decide
  have h₂ : (3 : ℕ) ≤ 4 := by decide
  exact preorder_transitivity (x := 2) (y := 3) (z := 4) h₁ h₂

end Preorder

section PartialOrder

variable {E : Type*} [PartialOrder E]

/-- Least upper bounds are unique in a partial order. -/
theorem supremum_unique {A : Set E} {s s' : E}
    (hs : IsLUB A s) (hs' : IsLUB A s') : s = s' :=
  hs.unique hs'

/-- A formulation using the defining universal property of a least upper bound. -/
theorem sSup_unique {A : Set E} {s s' : E}
    (h₁ : ∀ a ∈ A, a ≤ s) (h₂ : ∀ x, (∀ a ∈ A, a ≤ x) → s ≤ x)
    (h₁' : ∀ a ∈ A, a ≤ s') (h₂' : ∀ x, (∀ a ∈ A, a ≤ x) → s' ≤ x) :
    s = s' :=
  le_antisymm (h₂ _ h₁') (h₂' _ h₁)

example :
    1 = 1 := by
  classical
  -- `A` consists of natural numbers bounded by `1`, so `1` is the least upper bound.
  have h :=
    sSup_unique (A := { n : ℕ | n ≤ 1 }) (s := 1) (s' := 1)
      (by intro a ha; exact ha)
      (by intro x hx; exact hx 1 (by decide))
      (by intro a ha; exact ha)
      (by intro x hx; exact hx 1 (by decide))
  simpa using h

end PartialOrder

section Lattice

variable {L : Type*} [Lattice L]

/-- A subdistributive inequality valid in any lattice. -/
theorem lattice_subdistributive (x y z : L) :
    (x ⊓ y) ⊔ (x ⊓ z) ≤ x ⊓ (y ⊔ z) := by
  refine sup_le ?_ ?_
  · exact le_inf inf_le_left ((inf_le_right).trans le_sup_left)
  · exact le_inf inf_le_left ((inf_le_right).trans le_sup_right)

example : ((2 : ℕ) ⊓ 3) ⊔ ((2 : ℕ) ⊓ 4) ≤ 2 ⊓ (3 ⊔ 4) := by
  simpa using lattice_subdistributive (L := ℕ) 2 3 4

end Lattice

section DistribLattice

variable {L : Type*} [DistribLattice L]

/-- Distributivity of infimum over supremum in a distributive lattice. -/
theorem distributive_law (x y z : L) :
    x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := by
  classical
  convert (inf_sup_left (a := x) (b := y) (c := z))

/-- The corresponding distributivity of supremum over infimum. -/
theorem distributive_law_sup (x y z : L) :
    x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z) := by
  classical
  convert (sup_inf_left (a := x) (b := y) (c := z))

example :
    (2 : ℕ) ⊓ (3 ⊔ 4) = ((2 : ℕ) ⊓ 3) ⊔ ((2 : ℕ) ⊓ 4) := by
  simpa using distributive_law (L := ℕ) (x := (2 : ℕ)) (y := 3) (z := 4)

end DistribLattice

section Group

variable {G H : Type*} [Group G] [Group H]
/-- The image of a group homomorphism forms a subgroup of the codomain. -/
def imageSubgroup (f : G →* H) : Subgroup H :=
  f.range

@[simp] lemma coe_imageSubgroup (f : G →* H) :
    (imageSubgroup f : Set H) = Set.range f :=
  rfl

lemma one_mem_image (f : G →* H) : (1 : H) ∈ Set.range f := by
  refine ⟨1, ?_⟩
  simpa using f.map_one

lemma inv_mem_image (f : G →* H) {h : H} (hh : h ∈ Set.range f) :
    h⁻¹ ∈ Set.range f := by
  rcases hh with ⟨g, rfl⟩
  refine ⟨g⁻¹, ?_⟩
  simpa using f.map_inv g

lemma mul_mem_image (f : G →* H) {h₁ h₂ : H}
    (hh₁ : h₁ ∈ Set.range f) (hh₂ : h₂ ∈ Set.range f) :
    h₁ * h₂ ∈ Set.range f := by
  rcases hh₁ with ⟨g₁, rfl⟩
  rcases hh₂ with ⟨g₂, rfl⟩
  refine ⟨g₁ * g₂, ?_⟩
  simpa using f.map_mul g₁ g₂

example :
    (1 : ℤ) ∈ Set.range (MonoidHom.id ℤ : ℤ →* ℤ) := by
  refine ⟨1, ?_⟩
  simp

end Group

section Topology

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- Compact subsets of a Hausdorff space are closed. -/
theorem compact_is_closed {K : Set X} (hK : IsCompact K) :
    IsClosed K :=
  hK.isClosed

/-- The same statement expressed via open complements. -/
theorem isCompact_isClosed {K : Set X} (h : IsCompact K) :
    IsClosed K := by
  rw [← isOpen_compl_iff]
  exact (h.isClosed.isOpen_compl)

/-- A point outside a compact set admits an open neighbourhood disjoint from
that of the compact set. -/
theorem exists_open_nhds_disjoint_of_not_mem_compact
    {x : X} {K : Set X} (hK : IsCompact K) (hx : x ∉ K) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧
      x ∈ U ∧ K ⊆ V ∧ Disjoint U V := by
  obtain ⟨V, U, hVopen, hUopen, hKV, hxU, hdisj⟩ :=
    hK.separation_of_notMem hx
  refine ⟨U, V, hUopen, hVopen, hxU, hKV, hdisj.symm⟩

example :
    IsClosed (Set.Icc (0 : ℝ) 1) :=
  compact_is_closed (X := ℝ) (K := Set.Icc (0 : ℝ) 1) isCompact_Icc

end Topology

section FiniteProducts

/-- The product of compact sets in a product space is compact. -/
theorem compact_prod {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {K : Set X} {L : Set Y}
    (hK : IsCompact K) (hL : IsCompact L) :
    IsCompact (K ×ˢ L) :=
  hK.prod hL

/-- Finite (indeed arbitrary) products of compact sets are compact. -/
theorem compact_pi_finite {ι : Type*} {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] {K : ∀ i, Set (X i)}
    (hK : ∀ i, IsCompact (K i)) :
    IsCompact (Set.pi Set.univ K) :=
  isCompact_univ_pi hK

/-- A triple product of compact spaces is compact. -/
theorem compact_prod3 {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (hX : CompactSpace X) (hY : CompactSpace Y) (hZ : CompactSpace Z) :
    CompactSpace (X × Y × Z) := by
  classical
  exact inferInstance

example :
    IsCompact ((Set.Icc (0 : ℝ) 1) ×ˢ (Set.Icc (0 : ℝ) 1)) :=
  compact_prod (K := Set.Icc (0 : ℝ) 1) (L := Set.Icc (0 : ℝ) 1)
    isCompact_Icc isCompact_Icc

end FiniteProducts
