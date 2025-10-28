/-
# Extended Set-Theoretic Exercises in the Spirit of Bourbaki

This module extends P1.lean with additional Bourbaki-inspired exercises covering:
* Order-theoretic constructions (Galois connections, closure operators)
* Algebraic structures (quotient groups, normal subgroups)
* Topological properties (connectedness, continuity)
* Categorical perspectives (universal properties, adjunctions)

These exercises emphasize the structural and functorial viewpoint characteristic
of Bourbaki's approach to mathematics.
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.ModularLattice
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.CategoryTheory.Functor.Basic
import MyProjects.Set.Bourbaki_Lean_Guide

open Set Function

-- ============================================================================
-- Section 1: Galois Connections (Order Theory)
-- ============================================================================
section GaloisConnection

variable {α β : Type*} [Preorder α] [Preorder β]

/-- A Galois connection between posets α and β consists of monotone maps
    satisfying l(a) ≤ b ↔ a ≤ u(b) for all a ∈ α, b ∈ β.
    This is a fundamental concept in Bourbaki's treatment of order structures. -/
theorem galois_connection_composition
    {γ : Type*} [Preorder γ]
    {l₁ : α → β} {u₁ : β → α} (gc₁ : GaloisConnection l₁ u₁)
    {l₂ : β → γ} {u₂ : γ → β} (gc₂ : GaloisConnection l₂ u₂) :
    GaloisConnection (l₂ ∘ l₁) (u₁ ∘ u₂) := by
  intro a c
  change l₂ (l₁ a) ≤ c ↔ a ≤ u₁ (u₂ c)
  exact (gc₂ (a := l₁ a) (b := c)).trans (gc₁ (a := a) (b := u₂ c))

/-- The lower adjoint in a Galois connection preserves suprema. -/
theorem galois_lower_preserves_sup
    {l : α → β} {u : β → α} (gc : GaloisConnection l u)
    {s : Set α} {a : α} (ha : IsLUB s a) :
    IsLUB (l '' s) (l a) := by
  classical
  constructor
  · intro b hb
    rcases hb with ⟨a', ha', rfl⟩
    exact gc.monotone_l (ha.1 ha')
  · intro b hb
    have h₁ : a ≤ u b := by
      apply ha.2
      intro a' ha'
      have : l a' ≤ b := hb ⟨a', ha', rfl⟩
      exact (gc (a := a') (b := b)).mp this
    exact (gc (a := a) (b := b)).mpr h₁

/-- Example: Power set and image form a Galois connection -/
example {X Y : Type*} (f : X → Y) :
    GaloisConnection (fun (A : Set X) => f '' A) (fun (B : Set Y) => f ⁻¹' B) := by
  intro A B
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · intro h y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact h hx

end GaloisConnection

-- ============================================================================
-- Section 1b: Auxiliary Order Lemmas
-- ============================================================================
section AuxiliaryOrder

variable {E : Type*} [Preorder E]

/-- A three-step chain of inequalities can be collapsed via transitivity. -/
lemma preorder_chain (w x y z : E)
    (h₁ : w ≤ x) (h₂ : x ≤ y) (h₃ : y ≤ z) : w ≤ z :=
  (le_trans h₁ h₂).trans h₃

example : (2 : ℕ) ≤ 5 := by
  have h₁ : (2 : ℕ) ≤ 3 := by decide
  have h₂ : (3 : ℕ) ≤ 4 := by decide
  have h₃ : (4 : ℕ) ≤ 5 := by decide
  exact preorder_chain (w := 2) (x := 3) (y := 4) (z := 5) h₁ h₂ h₃

variable {E : Type*} [PartialOrder E]

/-- Greatest lower bounds are unique, mirroring the supremum property used earlier. -/
lemma infimum_unique {A : Set E} {i i' : E}
    (hi : IsGLB A i) (hi' : IsGLB A i') : i = i' :=
  hi.unique hi'

example :
    (0 : ℕ) = 0 := by
  classical
  have h :=
    infimum_unique (A := ({0} : Set ℕ)) (i := 0) (i' := 0)
      (by simpa using isGLB_singleton (a := (0 : ℕ)))
      (by simpa using isGLB_singleton (a := (0 : ℕ)))
  simpa using h

end AuxiliaryOrder

-- ============================================================================
-- Section 1c: Modular Lattices
-- ============================================================================
section ModularLattice

variable {L : Type*} [Lattice L] [IsModularLattice L]

/-- The modular identity relating suprema and infima whenever `x ≤ z`. -/
lemma modular_law (x y z : L) (h : x ≤ z) :
    x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ z :=
  (sup_inf_assoc_of_le (x := x) (y := y) (z := z) h).symm

example (x y : L) :
    x ⊔ (y ⊓ x) = (x ⊔ y) ⊓ x :=
  modular_law (x := x) (y := y) (z := x) le_rfl

end ModularLattice

-- ============================================================================
-- Section 2: Closure Operators (Algebraic Structures)
-- ============================================================================
section BourbakiClosureOperator

variable {α : Type*} [SemilatticeInf α]

/-- A closure operator is an increasing, idempotent, and extensive map.
    These axioms capture the essence of topological closure, algebraic closure,
    and convex closure in Bourbaki's framework. -/
structure BourbakiClosureOperator (α : Type*) [PartialOrder α] where
  cl : α → α
  monotone : Monotone cl
  extensive : ∀ x, x ≤ cl x
  idempotent : ∀ x, cl (cl x) = cl x

variable (c : BourbakiClosureOperator α)

/-- Fixpoints of the closure operator; renamed to avoid clashes with the
topological predicate `IsClosed`. -/
def closureFixed (x : α) : Prop := c.cl x = x

/-- The closure of a closure is the closure. -/
theorem closure_of_closed {x : α} (hx : closureFixed c x) : c.cl x = x := hx

/-- Fixed points are stable under infimum, echoing Bourbaki's preference for
structured hierarchies of subobjects. -/
lemma closureFixed_inf
    {x y : α} (hx : closureFixed c x) (hy : closureFixed c y) :
    closureFixed c (x ⊓ y) := by
  unfold closureFixed at hx hy ⊢
  refine le_antisymm ?_ (c.extensive (x ⊓ y))
  have hx' : c.cl (x ⊓ y) ≤ c.cl x := by
    simpa using c.monotone (show x ⊓ y ≤ x from inf_le_left)
  have hy' : c.cl (x ⊓ y) ≤ c.cl y := by
    simpa using c.monotone (show x ⊓ y ≤ y from inf_le_right)
  have hx'' : c.cl (x ⊓ y) ≤ x := by simpa [hx] using hx'
  have hy'' : c.cl (x ⊓ y) ≤ y := by simpa [hy] using hy'
  exact le_inf hx'' hy''

/-- Intersecting a fixed point with itself keeps it fixed. -/
example {x : α} (hx : closureFixed c x) :
    closureFixed c (x ⊓ x) := by
  simpa using closureFixed_inf (c := c) (x := x) (y := x) hx hx

open BourbakiLeanGuide

/-- The closure operator induces a canonical tower of downward-closed sets. -/
def tower :
    StructureTower α α :=
  StructureTower.ofMonotone
    (ι := α)
    (α := α)
    (level := fun x => {y : α | y ≤ c.cl x})
    (by
      intro x y hxy z hz
      exact le_trans hz (c.monotone hxy))

/-- Each element lies in the level indexed by itself. -/
lemma self_mem_tower_level (x : α) :
    x ∈ (tower c).level x := by
  change x ≤ c.cl x
  exact c.extensive x

/-- The union of all levels equals the whole carrier, reflecting that
every element embeds into the hierarchy via extensivity. -/
lemma tower_union :
    StructureTower.union (tower c) = (Set.univ : Set α) :=
  StructureTower.union_eq_univ_of_forall_mem (tower c) (by
    intro x
    refine ⟨x, ?_⟩
    change x ≤ c.cl x
    exact c.extensive x)

/-- As a corollary, membership in the tower union is immediate. -/
example (x : α) :
    x ∈ StructureTower.union (tower c) := by
  have hx : x ∈ (tower c).level x := self_mem_tower_level (c := c) x
  exact StructureTower.mem_union_of_mem (T := tower c) hx

end BourbakiClosureOperator

-- ============================================================================
-- Section 3: Quotient Groups and Normal Subgroups
-- ============================================================================
section QuotientGroup

variable {G : Type*} [Group G]

/-- A subgroup N is normal if it is closed under conjugation.
    This is expressed in Bourbaki's notation as: ∀ g ∈ G, ∀ n ∈ N, g⁻¹ng ∈ N -/
def IsNormalSubgroup (N : Subgroup G) : Prop :=
  ∀ (n : G) (g : G), n ∈ N → g⁻¹ * n * g ∈ N

/-- The kernel of a group homomorphism is a normal subgroup. -/
theorem kernel_is_normal {H : Type*} [Group H] (f : G →* H) :
    ∀ (n : G) (g : G), n ∈ MonoidHom.ker f → g⁻¹ * n * g ∈ MonoidHom.ker f := by
  intro n g hn
  have hnormal : (MonoidHom.ker f).Normal := inferInstance
  have hx := hnormal.conj_mem n hn g⁻¹
  simpa using hx

/-- First Isomorphism Theorem (structural statement):
    For a group homomorphism f : G → H, the image Im(f) is isomorphic
    to the quotient G/Ker(f). -/
theorem first_isomorphism_structural {H : Type*} [Group H] (f : G →* H) :
    ∃ φ : (G ⧸ MonoidHom.ker f) →* MonoidHom.range f, Bijective φ := by
  use QuotientGroup.quotientKerEquivRange f
  exact (QuotientGroup.quotientKerEquivRange f).bijective

/-- Example: The trivial subgroup is normal -/
example : IsNormalSubgroup (⊥ : Subgroup G) := by
  intro n g hn
  simp at hn ⊢
  rw [hn]
  simp

end QuotientGroup

-- ============================================================================
-- Section 4: Connectedness in Topology
-- ============================================================================
section Connectedness

variable {X : Type*} [TopologicalSpace X]

/-- A space is connected if it cannot be written as a disjoint union
    of two nonempty open sets. This definition follows Bourbaki's approach
    via the absence of non-trivial clopen sets. -/
theorem connected_iff_no_clopen_partition :
    ConnectedSpace X ↔
    (Nonempty X ∧ ∀ U : Set X, IsOpen U → IsClosed U → (U = ∅ ∨ U = univ)) := by
  classical
  constructor
  · intro h
    obtain ⟨hx, hcl⟩ := (connectedSpace_iff_clopen (α := X)).mp h
    refine ⟨hx, ?_⟩
    intro U hUopen hUclosed
    exact hcl U ⟨hUclosed, hUopen⟩
  · intro h
    rcases h with ⟨hx, hprop⟩
    refine (connectedSpace_iff_clopen (α := X)).mpr ⟨hx, ?_⟩
    intro U hU
    exact hprop U hU.2 hU.1

/-- The continuous image of a connected space is connected.
    This is a fundamental theorem in Bourbaki's topology. -/
theorem connected_continuous_image {Y : Type*} [TopologicalSpace Y]
    [ConnectedSpace X] (f : X → Y) (hf : Continuous f) :
    IsConnected (range f) := by
  exact isConnected_range hf

end Connectedness

-- ============================================================================
-- Section 5: Universal Properties and Categorical Perspective
-- ============================================================================
section UniversalProperties

open Function

variable {X A B : Type*}

/-- The cartesian product realises the universal property of binary products in `Type`. -/
theorem prod_universal (f : X → A) (g : X → B) :
    ∃! h : X → A × B, (Prod.fst ∘ h = f) ∧ (Prod.snd ∘ h = g) := by
  classical
  refine ⟨fun x => (f x, g x), ?_, ?_⟩
  · constructor <;> funext x <;> rfl
  · intro h hh
    rcases hh with ⟨hf, hg⟩
    funext x
    apply Prod.ext
    · have : (Prod.fst ∘ h) x = f x := congrArg (fun k : X → A => k x) hf
      simpa [Function.comp] using this
    · have : (Prod.snd ∘ h) x = g x := congrArg (fun k : X → B => k x) hg
      simpa [Function.comp] using this

/-- The canonical pairing map realises the universal arrow to the product. -/
example (f : ℕ → ℤ) (g : ℕ → ℤ) :
    ∃! h : ℕ → ℤ × ℤ, (Prod.fst ∘ h = f) ∧ (Prod.snd ∘ h = g) :=
  prod_universal (X := ℕ) f g

end UniversalProperties

-- ============================================================================
-- Section 6: Homeomorphisms and Topological Equivalence
-- ============================================================================
section Homeomorphism

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A homeomorphism is a continuous bijection with continuous inverse.
    Bourbaki emphasizes that homeomorphic spaces share all topological
    properties. -/
def IsHomeomorphism (f : X → Y) : Prop :=
  Continuous f ∧ Bijective f ∧ ∃ g : Y → X, Continuous g ∧ LeftInverse g f ∧ RightInverse g f

/-- Homeomorphisms preserve compactness -/
theorem homeomorphism_preserves_compactness
    (f : X ≃ₜ Y) [CompactSpace X] :
    CompactSpace Y :=
  Homeomorph.compactSpace f

/-- Homeomorphisms preserve connectedness -/
theorem homeomorphism_preserves_connectedness
    (f : X ≃ₜ Y) [ConnectedSpace X] :
    ConnectedSpace Y := by
  classical
  have hx : IsConnected (Set.univ : Set X) := isConnected_univ (α := X)
  have hy : IsConnected (Set.univ : Set Y) := by
    simpa [Set.preimage_univ] using
      (f.isConnected_preimage (s := (Set.univ : Set Y))).1 hx
  exact (connectedSpace_iff_univ (α := Y)).mpr hy

/-- The composition of homeomorphisms is a homeomorphism.
    This shows that homeomorphisms form a groupoid. -/
def homeomorph_trans {Z : Type*} [TopologicalSpace Z]
    (f : X ≃ₜ Y) (g : Y ≃ₜ Z) :
    X ≃ₜ Z :=
  f.trans g

end Homeomorphism

-- ============================================================================
-- Section 7: Advanced Example - Urysohn's Lemma (Sketch)
-- ============================================================================
section UrysohnLemma

variable {X : Type*} [TopologicalSpace X] [NormalSpace X]

/-- Urysohn's Lemma: In a normal space, disjoint closed sets can be
    separated by a continuous function to [0,1].
    This is a cornerstone of Bourbaki's general topology. -/
theorem urysohn_lemma_exists {A B : Set X}
    (hAclosed : IsClosed A) (hBclosed : IsClosed B)
    (hdisjoint : Disjoint A B) :
    ∃ f : X → ℝ, Continuous f ∧
      (∀ x ∈ A, f x = 0) ∧
      (∀ x ∈ B, f x = 1) ∧
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) := by
  classical
  obtain ⟨f, hfA, hfB, hfI⟩ :=
    exists_continuous_zero_one_of_isClosed (X := X)
      (s := A) (t := B) hAclosed hBclosed hdisjoint
  refine ⟨fun x => f x, f.continuous, ?_, ?_, ?_⟩
  · intro x hx
    simpa using hfA hx
  · intro x hx
    simpa using hfB hx
  · intro x
    obtain ⟨hx₁, hx₂⟩ := hfI x
    exact ⟨hx₁, hx₂⟩

end UrysohnLemma

-- ============================================================================
-- Section 8: Metric Spaces and Completeness
-- ============================================================================
section MetricSpaces

variable {X : Type*} [MetricSpace X]

/-- A Cauchy sequence in a metric space, phrased via the standard uniform structure. -/
def IsCauchySeq (x : ℕ → X) : Prop :=
  CauchySeq x

/-- Bourbaki's notion of completeness coincides with the usual one in Lean. -/
def BourbakiIsComplete : Prop :=
  CompleteSpace X

/-- Uniformly continuous maps send Cauchy sequences to Cauchy sequences. -/
theorem uniformContinuous_maps_cauchy {Y : Type*} [MetricSpace Y]
    (f : X → Y) (hf : UniformContinuous f) (x : ℕ → X) (hx : IsCauchySeq x) :
    IsCauchySeq (f ∘ x) := by
  simpa using hf.comp_cauchySeq hx

end MetricSpaces

-- ============================================================================
-- Philosophical Notes on Bourbaki's Approach
-- ============================================================================

/-!
## Bourbaki's Structuralist Philosophy in Lean

The exercises above embody several key Bourbaki principles:

1. **Mother Structures** (Structures mères):
   - Order structures: Preorders, partial orders, lattices
   - Algebraic structures: Groups, rings, modules
   - Topological structures: Topological spaces, uniform spaces

2. **Universal Constructions**:
   - Products, coproducts, limits, colimits
   - Quotients and kernels
   - Free objects and forgetful functors

3. **Functoriality**:
   - Structure-preserving maps (homomorphisms, continuous functions)
   - Naturality and diagram commutativity
   - Adjunctions and Galois connections

4. **Abstraction and Generality**:
   - Starting from sets, relations, and functions
   - Building structures through axioms
   - Deriving properties from minimal assumptions

5. **Rigorous Formalization**:
   - Every concept is precisely defined
   - Every theorem is proven from axioms
   - No appeal to geometric intuition without formal justification

The Lean proof assistant and Mathlib4 provide an ideal environment for
realizing Bourbaki's vision of formalized mathematics, with dependent type
theory offering even more expressive power than set theory alone.
-/




































