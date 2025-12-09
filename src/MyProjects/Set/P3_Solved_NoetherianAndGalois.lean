/-
# P3_NextFrontiers.lean: The Next Frontiers

Based on your excellent implementations of P1_Extended_Next and P2_Advanced_Analysis,
this module proposes concrete next steps that build on your StructureTower framework
and push toward research-level mathematics.

These exercises are designed to be challenging but achievable, combining:
* Your StructureTower abstraction
* Advanced Bourbaki topics
* Modern mathematical perspectives
-/

import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.FieldTheory.Extension
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Order.Closure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import MyProjects.Set.Bourbaki_Lean_Guide
import MyProjects.Set.P1_Extended
import MyProjects.Set.P1_Extended_Next

open Classical
open CategoryTheory
open BourbakiLeanGuide P1ExtendedNext

namespace P3NextFrontiers

/-!
## Challenge 1: Noetherian Rings and Ascending Chain Condition

Noetherian rings are fundamental in commutative algebra. Use StructureTower
to express the ascending chain condition.
-/

section NoetherianRings

variable {R : Type*} [CommRing R]

/-- A ring R is Noetherian if every ascending chain of ideals stabilizes. -/
class IsNoetherianRing (R : Type*) [CommRing R] : Prop where
  ascending_chain_condition :
    ∀ (f : ℕ → Ideal R), Monotone f → ∃ N, ∀ n ≥ N, f n = f N

abbrev IdealChain (R : Type*) [CommRing R] := ℕ → Ideal R

namespace IdealChain

variable {R : Type*} [CommRing R]

/-- View an ascending chain of ideals as a set-valued filtration on `R`. -/
def asFiltration (f : IdealChain R) : Filtration R :=
  fun n => (f n : Set R)

lemma monotone_asFiltration {f : IdealChain R} (hf : Monotone f) :
    Monotone (asFiltration (R := R) f) := by
  intro n m hnm x hx
  change x ∈ (f m : Set R)
  have hx' : x ∈ (f n : Set R) := hx
  exact (hf hnm) hx'

/-- The StructureTower attached to an ascending chain of ideals. -/
def tower (f : IdealChain R) (hf : Monotone f) :
    StructureTower ℕ R :=
  filtrationTower (asFiltration (R := R) f)
    (monotone_asFiltration (R := R) hf)

end IdealChain

/-- The stabilization point of a Noetherian chain. -/
noncomputable def stabilizationPoint [IsNoetherianRing R]
    (f : IdealChain R) (hf : Monotone f) : ℕ :=
  Nat.find (IsNoetherianRing.ascending_chain_condition f hf)

/-- Exercise: Prove that the chain stabilizes at the stabilization point. -/
theorem chain_stabilizes_at_point [IsNoetherianRing R]
    (f : IdealChain R) (hf : Monotone f) :
    ∀ n ≥ stabilizationPoint f hf, f n = f (stabilizationPoint f hf) := by
  dsimp [stabilizationPoint]
  exact
    Nat.find_spec
      (IsNoetherianRing.ascending_chain_condition (R := R) f hf)

/-- Exercise: The tower union equals the stabilization ideal. -/
theorem noetherian_tower_stabilizes [IsNoetherianRing R]
    (f : IdealChain R) (hf : Monotone f) :
    StructureTower.union (IdealChain.tower (R := R) f hf) =
    (f (stabilizationPoint f hf) : Set R) := by
  classical
  set N := stabilizationPoint f hf
  have hstab := chain_stabilizes_at_point (R := R) (f := f) (hf := hf)
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨n, hx⟩
    have hx' :
        x ∈ (f (max n N) : Set R) :=
      (hf (Nat.le_max_left _ _)) hx
    have hmax : f (max n N) = f N :=
      hstab (max n N) (Nat.le_max_right _ _)
    simpa [N, hmax] using hx'
  · intro hx
    have hx' :
        x ∈ (IdealChain.tower (R := R) f hf).level N := by
      simpa [IdealChain.tower, IdealChain.asFiltration, N]
        using hx
    exact
      StructureTower.mem_union_of_mem
        (T := IdealChain.tower (R := R) f hf) hx'

/-- Exercise: In a Noetherian ring, every ideal is finitely generated. -/
theorem noetherian_ideals_finitely_generated [IsNoetherianRing R] (I : Ideal R) :
    ∃ (s : Finset R), Ideal.span (s : Set R) = I := by
  classical
  -- helper lemma: in a proper inclusion of ideals we can pick a witness
  have exists_mem_of_lt :
      ∀ ⦃J K : Ideal R⦄, J ≤ K → J ≠ K → ∃ x ∈ K, x ∉ J := by
    intro J K hJK hne
    classical
    have :
        ¬ ∀ x, x ∈ K → x ∈ J := by
      intro h
      have hKJ : K ≤ J := by
        intro x hxK
        exact h x hxK
      exact hne (le_antisymm hJK hKJ)
    obtain ⟨x, hx⟩ := not_forall.mp this
    obtain ⟨hxK, hxnot⟩ := Classical.not_imp.mp hx
    exact ⟨x, hxK, hxnot⟩
  by_contra hI
  have hI' : ∀ s : Finset R, Ideal.span (s : Set R) ≠ I := by
    classical
    simpa [not_exists] using hI
  -- construct an infinite strictly ascending chain of finitely generated ideals
  classical
  let chainData :
      ℕ → { s : Finset R // Ideal.span ((s : Finset R) : Set R) ≤ I } :=
    Nat.rec
      (⟨∅,
        by
          simpa using (bot_le : (⊥ : Ideal R) ≤ I)⟩)
      (fun n data =>
        let s : Finset R := data.1
        let hs : Ideal.span ((s : Finset R) : Set R) ≤ I := data.2
        have hx :
            ∃ x ∈ I, x ∉ Ideal.span ((s : Finset R) : Set R) :=
          exists_mem_of_lt hs (hI' s)
        let x := Classical.choose hx
        have hx_mem : x ∈ I := (Classical.choose_spec hx).1
        have hx_not :
            x ∉ Ideal.span ((s : Finset R) : Set R) :=
          (Classical.choose_spec hx).2
        have hs' :
            Ideal.span ((insert x s : Finset R) : Set R) ≤ I := by
          refine Ideal.span_le.mpr ?_
          intro y hy
          classical
          have hy' : y ∈ insert x s := by
            simpa using hy
          rcases Finset.mem_insert.mp hy' with hy'' | hy''
          · simpa [hy''] using hx_mem
          · have hy_s : y ∈ (s : Set R) := by
              simpa using hy''
            have hy_span : y ∈ Ideal.span ((s : Finset R) : Set R) :=
              Ideal.subset_span hy_s
            exact hs hy_span
        ⟨insert x s, hs'⟩)
  let chainFinset : ℕ → Finset R := fun n => (chainData n).1
  have chain_subset :
      ∀ n, Ideal.span ((chainFinset n : Finset R) : Set R) ≤ I := by
    intro n
    exact (chainData n).2
  let chain : ℕ → Ideal R :=
    fun n => Ideal.span ((chainFinset n : Finset R) : Set R)
  have chain_succ :
      ∀ n,
        ∃ x ∈ I,
          x ∉ chain n ∧
            chainFinset (n + 1) =
              insert x (chainFinset n) := by
    intro n
    classical
    set hx :=
      exists_mem_of_lt
        (chain_subset n)
        (hI' (chainFinset n)) with hx_def
    refine ⟨Classical.choose hx, ?_, ?_, ?_⟩
    · have := (Classical.choose_spec hx).1
      simpa [hx_def] using this
    · have := (Classical.choose_spec hx).2
      simpa [chain, chainFinset] using this
    · simp [chainFinset, chainData]
  have chain_mono : Monotone chain := by
    classical
    have step :
        ∀ n, chain n ≤ chain (n + 1) := by
      intro n
      obtain ⟨x, -, -, hxEq⟩ := chain_succ n
      refine Ideal.span_le.mpr ?_
      intro y hy
      have hy_fin : y ∈ chainFinset n := by
        simpa using hy
      have hy_insert :
          y ∈ (insert x (chainFinset n) : Finset R) :=
        Finset.mem_insert.mpr (Or.inr hy_fin)
      have : y ∈
          ((insert x (chainFinset n) : Finset R) : Set R) := by
        simpa using hy_insert
      simpa [chain, hxEq] using
        (Ideal.subset_span (s := ((insert x (chainFinset n) : Finset R) : Set R)) this)
    intro n m hnm
    have step'' : ∀ k, chain n ≤ chain (k + n) := by
      intro k
      induction k with
      | zero =>
          simpa using (le_rfl : chain n ≤ chain n)
      | succ k ih =>
          have hk := step (k + n)
          have hk_total : chain n ≤ chain (k + n + 1) := le_trans ih hk
          simpa [Nat.succ_add, Nat.add_assoc] using hk_total
    have hmn : (m - n) + n = m := Nat.sub_add_cancel hnm
    have := step'' (m - n)
    simpa [hmn, Nat.add_comm] using this
  have chain_strict :
      ∀ n, chain n ≠ chain (n + 1) := by
    intro n
    obtain ⟨x, hxI, hxnot, hxEq⟩ := chain_succ n
    intro h
    have hx_in :
        x ∈ chain (n + 1) := by
      have hx_in_span :
          x ∈ Ideal.span
            ((insert x (chainFinset n : Finset R)) : Set R) :=
        by
          refine Ideal.subset_span ?_
          simp
      simpa [chain, hxEq] using hx_in_span
    have hx_prev : x ∈ chain n := by
      simpa [h] using hx_in
    exact hxnot hx_prev
  obtain ⟨N, hN⟩ :=
    IsNoetherianRing.ascending_chain_condition
      (f := chain) chain_mono
  -- stability contradicts strict increase
  have hEq :=
    hN (N + 1) (Nat.le_of_lt (Nat.lt_succ_self N))
  have hEq' : chain N = chain (N + 1) := hEq.symm
  exact (chain_strict N) hEq'

end NoetherianRings

/-!
## Challenge 2: Galois Connections and Complete Lattices

Extend your Galois connection work to show the relationship with complete lattices.
-/

section GaloisAndLattices

variable {α β : Type*} [CompleteLattice α] [CompleteLattice β]

/-- A Galois connection induces a closure operator on α. -/
def galoisClosure {l : α → β} {u : β → α} (gc : GaloisConnection l u) :
    α → α := u ∘ l

/-- Exercise: The Galois closure is indeed a closure operator. -/
theorem galoisClosure_is_closure {l : α → β} {u : β → α} (gc : GaloisConnection l u) :
    ∃ c : BourbakiClosureOperator α,
      c.cl = galoisClosure gc := by
  classical
  refine ⟨
    { cl := galoisClosure gc
      monotone := gc.monotone_u.comp gc.monotone_l
      extensive := by
        intro x
        exact gc.le_u_l x
      idempotent := by
        intro x
        unfold galoisClosure
        simp [Function.comp, gc.u_l_u_eq_u (l x)] }, rfl⟩

/-- Exercise: The fixed points of Galois closure form a complete lattice. -/
noncomputable def galoisClosure_fixedPoints_complete_lattice
    {l : α → β} {u : β → α} (gc : GaloisConnection l u) :
    CompleteLattice {x : α | galoisClosure gc x = x} := by
  classical
  let c := gc.closureOperator
  have : CompleteLattice c.Closeds := c.gi.liftCompleteLattice
  simpa [galoisClosure, Function.comp, ClosureOperator.Closeds, ClosureOperator.IsClosed]
    using this

/-- The Galois closure agrees pointwise with the mathlib closure operator. -/
example {l : α → β} {u : β → α} (gc : GaloisConnection l u) (x : α) :
    galoisClosure gc x = gc.closureOperator x :=
  rfl

/-- Exercise: Connect this to your StructureTower framework. -/
def galoisTower {l : α → β} {u : β → α} (gc : GaloisConnection l u) :
    StructureTower α α where
  level x := {y : α | y ≤ galoisClosure gc x}
  monotone_level := by
    intro x x' hxx' y hy
    change y ≤ galoisClosure gc x'
    have hmon : Monotone (galoisClosure gc) :=
      gc.monotone_u.comp gc.monotone_l
    exact le_trans hy (hmon hxx')

/-- For the identity Galois connection on sets, the tower records subset inclusions. -/
example {γ : Type*} (x y : Set γ) (hyx : y ⊆ x) :
    y ∈
      (galoisTower
        (gc := (GaloisConnection.id :
          GaloisConnection (fun s : Set γ => s) fun s => s))).level x := by
  classical
  change y ⊆ galoisClosure _ x
  simpa [galoisClosure]

end GaloisAndLattices
