import Mathlib.Data.Nat.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import MyProjects.ST.MeasurableTower
import MyProjects.ST.Claude_Probability

/-
# Probability Towers – Extended: Stopping Times

This file continues the development from `Claude_Probability.lean` by introducing
stopping times, showing that the tower `minLayer` defines a canonical stopping time,
constructing first hitting times, and formalising the natural filtration generated
by a process.
-/

noncomputable section

universe u v w

open Classical
open Set
open scoped MeasureTheory

namespace MyProjects
namespace ST
namespace Claude

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A stopping time for a discrete filtration. -/
structure StoppingTime (F : DiscreteFiltration Ω) where
  /-- The time at which we stop. -/
  τ : Ω → ℕ
  /-- Adapted condition: the debut event is measurable at each time. -/
  adapted : ∀ n : ℕ, MeasurableSet[(F.sigma n)] {ω | τ ω ≤ n}

namespace StoppingTime

variable {F : DiscreteFiltration Ω}

/-- Constant stopping time. -/
def const (F : DiscreteFiltration Ω) (n : ℕ) : StoppingTime F where
  τ := fun _ => n
  adapted := by
    intro m
    by_cases h : n ≤ m
    · have : {ω : Ω | n ≤ m} = (Set.univ : Set Ω) := by
        ext ω; simp [h]
      simpa [this]
    · have : {ω : Ω | n ≤ m} = (∅ : Set Ω) := by
        ext ω; simp [h]
      simpa [this]

/-- Infimum of two stopping times (pointwise minimum). -/
def inf (σ τ : StoppingTime F) : StoppingTime F where
  τ := fun ω => min (σ.τ ω) (τ.τ ω)
  adapted := by
    intro n
    have hset :
        {ω : Ω | min (σ.τ ω) (τ.τ ω) ≤ n} =
        {ω : Ω | σ.τ ω ≤ n} ∪ {ω : Ω | τ.τ ω ≤ n} := by
      ext ω
      simp [min_le_iff]
    rw [hset]
    exact MeasurableSet.union (σ.adapted n) (τ.adapted n)

/-- Supremum of two stopping times (pointwise maximum). -/
def sup (σ τ : StoppingTime F) : StoppingTime F where
  τ := fun ω => max (σ.τ ω) (τ.τ ω)
  adapted := by
    intro n
    have hset :
        {ω : Ω | max (σ.τ ω) (τ.τ ω) ≤ n} =
        {ω : Ω | σ.τ ω ≤ n} ∩ {ω : Ω | τ.τ ω ≤ n} := by
      ext ω
      simp [max_le_iff]
    rw [hset]
    exact MeasurableSet.inter (σ.adapted n) (τ.adapted n)

end StoppingTime

/-- The tower `minLayer` defines a canonical stopping time (under countability). -/
def minLayerStoppingTime (F : DiscreteFiltration Ω) [Countable Ω] :
    StoppingTime F where
  τ := fun ω => F.toMeasurableTower.minLayer ω
  adapted := by
    intro n
    classical
    have hset :
        {ω : Ω | F.toMeasurableTower.minLayer ω ≤ n} =
          ⋃ (x : {ω // F.toMeasurableTower.minLayer ω ≤ n}),
            ({x.1} : Set Ω) := by
      ext ω; constructor
      · intro hω
        refine Set.mem_iUnion.mpr ?_
        refine ⟨⟨ω, hω⟩, ?_⟩
        simp
      · intro hω
        rcases Set.mem_iUnion.mp hω with ⟨x, hx⟩
        rcases hx with rfl
        exact x.property
    haveI : Countable F.toMeasurableTower.carrier := by
      change Countable Ω
      infer_instance
    haveI : Countable {ω // F.toMeasurableTower.minLayer ω ≤ n} :=
      Subtype.countable (p := fun ω => F.toMeasurableTower.minLayer ω ≤ n)
    refine hset ▸ MeasurableSet.iUnion fun x => ?_
    have hx :
        MeasurableSet[(F.sigma (F.toMeasurableTower.minLayer x.1))]
          ({x.1} : Set Ω) :=
      F.toMeasurableTower.minLayer_mem x.1
    exact (F.mono x.property) (s := {x.1}) hx

/-- Minimality of the canonical stopping time. -/
theorem minLayerStoppingTime_minimal (F : DiscreteFiltration Ω) (ω : Ω)
    (τ : StoppingTime F)
    (h : MeasurableSet[(F.sigma (τ.τ ω))] ({ω} : Set Ω)) :
    F.toMeasurableTower.minLayer ω ≤ τ.τ ω := by
  exact F.minLayer_le h

/-- First hitting time of a sequence of measurable sets.
We assume every outcome admits a minimal hitting index. -/
def firstHittingTime (F : DiscreteFiltration Ω)
    (A : ℕ → Set Ω)
    (hA : ∀ n, MeasurableSet[(F.sigma n)] (A n))
    (hStruct : ∀ ω, ∃ k, ω ∈ A k ∧ ∀ j < k, ω ∉ A j) :
    StoppingTime F where
  τ := fun ω => Classical.choose (hStruct ω)
  adapted := by
    intro n
    classical
    have key :
        {ω : Ω | Classical.choose (hStruct ω) ≤ n} =
          ⋃ k ∈ Finset.range (n + 1),
            (A k ∩ ⋂ j ∈ Finset.range k, (A j)ᶜ) := by
      ext ω; constructor
      · intro hω
        set k := Classical.choose (hStruct ω)
        have hk := Classical.choose_spec (hStruct ω)
        have hk_le : k ≤ n := by simpa [k] using hω
        have hk_range : k ∈ Finset.range (n + 1) := by
          simp [Finset.mem_range, Nat.lt_succ_iff, hk_le, k]
        have hk_mem : ω ∈ A k := hk.1
        have hmin : ∀ j < k, ω ∉ A j := hk.2
        refine Set.mem_iUnion.mpr ?_
        refine ⟨k, ?_⟩
        refine Set.mem_iUnion.mpr ?_
        refine ⟨hk_range, ?_⟩
        refine ⟨hk_mem, ?_⟩
        have : ∀ j ∈ Finset.range k, ω ∈ (A j)ᶜ := by
          intro j hj
          have hj_lt : j < k := Finset.mem_range.mp hj
          have : ω ∉ A j := hmin j hj_lt
          simpa using this
        simpa using this
      · intro hω
        rcases Set.mem_iUnion.mp hω with ⟨k, hk⟩
        rcases Set.mem_iUnion.mp hk with ⟨hk_range, hrest⟩
        rcases hrest with ⟨hk_mem, hall⟩
        set k₀ := Classical.choose (hStruct ω)
        have hk₀ := Classical.choose_spec (hStruct ω)
        have hk_lt : k < n + 1 := Finset.mem_range.mp hk_range
        have hk_le : k ≤ n := Nat.lt_succ_iff.mp hk_lt
        have hmin : ∀ j < k, ω ∉ A j := by
          have hall' :
              ∀ j ∈ Finset.range k, ω ∈ (A j)ᶜ := by
            simpa using hall
          intro j hj
          have := hall' j ((Finset.mem_range).2 hj)
          simpa using this
        have hk₀_le_k : k₀ ≤ k := by
          by_contra hlt
          have hk_lt : k < k₀ := Nat.lt_of_not_ge hlt
          exact (hk₀.2 k hk_lt) hk_mem
        have k_le_k₀ : k ≤ k₀ := by
          by_contra hlt
          have hk₀_lt : k₀ < k := Nat.lt_of_not_ge hlt
          exact (hmin k₀ hk₀_lt) hk₀.1
        have hk_eq : k = k₀ := le_antisymm k_le_k₀ hk₀_le_k
        simpa [hk_eq] using hk_le
    rw [key]
    apply MeasurableSet.biUnion
    · exact (Finset.range (n + 1)).countable_toSet
    intro k hk
    have hk_lt : k < n + 1 := Finset.mem_range.mp hk
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp hk_lt
    have hAk : MeasurableSet[(F.sigma n)] (A k) :=
      (F.mono hk_le) (s := A k) (hA k)
    have hcompl :
        ∀ j ∈ Finset.range k,
          MeasurableSet[(F.sigma n)] ((A j)ᶜ) := by
      intro j hj
      have hj_lt : j < k := Finset.mem_range.mp hj
      have hj_le : j ≤ n := Nat.le_trans (Nat.le_of_lt hj_lt) hk_le
      have hAj : MeasurableSet[(F.sigma j)] (A j) := hA j
      have hmono := F.mono hj_le
      exact (MeasurableSet.compl (hmono (s := A j) hAj))
    exact
      MeasurableSet.inter hAk
        (MeasurableSet.biInter (Finset.range k).countable_toSet hcompl)

/-- The first hitting time hits as expected. -/
theorem firstHittingTime_spec (F : DiscreteFiltration Ω)
    (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet[(F.sigma n)] (A n))
    (hStruct : ∀ ω, ∃ k, ω ∈ A k ∧ ∀ j < k, ω ∉ A j) (ω : Ω) :
    ω ∈ A ((firstHittingTime F A hA hStruct).τ ω) := by
  classical
  exact (Classical.choose_spec (hStruct ω)).1

/-- Natural filtration generated by a sequence of measurable maps.
The separating assumption ensures singletons appear in some layer. -/
def naturalFiltration {α : Type v} [MeasurableSpace α]
    (X : ℕ → Ω → α) (hX : ∀ n, Measurable (X n))
    (hSep : ∀ ω : Ω, ∃ k : ℕ, ∃ A : Set α,
      MeasurableSet A ∧ X k ⁻¹' A = {ω}) :
    DiscreteFiltration Ω where
  sigma n := MeasurableSpace.generateFrom
    {s | ∃ k ≤ n, ∃ A : Set α, MeasurableSet A ∧ s = X k ⁻¹' A}
  adapted := by
    intro m n hmn
    apply MeasurableSpace.generateFrom_mono
    intro s hs
    obtain ⟨k, hk, A, hA, rfl⟩ := hs
    exact ⟨k, Nat.le_trans hk hmn, A, hA, rfl⟩
  bounded := by
    intro n
    apply MeasurableSpace.generateFrom_le
    intro s hs
    obtain ⟨k, _, A, hA, rfl⟩ := hs
    have hpre : MeasurableSet (X k ⁻¹' A) := measurableSet_preimage (hX k) hA
    simpa using hpre
  point_measurable := by
    intro ω
    classical
    obtain ⟨k, A, hA, hpre⟩ := hSep ω
    refine ⟨k, ?_⟩
    have : ({ω} : Set Ω) ∈
        {s | ∃ k' ≤ k, ∃ A : Set α, MeasurableSet A ∧ s = X k' ⁻¹' A} := by
      refine ⟨k, le_rfl, A, hA, ?_⟩
      simpa using hpre.symm
    simpa using (MeasurableSpace.measurableSet_generateFrom this)

/-- Constant stopping time evaluates to the underlying constant. -/
example (F : DiscreteFiltration Ω) :
    (StoppingTime.const F 0).τ = fun _ => 0 := rfl

/-- Infimum of constant stopping times. -/
example (F : DiscreteFiltration Ω) :
    (StoppingTime.inf (StoppingTime.const F 2) (StoppingTime.const F 3)).τ =
      fun _ => 2 := by
  ext ω
  simp [StoppingTime.inf, StoppingTime.const, min_eq_left]

end Claude
end ST
end MyProjects
