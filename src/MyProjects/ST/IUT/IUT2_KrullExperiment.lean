import Mathlib

/-!
Minimal experiment: StructureTowerMin + IdealChain + krullTower
-/

structure StructureTowerMin where
  carrier : Type
  layer : ℕ → Set carrier
  covering : ∀ x : carrier, ∃ i, x ∈ layer i
  monotone : ∀ {i j}, i ≤ j → layer i ⊆ layer j
  minLayer : carrier → ℕ
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  minLayer_minimal : ∀ x i, x ∈ layer i → minLayer x ≤ i

namespace KrullExperiment

inductive IdealChain : Type
  | trivial : IdealChain
  | onestep : IdealChain
  | twostep : IdealChain
  deriving DecidableEq

def chainLength : IdealChain → ℕ
  | .trivial => 0
  | .onestep => 1
  | .twostep => 2

def krullTower : StructureTowerMin where
  carrier := IdealChain
  layer n := { c : IdealChain | chainLength c ≤ n }
  covering := by
    intro c
    refine ⟨chainLength c, ?_⟩
    change chainLength c ≤ chainLength c
    exact le_rfl
  monotone := by
    intro i j hij c hc
    change chainLength c ≤ i at hc
    change chainLength c ≤ j
    exact le_trans hc hij
  minLayer := chainLength
  minLayer_mem := by intro c; change chainLength c ≤ chainLength c; exact le_rfl
  minLayer_minimal := by intro c i hc; exact hc


example : krullTower.minLayer IdealChain.twostep = 2 := rfl

end KrullExperiment
