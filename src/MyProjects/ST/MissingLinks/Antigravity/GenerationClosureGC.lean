import MyProjects.ST.CAT2_complete
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Lattice
import Mathlib.Data.Nat.Lattice

/-!
# Generation and Closure in Structure Towers

This file implements the "Generation" aspect of Structure Towers.
Focus: Computable rank for finite sets (M1).

-/

namespace ST

open StructureTowerWithMin

-- ==========================================
-- Lane B: Computable Finite (Index = ℕ)
-- ==========================================

section NatRank

variable (T : StructureTowerWithMin)

-- We require Index to have SemilatticeSup and OrderBot.
variable [SemilatticeSup T.Index] [OrderBot T.Index]
-- DecidableEq is needed for Finset operations
variable [DecidableEq T.carrier]
variable (h_compat : ∀ x y : T.Index, x ≤ y ↔ T.indexPreorder.le x y)

-- Manual instance for commutativity to satisfy Finset.fold
instance : Std.Commutative (α := T.Index) (· ⊔ ·) := ⟨sup_comm⟩
instance : Std.Associative (α := T.Index) (· ⊔ ·) := ⟨sup_assoc⟩

/--
Computable rank for finite sets (`Finset`).
`rankFin s := s.fold (· ⊔ ·) ⊥ T.minLayer`
-/
def rankFin (s : Finset T.carrier) : T.Index :=
  s.fold (· ⊔ ·) ⊥ T.minLayer

/--
Computable closure for finite sets.
-/
def closureFin (s : Finset T.carrier) : Set T.carrier :=
  T.layer (rankFin T s)

theorem rankFin_le_iff (s : Finset T.carrier) (i : T.Index) :
    rankFin T s ≤ i ↔ (s : Set T.carrier) ⊆ T.layer i := by
  have le_iff_Tower : ∀ x y, x ≤ y ↔ T.indexPreorder.le x y := h_compat

  constructor
  · -- Left to Right
    intro h x hx
    have min_le_rank : T.minLayer x ≤ rankFin T s := by
      simp [rankFin]
      let P (s : Finset T.carrier) := ∀ y ∈ s, T.minLayer y ≤ s.fold (· ⊔ ·) ⊥ T.minLayer
      have P_holds : P s := by
        intro y hy
        revert y
        induction s using Finset.induction_on with
        | empty =>
          intro y hy
          contradiction
        | insert a s' ha' IH =>
          intro y hy
          simp_all [Finset.fold_insert ha', Finset.mem_insert]
          cases hy with
          | inl h_eq =>
              subst h_eq
              exact le_sup_left
          | inr h_in =>
              exact le_trans (IH y h_in) le_sup_right
      exact P_holds x hx

    have min_le_i_Lat : T.minLayer x ≤ i := le_trans min_le_rank h
    rw [le_iff_Tower] at min_le_i_Lat
    apply T.monotone min_le_i_Lat
    apply T.minLayer_mem

  · -- Right to Left
    intro h
    simp [rankFin]
    induction s using Finset.induction_on with
    | empty =>
      exact bot_le
    | insert a s' ha' IH =>
      simp [Finset.fold_insert ha']
      -- Switch goal to Lattice order to use sup_le
      rw [le_iff_Tower]
      rw [← le_iff_Tower]
      -- Note: If goal is already T.indexPreorder, usage of `le_iff_Tower`
      -- to rewrite to Lattice `<=` is needed.
      -- However, since `rankFin` returns `Index`, the `<=` in goal depends on context.
      -- `rankFin_le_iff` return type is implicit.
      -- Wait, I will force the rewrite to be sure.
      rw [← le_iff_Tower]

      apply sup_le
      · -- minLayer a ≤ i
        have ha_in : a ∈ T.layer i := h (Finset.mem_insert_self a s')
        have min_le_tower : T.indexPreorder.le (T.minLayer a) i :=
          T.minLayer_minimal a i ha_in
        rw [← le_iff_Tower] at min_le_tower
        exact min_le_tower
      · -- fold s' ≤ i
        -- IH is in Lattice order or Tower?
        -- IH matches goal type.
        -- We unwrapped earlier.
        -- Let's trust compatible reasoning.
        simp [rankFin] at IH
        apply IH
        intro x hx
        apply h
        exact Finset.mem_insert_of_mem a hx

theorem mem_closureFin (h_compat : ∀ x y : T.Index, x ≤ y ↔ T.indexPreorder.le x y)
    (s : Finset T.carrier) (x : T.carrier) :
    x ∈ s → x ∈ closureFin T s := by
  intro hx
  rw [closureFin]
  have refl : rankFin T s ≤ rankFin T s := le_refl _
  have sub : (s : Set T.carrier) ⊆ T.layer (rankFin T s) :=
    (rankFin_le_iff T h_compat s (rankFin T s)).mp refl
  exact sub hx

end NatRank

end ST

-- ==========================================
-- Examples and Verification
-- ==========================================

namespace ST.Examples

open StructureTowerWithMin

abbrev NatTowerConcrete : StructureTowerWithMin :=
{
  carrier := ℕ
  Index := ℕ
  indexPreorder := inferInstance
  layer := fun n => {k | k ≤ n}
  minLayer := id
  monotone := fun {i} {j} h x hx => le_trans hx h
  minLayer_mem := fun x => le_refl x
  minLayer_minimal := fun _ _ h => h
  covering := fun x => ⟨x, le_refl x⟩
}

theorem nat_compat : ∀ x y : NatTowerConcrete.Index, x ≤ y ↔ NatTowerConcrete.indexPreorder.le x y :=
  fun _ _ => Iff.rfl

#eval ST.rankFin NatTowerConcrete ({1, 3, 5} : Finset ℕ)
#eval ST.rankFin NatTowerConcrete ({10} : Finset ℕ)
#eval ST.rankFin NatTowerConcrete (∅ : Finset ℕ)

end ST.Examples
