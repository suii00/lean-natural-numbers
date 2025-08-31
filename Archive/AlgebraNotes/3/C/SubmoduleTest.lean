/-
# Test Submodule Approach for Ideal Theory
## Verify Submodule.mem_map availability
-/

import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic  
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Module.Submodule.Map

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (I : Ideal R) (J : Ideal S)

-- Test Submodule operations
#check Submodule.mem_map
#check Submodule.mem_comap

-- Test that Ideal inherits from Submodule
#check (I : Submodule R R)
#check Ideal.map f I
#check (Ideal.map f I : Submodule S S)

-- Test our key lemma
lemma ideal_mem_map_iff (s : S) :
    s ∈ Ideal.map f I ↔ ∃ r ∈ I, f r = s := by
  -- Use Submodule.mem_map since Ideal.map = Submodule.map
  rw [Ideal.map]
  exact Submodule.mem_map.symm