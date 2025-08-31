/-
# Test Operations.lean API
## Verify what functions are available
-/

import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic  
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Operations

variable {R : Type*} [CommRing R] (I J : Ideal R) (f : R →+* R)

-- Test comap availability
#check Ideal.comap
#check I.comap f

-- Test map availability  
#check Ideal.map
#check I.map f

-- Test quotient operations
#check R ⧸ I
#check Ideal.Quotient.mk I

-- Test membership lemmas
#check Ideal.mem_comap
#check Ideal.mem_map

-- Test prime/maximal
#check Ideal.IsPrime
#check Ideal.IsMaximal