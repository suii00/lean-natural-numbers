/-
# Complete API Discovery for Noether Correspondence
## Finding correct Mathlib 4 ideal theory APIs
-/

import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

-- Test basic ideal operations
#check Ideal
#check RingHom

-- Search for map/comap operations
#find map
#find comap

-- Check quotient construction
#check Ideal.Quotient
#check Ideal.Quotient.mk

-- Check available ideal operations
section TestIdealOps

variable {R : Type*} [CommRing R] (I J : Ideal R) (f : R →+* R)

#check I.map f
#check I.comap f
#check Ideal.map f I
#check Ideal.comap f J

-- Check quotient operations
#check R ⧸ I
#check Ideal.Quotient.mk I

-- Check prime and maximal
#check Ideal.IsPrime
#check Ideal.IsMaximal

end TestIdealOps

-- Search for membership lemmas
#find mem_map
#find mem_comap