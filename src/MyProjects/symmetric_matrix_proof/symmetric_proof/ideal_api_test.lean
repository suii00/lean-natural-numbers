import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Algebra.Module.Submodule.Map

-- Test the exact APIs that exist in current Mathlib

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) 
variable (I : Ideal R) (J : Ideal S)

-- Test each API
#check @Ideal.map_isPrime_of_surjective
#check @Ideal.IsPrime.comap
#check @Ideal.comap_isMaximal_of_surjective  
#check @Ideal.map_eq_top_or_isMaximal_of_surjective
#check @Submodule.mem_comap
#check @Ideal.map_isPrime_of_equiv
#check @Ideal.comap_isPrime

example [IsPrime J] : IsPrime (Ideal.comap f J) := by infer_instance
example (hf : Function.Surjective f) [IsMaximal J] : IsMaximal (Ideal.comap f J) := 
  Ideal.comap_isMaximal_of_surjective hf