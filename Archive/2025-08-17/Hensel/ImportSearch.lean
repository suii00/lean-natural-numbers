import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Polynomial.Derivative
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Algebra.Ring.IsCoprime
import Mathlib.RingTheory.Polynomial.Basic

open Polynomial ZMod

-- 必要な関数や定理を検索
#check Nat.factorization
#check Int.natAbs
#check Polynomial.map
#check Int.castRingHom
#check Polynomial.derivative
#check ZMod.castHom
#check pow_dvd_pow
#check IsCoprime
#check Polynomial.eval₂
#check List.Pairwise
#check List.prod

-- Nat.Coprime
#check Nat.Coprime

-- factorization関連
#find Nat.factorization

-- ZMod関連
#find ZMod.castHom
#find ZMod.cast

-- Polynomial関連
#find Polynomial.map
#find Polynomial.derivative
#find Polynomial.eval₂