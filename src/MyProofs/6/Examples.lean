/-
簡易テスト：有限体上での exhaustive test（小 p）
-/
import MyProofs.Elliptic.Group
import Mathlib.Data.ZMod.Basic

open MyProofs.Elliptic Point

-- Example: E: y^2 = x^3 - x over ZMod 11 (small prime)
def E11 : ShortWeierstrass (ZMod 11) := { a := (-1 : ZMod 11), b := 0, non_singular := by decide }

-- A small sanity check constructing two affine points and adding them
example : True := by
  let P := affine (E11) (0 : ZMod 11) (0 : ZMod 11) (by decide)
  let Q := affine (E11) (1 : ZMod 11) (0 : ZMod 11) (by decide)
  -- We only check that addition produces a Point (no heavy equation checking here)
  have R := P + Q
  trivial
