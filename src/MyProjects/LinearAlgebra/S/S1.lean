import Mathlib

/-!
# S1: Basic planar linear algebra lemmas

This file collects small lemmas about two-dimensional vectors viewed as ordered pairs.
We connect the oriented area of two vectors with the determinant of a `2 x 2` matrix.
-/

namespace HW_S1

open Matrix
open Real
open scoped BigOperators

/-- Oriented area formed by two planar vectors. -/
def orient2D (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

/-- Parallelogram area determined by two planar vectors. -/
def parArea2D (u v : ℝ × ℝ) : ℝ := |orient2D u v|


/-! ## S1_P01
Elementary verification that a point on the graph of the affine function `x ↦ a * x + b`
satisfies the expected relation between its coordinates.
-/
theorem S1_P01 (a b x : ℝ) :
    (x, a * x + b).2 = a * (x, a * x + b).1 + b := by
  simp


/-! ## S1_P02
Given two distinct points in the plane, construct the slope-intercept form of the unique
line through them and verify that both points satisfy the resulting equation.
-/
theorem S1_P02 (p q : ℝ × ℝ) (h : p.1 ≠ q.1) :
    let m := (q.2 - p.2) / (q.1 - p.1)
    let b := p.2 - m * p.1
    (p.2 = m * p.1 + b) ∧ (q.2 = m * q.1 + b) := by
  classical
  set m := (q.2 - p.2) / (q.1 - p.1) with hm
  set b := p.2 - m * p.1 with hb
  have h₁ : q.1 - p.1 ≠ 0 := sub_ne_zero.mpr (ne_comm.mp h)
  suffices (p.2 = m * p.1 + b) ∧ (q.2 = m * q.1 + b) by
    simpa [hm, hb]
  constructor
  · simp [hb]
  ·
    have h' :
        ((q.2 - p.2) / (q.1 - p.1)) * q.1
            + (p.2 - ((q.2 - p.2) / (q.1 - p.1)) * p.1)
            = q.2 := by
      field_simp [h₁]
      ring
    have h'' : m * q.1 + b = q.2 := by
      simpa [hm, hb] using h'
    exact (eq_comm.mp h'')


/-! ## S1_P03
`orient2D` is additive in its first argument.
-/
theorem S1_P03 (u v w : ℝ × ℝ) :
    orient2D (u + w) v = orient2D u v + orient2D w v := by
  classical
  cases' u with ux uy
  cases' v with vx vy
  cases' w with wx wy
  have hx :
      (ux + wx) * vy - (uy + wy) * vx
        = (ux * vy - uy * vx) + (wx * vy - wy * vx) := by
    ring
  simp [orient2D, hx]


/-! ## S1_P04
Swapping the arguments of `orient2D` changes its sign.
-/
theorem S1_P04 (u v : ℝ × ℝ) :
    orient2D u v = - orient2D v u := by
  classical
  cases' u with ux uy
  cases' v with vx vy
  have hx : ux * vy - uy * vx = - (vx * uy - vy * ux) := by
    ring
  simp [orient2D, hx]


/-! ## S1_P05
Solving the affine equation `y = a * x + b` is equivalent to moving all terms to the left
and checking that the result is zero.
-/
theorem S1_P05 (a b x y : ℝ) :
    (y = a * x + b) ↔ (a * x - y + b = 0) := by
  constructor
  · intro hy
    subst hy
    ring
  · intro hy
    have hy1 := congrArg (fun t => t + y) hy
    simp [sub_eq_add_neg, add_comm, add_left_comm] at hy1
    have hy2 : y = b + a * x := hy1.symm
    have : y = a * x + b := by
      calc
        y = b + a * x := hy2
        _ = a * x + b := by simp [add_comm]
    exact this


/-! ## S1_CH
The parallelogram area agrees with the absolute value of the determinant of the
matrix whose rows are the given vectors.
-/
theorem S1_CH (u v : ℝ × ℝ) :
    parArea2D u v = |Matrix.det ![![u.1, u.2], ![v.1, v.2]]| := by
  classical
  simp [parArea2D, orient2D, Matrix.det_fin_two]


end HW_S1
