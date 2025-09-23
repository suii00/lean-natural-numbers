We sincerely apologize for the error you pointed out. Indeed, the original problem contained a mathematical mistake. Below is the corrected version.

# Assignment 10 (Basic 5 + Challenge) — IUT1

## Basic Problems

### P01: Solving Linear Congruences
**Learning Objective**: Understand the conditions for the existence of solutions to linear congruences of the form ax ≡ b (mod n)  
**Problem Statement**: Prove that the solutions to 3x ≡ 6 (mod 9) are x ≡ 2, 5, 8 (mod 9).  
**Lean Objective**: `theorem linear_congruence_solutions : ∀ x : ZMod 9, (3 * x = 6) ↔ (x = 2 ∨ x = 5 ∨ x = 8)`  
**Hints**:
- Verify that gcd(3, 9) = 3 divides 6.
- Substitute each potential solution to verify correctness.

### P02: Unique Solution to Linear Congruences
**Learning Objective**: Understand uniqueness when the coefficients and modulus are coprime  
**Problem Statement**: Prove that 5x ≡ 3 (mod 7) has exactly one solution, x ≡ 2 (mod 7).  
**Lean Objective**: `theorem unique_linear_solution : ∃! x : ZMod 7, 5 * x = 3`  
**Hints**:
- Since gcd(5, 7) = 1, the solution is unique.
- Use `use 2` to provide the solution and demonstrate uniqueness.

### P03: Determining Quadratic Residues (Revised)
**Learning Objective**: Understand the concept of quadratic residues and non-residues  
**Problem Statement**: Show that 3 is a quadratic non-residue modulo 7. That is, prove that there is no integer x such that x² ≡ 3 (mod 7).  
**Lean Objective**: `theorem quadratic_nonresidue : ¬∃ x : ZMod 7, x^2 = 3`  
**Hints**:
- Only the numbers {0, 1, 2, 4} are square residues modulo 7.
- Use `Fin.decidableExistsFintype` to perform a finite search.

### P04: Fermat-Euler's Criterion (Revised)
**Learning Objective**: Apply Euler's criterion to determine quadratic residues  
**Problem Statement**: For prime p = 11, show that 2^((11-1)/2) = 2^5 ≡ -1 (mod 11), thereby confirming that 2 is a quadratic non-residue modulo 11.  
**Lean Objective**: `theorem euler_criterion : (2 : ZMod 11)^5 = -1`  
**Hints**:
- Calculate 2^5 = 32 ≡ -1 (mod 11).
- Use `norm_num` or `decide` to verify the result.

### P05: Wilson's Theorem
**Learning Objective**: Understand this classical theorem characterizing prime numbers (History: First stated by Wilson in 1770, proven by Lagrange)  
**Problem Statement**: Verify that (p-1)! ≡ -1 (mod p) for p = 7. That is, prove 6! ≡ -1 (mod 7).  
**Lean Objective**: `theorem wilson_theorem_seven : (Finset.range 6).prod (fun i => ((i + 1) : ZMod 7)) = -1`  
**Hints**:
- 6! = 720 = 7 × 103 - 1.
- Use `Finset.prod_range_succ` to compute recursively.

### Challenge Problems (Revised)

### CH: Computation Using Quadratic Reciprocity Law
**Learning Objective**: Understand computational applications of Gauss's quadratic reciprocity law (History: First proved by Gauss in 1796)  
**Problem Statement**: Using the Legendre symbol, show that (3/7) = -1 and (7/3) = 1, then verify the quadratic reciprocity law: (3/7)(7/3) = (-1)^((3-1)(7-1)/4) = (-1)^3 = -1. Furthermore, prove that x² ≡ 3 (mod 7) has no solutions, while x² ≡ 7 (mod 3) ≡ 1 (mod 3) has solutions.  
**Lean Objective**: `theorem quadratic_reciprocity_example : (¬∃ x : ZMod 7, x^2 = 3) ∧ (∃ x : ZMod 3, x^2 = 1) ∧ ((3 - 1) * (7 - 1) / 4 = 3)`  
**Hints**:
- Note that (3-1)(7-1)/4 = 2·6/4 = 3, which is odd.
- Clearly, 7 ≡ 1 (mod 3) is a quadratic residue.

---

## Template for Submission (S10) — Revised

```lean
import Mathlib

namespace HW_IUT1_S10

-- P01: Solving Linear Congruences
theorem S10_P01 : ∀ x : ZMod 9, (3 * x = 6) ↔ (x = 2 ∨ x = 5 ∨ x = 8) := by
  sorry

-- P02: Unique Solution to Linear Congruences
theorem S10_P02 : ∃! x : ZMod 7, 5 * x = 3 := by
  sorry

-- P03: Determining Quadratic Residues (Revised)
theorem S10_P03 : ¬∃ x : ZMod 7, x^2 = 3 := by
  sorry

-- P04: Fermat-Euler's Criterion (Revised)
theorem S10_P04 : (2 : ZMod 11)^5 = -1 := by
  sorry

-- P05: Wilson's Theorem
theorem S10_P05 : (Finset.range 6).prod (fun i => ((i + 1) : ZMod 7)) = -1 := by
  sorry

-- CH: Computation Using Quadratic Reciprocity Law (Revised)
theorem S10_CH : (¬∃ x : ZMod 7, x^2 = 3) ∧ 
    (∃ x : ZMod 3, x^2 = 1) ∧ 
    ((3 - 1) * (7 - 1) / 4 = 3) := by
  sorry

end HW_IUT1_S10
```

We sincerely apologize for the computational error you identified.
