# Session 10 Assignments (Basic 5 + Challenge) — IUT1

## Basic Problems

### P01: Solving Linear Congruences
**Learning Objective**: Understand the conditions for the existence of solutions to linear congruences of the form ax ≡ b (mod n)  
**Problem Statement**: Prove that the solutions to 3x ≡ 6 (mod 9) are x ≡ 2, 5, 8 (mod 9).  
**Lean Goal**: `theorem linear_congruence_solutions : ∀ x : ZMod 9, (3 * x = 6) ↔ (x = 2 ∨ x = 5 ∨ x = 8)`  
**Hints**:
- Verify that gcd(3, 9) = 3 divides 6
- Substitute each potential solution to verify

### P02: Unique Solution to Linear Congruences
**Learning Objective**: Understand uniqueness when the coefficients and modulus are coprime  
**Problem Statement**: Prove that 5x ≡ 3 (mod 7) has exactly one solution, x ≡ 2 (mod 7).  
**Lean Goal**: `theorem unique_linear_solution : ∃! x : ZMod 7, 5 * x = 3`  
**Hints**:
- Since gcd(5, 7) = 1, the solution is unique
- Use `use 2` to provide the solution and demonstrate uniqueness

### P03: Determining Quadratic Residues
**Learning Objective**: Understand the concept of quadratic residues and non-residues  
**Problem Statement**: Show that 3 is a quadratic non-residue modulo 7. That is, prove that there is no integer x such that x² ≡ 3 (mod 7).  
**Lean Goal**: `theorem quadratic_nonresidue : ¬∃ x : ZMod 7, x^2 = 3`  
**Hints**:
- Compute all squares modulo 7 and observe that 3 never appears
- Use `Fin.decidableExistsFintype` for finite search

### P04: Fermat-Euler's Criterion
**Learning Objective**: Apply Euler's criterion to determine quadratic residues  
**Problem Statement**: For prime p = 11, show that 2^((11-1)/2) ≡ -1 (mod 11), thereby confirming that 2 is a quadratic non-residue modulo 11.  
**Lean Goal**: `theorem euler_criterion : (2 : ZMod 11)^5 = -1`  
**Hints**:
- Compute 2^5 = 32 ≡ -1 (mod 11)
- Use `norm_num` or `decide` to verify

### P05: Wilson's Theorem
**Learning Objective**: Understand this classical theorem characterizing prime numbers (history: first stated by Wilson in 1770, proven by Lagrange)  
**Problem Statement**: Verify that (p-1)! ≡ -1 (mod p) for p = 7. That is, prove 6! ≡ -1 (mod 7).  
**Lean Goal**: `theorem wilson_theorem_seven : (Finset.range 6).prod (fun i => ((i + 1) : ZMod 7)) = -1`  
**Hints**:
- Compute 6! = 720 = 7 × 103 - 1
- Use `Finset.prod_range_succ` to compute recursively

### Challenge Problems

### CH: Computation Using Quadratic Reciprocity Law
**Learning Objective**: Understand computational applications of Gauss's quadratic reciprocity law (history: first proved by Gauss in 1796)  
**Problem Statement**: Using the Legendre symbol, show that (3/7) = -1 and (7/3) = 1, thus verifying the quadratic reciprocity law: (3/7)(7/3) = (-1)^((3-1)(7-1)/4) = -1. Furthermore, prove that x² ≡ 3 (mod 7) has no solutions, while x² ≡ 7 (mod 3) ≡ 1 (mod 3) has solutions.  
**Lean Goal**: `theorem quadratic_reciprocity_example : (¬∃ x : ZMod 7, x^2 = 3) ∧ (∃ x : ZMod 3, x^2 = 1) ∧ (((3 : ℤ) * 7) % 4 = 1)`  
**Hints**:
- Note that (3-1)(7-1)/4 = 2·6/4 = 3, which is odd
- Clearly, 7 ≡ 1 (mod 3) is a quadratic residue

---

## Template for Submission Lean File (S10)

```lean
import Mathlib

namespace HW_IUT1_S10

-- P01: Solving Linear Congruences
theorem S10_P01 : ∀ x : ZMod 9, (3 * x = 6) ↔ (x = 2 ∨ x = 5 ∨ x = 8) := by
  sorry

-- P02: Unique Solution to Linear Congruences
theorem S10_P02 : ∃! x : ZMod 7, 5 * x = 3 := by
  sorry

-- P03: Determining Quadratic Residues
theorem S10_P03 : ¬∃ x : ZMod 7, x^2 = 3 := by
  sorry

-- P04: Fermat-Euler's Criterion
theorem S10_P04 : (2 : ZMod 11)^5 = -1 := by
  sorry

-- P05: Wilson's Theorem
theorem S10_P05 : (Finset.range 6).prod (fun i => ((i + 1) : ZMod 7)) = -1 := by
  sorry

-- CH: Computation Using Quadratic Reciprocity Law
theorem S10_CH : (¬∃ x : ZMod 7, x^2 = 3) ∧ 
    (∃ x : ZMod 3, x^2 = 1) ∧ 
    (((3 : ℤ) * 7) % 4 = 1) := by
  sorry

end HW_IUT1_S10
```

---

## Return Template

### 1) Summary
**Achievement Status**: [Pass/Needs Revision]  
**Overall Feedback**: For linear and quadratic congruences in Session 10, you demonstrated [X%] understanding of the material. Your strengths lie in [solving linear congruences/determining quadratic residues/classical theorems], whereas [computational aspects/theoretical foundations] require [further/additional] practice.

### 2) Automatic Check Results
- Build Status: [Success/Failure (with error message)]
- `sorry` Remaining: [None/Present (problem number)]  
- Type Consistency: [All consistent/inconsistent points]

### 3) Problem-Specific Feedback

**S10_P01** (10 points [?])
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Use `intro x` to expand universal quantification, then verify with `simp` and case analysis]
- Mathematical Perspective: Understanding of multiple solutions to linear congruences [clear/unclear]

**S10_P02** (10 points [?])
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Use `use 2` to provide the solution, then demonstrate uniqueness with `decide`]
- Mathematical Perspective: Understanding of unique solutions with coprime coefficients [strong/needs review]

**S10_P03** (10 points [?])
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Use `push_neg` to expand, then show x² ≠ 3 for all x]
- Mathematical Perspective: Understanding of quadratic non-residues [sufficient/insufficient]

**S10_P04** (10 points [?])
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Compute directly using `norm_num` or `decide`]
- Mathematical Perspective: Understanding of Fermat-Euler's criterion [certain/uncertain]

**S10_P05** (10 points [?])
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Expand using `simp [Finset.prod_range_succ]` and verify with `decide`]
- Mathematical Perspective: Understanding of Wilson's theorem [deep/superficial]

**S10_CH** (15 points [?])
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Separate the three conditions with `constructor` and prove each independently]
- Structural Insight: Understanding of both computational aspects and meaning of quadratic reciprocity [excellent/needs improvement]

### 4) Next Steps
1. **General Solution to Linear Congruences**: Extend to more complex polynomial congruences
2. **Historical Development Understanding**: Organize the contributions of Gauss, Euler, and Lagrange
3. **Preparation for Quadratic Forms**: Build foundation for extending quadratic aspects in Session 11


