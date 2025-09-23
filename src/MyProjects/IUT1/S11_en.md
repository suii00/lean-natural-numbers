# Session 11 Assignments (Foundation 5 + Challenge) — IUT1

## Foundational Problems

### P01: Representation as a Quadratic Form
**Learning Objective**: Understand integer representations through quadratic forms  
**Problem Statement**: Demonstrate that the integer 13 can be expressed in the form x² + y². Prove specifically that 13 = 2² + 3².  
**Lean Objective**: `theorem sum_of_two_squares : ∃ (x y : ℤ), x^2 + y^2 = 13`  
**Hints**:
- Use `use 2, 3` or `use 3, 2` to provide a witness
- Use `norm_num` to verify computations

### P02: Solution to the Pell Equation
**Learning Objective**: Understand the fundamental solution to the Pell equation x² - Dy² = 1  
**Problem Statement**: Verify that the smallest solution to the equation x² - 2y² = 1 is (x, y) = (3, 2).  
**Lean Objective**: `theorem pell_equation_solution : (3 : ℤ)^2 - 2 * 2^2 = 1`  
**Hints**:
- Direct calculation: 9 - 8 = 1
- Use `norm_num` to verify

### P03: Concrete Example of the Four Squares Theorem
**Learning Objective**: Verify through example that any natural number can be expressed as the sum of four squares  
**Problem Statement**: Prove that 7 = 2² + 1² + 1² + 1².  
**Lean Objective**: `theorem four_squares_seven : ∃ (a b c d : ℤ), a^2 + b^2 + c^2 + d^2 = 7`  
**Hints**:
- Use `use 2, 1, 1, 1` to provide a witness
- Verify that 4 + 1 + 1 + 1 = 7

### P04: Norm of Gaussian Integers
**Learning Objective**: Understand properties of the norm function for Gaussian integers ℤ[i]  
**Problem Statement**: Show that the norm N(3 + 4i) = 3² + 4² = 25 for the Gaussian integer 3 + 4i, and verify that this is equal to 5².  
**Lean Objective**: `theorem gaussian_norm : Complex.normSq (3 + 4 * Complex.I) = 25`  
**Hints**:
- The definition of `Complex.normSq` is the sum of squares of real and imaginary parts
- Use `norm_num` to verify the computation

### P05: System of Quadratic Congruences
**Learning Objective**: Find solutions satisfying multiple quadratic congruences simultaneously  
**Problem Statement**: Demonstrate that the smallest positive integer x satisfying both x² ≡ 1 (mod 8) and x ≡ 3 (mod 5) is 3.  
**Lean Objective**: `theorem quadratic_system : (3 : ℤ)^2 % 8 = 1 ∧ 3 % 5 = 3`  
**Hints**:
- Verify that 3² = 9 ≡ 1 (mod 8)
- Use `norm_num` to verify both conditions

### Challenge Problems

### CH: Equivalence and Class Number of Binary Quadratic Forms
**Learning Objective**: Understand equivalence relations and classification by discriminant for binary quadratic forms  
**Problem Statement**: Show that the quadratic forms f(x,y) = x² + 5y² and g(x,y) = 2x² + 2xy + 3y² share the same discriminant -20. Furthermore, verify that both forms can represent the prime number p = 29. Specifically, prove that 29 = 2² + 5·1² = 2·3² + 2·3·1 + 3·1². This serves as an example where the class number for the discriminant -20 is 2.  
**Lean Objective**: `theorem binary_quadratic_forms : let disc_f := -20; let disc_g := -20; (disc_f = disc_g) ∧ (∃ (x y : ℤ), x^2 + 5*y^2 = 29) ∧ (∃ (u v : ℤ), 2*u^2 + 2*u*v + 3*v^2 = 29)`  
**Hints**:
- Discriminant: For f, b² - 4ac = 0 - 4·1·5 = -20
- For g, b² - 4ac = 4 - 4·2·3 = -20
- Note: 29 = 2² + 5·5² is incorrect; the correct form is 29 = 2² + 5·1²

---

## Template for Submission Lean File (S11)

```lean
import Mathlib

namespace HW_IUT1_S11

-- P01: Representation as a Quadratic Form
theorem S11_P01 : ∃ (x y : ℤ), x^2 + y^2 = 13 := by
  sorry

-- P02: Solution to the Pell Equation
theorem S11_P02 : (3 : ℤ)^2 - 2 * 2^2 = 1 := by
  sorry

-- P03: Concrete Example of the Four Squares Theorem
theorem S11_P03 : ∃ (a b c d : ℤ), a^2 + b^2 + c^2 + d^2 = 7 := by
  sorry

-- P04: Norm of Gaussian Integers
theorem S11_P04 : Complex.normSq (3 + 4 * Complex.I) = 25 := by
  sorry

-- P05: System of Quadratic Congruences
theorem S11_P05 : (3 : ℤ)^2 % 8 = 1 ∧ 3 % 5 = 3 := by
  sorry

-- CH: Equivalence and Class Number of Binary Quadratic Forms
theorem S11_CH : 
    let disc_f := -20
    let disc_g := -20
    (disc_f = disc_g) ∧ 
    (∃ (x y : ℤ), x^2 + 5*y^2 = 29) ∧ 
    (∃ (u v : ℤ), 2*u^2 + 2*u*v + 3*v^2 = 29) := by
  sorry

end HW_IUT1_S11
```

---

## Return Template

### 1) Summary
**Achievement Status**: [Pass/Needs Revision]  
**Overall Feedback**: Your understanding of the quadratic aspects expanded in Session 11 shows [completeness]%. Particularly, your grasp of [quadratic forms/Pell equations/Gaussian integers] is [excellent/insufficient], and further practice is needed in [computational aspects/theoretical foundations].

### 2) Automatic Check Results
- Build Status: [Success/Failure (with error details)]
- `sorry` Remaining: [None/Present (problem number)]  
- Type Consistency: [All consistent/inconsistent points]

### 3) Problem-Specific Feedback

**S11_P01** (10 points [?])
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Provide witness using `use 2, 3` or `use 3, 2`, then verify with `norm_num`]
- Mathematical Perspective: Understanding of square sum representation [clear/unclear]

**S11_P02** (10 points [?])
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Verify directly using `norm_num`]
- Mathematical Perspective: Comprehension of fundamental solution to the Pell equation [good/needs review]

**S11_P03** (10 points [?])
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Provide witness using `use 2, 1, 1, 1`]
- Mathematical Perspective: Understanding of the four squares theorem [sufficient/insufficient]

**S11_P04** (10 points [?])
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Verify computation using `norm_num` or `simp [Complex.normSq]`]
- Mathematical Perspective: Understanding of Gaussian integer structure [certain/uncertain]

**S11_P05** (10 points [?])
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Separate conditions using `constructor`, then verify each with `norm_num`]
- Mathematical Perspective: Understanding of multiple congruence conditions [deep/superficial]

**S11_CH** (15 points [?])
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: The discriminants equality is trivial; provide specific values for each expression using `use`]
- Structural Insight: Understanding of class theory for binary quadratic forms [excellent/needs improvement]

### 4) Next Steps
1. **General Theory of Quadratic Forms**: Deeper understanding of classification by discriminant and equivalence relations
2. **Preparation for Algebraic Number Theory**: Progress from Gaussian integers to the ring of integers of general quadratic fields
3. **Bridge to p-adic Perspective**: Preparation for local-global principles in Session 12-13 leading up to p-adic numbers
