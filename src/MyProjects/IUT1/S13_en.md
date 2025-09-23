# Session 13 Assignments (Foundations 5 + Challenges) — IUT1

## Foundational Problems

### P01: p-adic Convergence
**Learning Objective**: Understand convergence of sequences in the p-adic norm
**Problem Statement**: Prove that the sequence aₙ = 1 + 5 + 5² + ... + 5ⁿ converges under the 5-adic norm. Specifically, verify that |aₙ₊₁ - aₙ|₅ = |5ⁿ⁺¹|₅ = 5⁻⁽ⁿ⁺¹⁾ → 0.
**Lean Goal**: `theorem padic_convergence (n : ℕ) : padicNorm 5 (5^(n+1) : ℚ) = (5 : ℚ)^(-(n+1 : ℤ))`
**Hints**:
- aₙ₊₁ - aₙ = 5ⁿ⁺¹
- |5ⁿ⁺¹|₅ = 5⁻⁽ⁿ⁺¹⁾

### P02: Characterization of p-adic Integers
**Learning Objective**: Understand the set ℤₚ = {x ∈ ℚₚ : |x|ₚ ≤ 1}
**Problem Statement**: Demonstrate that the rational number 2/3 is a 5-adic integer (i.e., |2/3|₅ ≤ 1), and prove that 1/5 is not a 5-adic integer (i.e., |1/5|₅ > 1).
**Lean Goal**: `theorem padic_integer_criterion : padicNorm 5 (2/3 : ℚ) ≤ 1 ∧ padicNorm 5 (1/5 : ℚ) > 1`
**Hints**:
- Since gcd(2,5) = 1 and gcd(3,5) = 1, we have |2/3|₅ = 1
- |1/5|₅ = 5

### P03: Solution of p-adic Equations
**Learning Objective**: Solve equations p-adically
**Problem Statement**: Show that x² = -1 has a solution in the 5-adic number field ℚ₅. Specifically, verify that x ≡ 2 (mod 5) satisfies x² ≡ -1 (mod 5) and can be extended to a solution to ℚ₅.
**Lean Goal**: `theorem padic_sqrt_minus_one : (2 : ZMod 5)^2 = -1 ∧ ∃ x : ZMod 25, x^2 = -1`
**Hints**:
- 2² = 4 ≡ -1 (mod 5)
- By Hensel's Lemma, this solution can be lifted to mod 5ⁿ

### P04: Strong Triangle Inequality
**Learning Objective**: Understand the ultrametric property of the p-adic norm
**Problem Statement**: Verify that the p-adic norm satisfies the strong triangle inequality |x + y|ₚ ≤ max{|x|ₚ, |y|ₚ} for the case x = 15, y = 10, and p = 5.
**Lean Goal**: `theorem ultrametric_inequality : padicNorm 5 (15 + 10 : ℚ) ≤ max (padicNorm 5 15) (padicNorm 5 10)`
**Hints**:
- |25|₅ = 1/25, |15|₅ = 1/5, |10|₅ = 1/5
- 1/25 ≤ max(1/5, 1/5) = 1/5

### P05: Existence Conditions for p-adic Logarithms
**Learning Objective**: Understand the conditions under which p-adic logarithms are defined
**Problem Statement**: Verify that 1 + p has a p-adic logarithm in ℤₚ. Specifically, when p = 5, show that |1 + 5 - 1|₅ = |5|₅ < 1.
**Lean Goal**: `theorem padic_log_domain : padicNorm 5 (5 : ℚ) < 1`
**Hints**:
- The p-adic logarithm log_p(1 + x) converges when |x|ₚ < 1
- |5|₅ = 1/5 < 1

### Challenge Problems

### CH: Local-Global Principle Example
**Learning Objective**: Understand the local-global principle (Hasse principle) for quadratic forms
**Problem Statement**: Verify that the equation x² + y² = 3 has a solution in both the real numbers ℝ and all p-adic number fields ℚₚ for primes p. Specifically,:
1. Existence in ℝ: The solution (√3, 0) exists
2. Existence in 2-adic: x ≡ 1, y ≡ 1 (mod 2) implies 1² + 1² ≡ 2 ≡ 0 (mod 2), which is incorrect. The correct solution is x ≡ 1, y ≡ 1 (mod 4) with 1² + 1² = 2 ≠ 3
3. Existence in 3-adic: The solution x ≡ 0, y ≡ 0 (mod 3) satisfies 0² + 0² ≡ 0 ≡ 3 (mod 3)
4. Existence for other odd primes p

Explain how the existence of solutions in these fields implies the existence of rational solutions. Note that in this case, no rational solution actually exists: this serves as a counterexample to the Hasse principle.
**Lean Goal**: `theorem local_global_counterexample : 
    (∃ x y : ℝ, x^2 + y^2 = 3) ∧ 
    (∃ x y : ZMod 8, x^2 + y^2 = 3) ∧ 
    (∃ x y : ZMod 3, x^2 + y^2 = 0) ∧ 
    (¬∃ x y : ℚ, x^2 + y^2 = 3)`
**Hints**:
- Considering modulo 4, only squares are 0 and 1
- It is impossible for x² + y² ≡ 3 (mod 4), demonstrating the non-existence of rational solutions

---

## Template for Submission Lean File (S13)

```lean
import Mathlib

namespace HW_IUT1_S13

-- P01: p-adic Convergence
theorem S13_P01 (n : ℕ) : padicNorm 5 (5^(n+1) : ℚ) = (5 : ℚ)^(-(n+1 : ℤ)) := by
  sorry

-- P02: Characterization of p-adic Integers
theorem S13_P02 : padicNorm 5 (2/3 : ℚ) ≤ 1 ∧ padicNorm 5 (1/5 : ℚ) > 1 := by
  sorry

-- P03: Solution of p-adic Equations
theorem S13_P03 : (2 : ZMod 5)^2 = -1 ∧ ∃ x : ZMod 25, x^2 = -1 := by
  sorry

-- P04: Strong Triangle Inequality
theorem S13_P04 : padicNorm 5 (15 + 10 : ℚ) ≤ max (padicNorm 5 15) (padicNorm 5 10) := by
  sorry

-- P05: Existence Conditions for p-adic Logarithms
theorem S13_P05 : padicNorm 5 (5 : ℚ) < 1 := by
  sorry

-- CH: Local-Global Principle Example (Hasse principle counterexample)
theorem S13_CH : 
    (∃ x y : ℝ, x^2 + y^2 = 3) ∧ 
    (∃ x y : ZMod 8, x^2 + y^2 = 3) ∧ 
    (∃ x y : ZMod 3, x^2 + y^2 = 0) ∧ 
    (¬∃ x y : ℚ, x^2 + y^2 = 3) := by
  sorry

end HW_IUT1_S13
```

---

## Return Template

### 1) Summary
**Performance**: [Pass/Needs Revision]
**Overall Feedback**: Your understanding of p-adic numbers in Session 13 shows [X%] mastery. Particularly strong/weak areas include [p-adic convergence/p-adic integers/local-global principle], with [theoretical aspects/computational techniques] requiring [further/additional] practice.

### 2) Automatic Check Results
- Build Status: [Success/Failure (with error message)]
- `sorry` Remaining: [None/Present (problem number)]
- Type Consistency: [All consistent/inconsistent points]

### 3) Problem-Specific Feedback

**S13_P01** (10 points, [?] points earned)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Use `padicNorm.norm_p_pow`]
- Mathematical Perspective: Understanding of p-adic convergence concept [clear/unclear]

**S13_P02** (10 points, [?] points earned)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Compute from p-adic valuations of numerator and denominator]
- Mathematical Perspective: Understanding of p-adic integer characterization [strong/needs review]

**S13_P03** (10 points, [?] points earned)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Separate both conditions using `constructor` and construct existence proof with `use`]
- Mathematical Perspective: Understanding of p-adic equation solutions [sufficient/insufficient]

**S13_P04** (10 points, [?] points earned)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Use `padicNorm.nonarchimedean` or compute directly]
- Mathematical Perspective: Understanding of ultrametric property [certain/uncertain]

**S13_P05** (10 points, [?] points earned)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Directly demonstrate using `padicNorm.norm_p`]
- Mathematical Perspective: Understanding of p-adic analysis fundamentals [deep/superficial]

**S13_CH** (15 points, [?] points earned)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Prove each condition separately; rational solution non-existence via modulo 4 argument]
- Structural Insight: Understanding of Hasse principle and its limitations [excellent/needs improvement]

### 4) Next Steps
1. **Preparation for p-adic L-functions**: Apply p-adic analytic techniques to p-adic interpolation of L-functions
2. **Bridge to Iwasawa Theory**: Connect p-adic representations to Galois group actions
3. **Preparation for Synthesis**: Organize applications of p-adic methods in Sessions 14-15
