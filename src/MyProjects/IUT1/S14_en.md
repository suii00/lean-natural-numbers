# Session 14 Assignments (Foundation 5 + Challenge) — IUT1

## Foundational Problems

### P01: Special Values of p-adic L-Functions
**Learning Objective**: Understand fundamental properties of p-adic L-functions  
**Problem Statement**: Consider special values of the p-adic analogue of the Riemann zeta function at ζₚ(2). For p = 5, verify that (1 - 5²)ζ(2) = (1 - 25)·π²/6 = -4π² can be interpreted p-adically. Specifically, demonstrate that 1 - 5² = -24 is a 5-adic unit.  
**Lean Goal**: `theorem padic_L_preparation : IsUnit (-24 : ZMod 125) ∧ Nat.Coprime 24 5`  
**Hints**:
- Verify that gcd(24, 5) = 1
- Construct the 5-adic inverse of -24

### P02: Kummer's Congruences
**Learning Objective**: Understand the relationship between Bernoulli numbers and p-adic properties  
**Problem Statement**: As a fundamental case of Kummer's congruences for Bernoulli numbers, examine the condition under which (1 - 2ⁿ)Bₙ/n becomes a p-adic integer. For n = 4 and p = 5, show that (1 - 16)·(-1/30)/4 is not a 5-adic integer when B₄ = -1/30.  
**Lean Goal**: `theorem kummer_congruence_check : padicNorm 5 (15/120 : ℚ) = 5`  
**Hints**:
- Recognize that 15/120 = 1/8, and v₅(1/8) = -1
- |1/8|₅ = 5

### P03: Local Zeta Functions
**Learning Objective**: Understand zeta functions of varieties over finite fields  
**Problem Statement**: Verify that the number of points on the projective line ℙ¹(𝔽₅) over 𝔽₅ is 6, and demonstrate that the numerator of the zeta function Z(t) = (1-t)⁻¹(1-5t)⁻¹ is 1 - 6t + 5t².  
**Lean Goal**: `theorem projective_line_count : Fintype.card (Fin 5 × Option Unit) = 6`  
**Hints**:
- ℙ¹(𝔽₅) = 𝔽₅ ∪ {∞}
- Number of points = 5 + 1 = 6

### P04: p-adic Measures
**Learning Objective**: Understand basic concepts of p-adic measures  
**Problem Statement**: Verify that the measure of the compact open set a + 5ⁿℤ₅ in ℤ₅ is 5⁻ⁿ. For n = 3, show that the measure of the set 2 + 125ℤ₅ is 1/125.  
**Lean Goal**: `theorem padic_measure : (5 : ℚ)^(-3 : ℤ) = 1/125`  
**Hints**:
- Apply the normalization of Haar measure
- Recall that the measure μ(a + pⁿℤₚ) = p⁻ⁿ

### P05: p-adic Interpolation
**Learning Objective**: Understand p-adic interpolation of continuous functions  
**Problem Statement**: Consider the p-adic interpolation of the factorial function n!. Since by Wilson's theorem we have (p-1)! ≡ -1 (mod p), verify p-adically that 4! = 24 ≡ -1 (mod 5), and show that 24 + 1 = 25 is divisible by 5².  
**Lean Goal**: `theorem wilson_padic : (24 : ℤ) % 5 = 4 ∧ (25 : ℤ) % 25 = 0`  
**Hints**:
- 24 = 5·5 - 1 ≡ -1 (mod 5)
- 25 = 5²

### Challenge Problems

### CH: Introduction to Iwasawa Theory
**Learning Objective**: Understand the relationship between p-adic L-functions of cyclotomic fields and class numbers  
**Problem Statement**: For p = 5 and cyclotomic field ℚ(ζ₅), prove the following:
1. [ℚ(ζ₅) : ℚ] = φ(5) = 4
2. 1 + ζ₅ + ζ₅² + ζ₅³ + ζ₅⁴ = 0 (property of roots of the cyclotomic polynomial)
3. The unit group in ℤ[ζ₅] is larger than ±ζ₅ᵏ for k = 0,1,2,3,4
4. Given that the class number h(ℚ(ζ₅)) = 1, demonstrate that ℤ[ζ₅] is a principal ideal domain  

Explain how these properties relate to the special values of the p-adic L-function Lₚ(s, χ).  
**Lean Goal**: `theorem cyclotomic_properties : (Nat.totient 5 = 4) ∧ (∃ (ζ : ℂ), ζ^5 = 1 ∧ ζ ≠ 1 ∧ 1 + ζ + ζ^2 + ζ^3 + ζ^4 = 0) ∧ (IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ))`  
**Hints**:
- Φ₅(X) = 1 + X + X² + X³ + X⁴
- Related to Fermat's Little Theorem

---

## Template for Submission Lean File (S14)

```lean
import Mathlib

namespace HW_IUT1_S14

-- P01: Special Values of p-adic L-Functions
theorem S14_P01 : IsUnit (-24 : ZMod 125) ∧ Nat.Coprime 24 5 := by
  sorry

-- P02: Kummer's Congruences
theorem S14_P02 : padicNorm 5 (15/120 : ℚ) = 5 := by
  sorry

-- P03: Local Zeta Functions
theorem S14_P03 : Fintype.card (Fin 5 × Option Unit) = 6 := by
  sorry

-- P04: p-adic Measures
theorem S14_P04 : (5 : ℚ)^(-3 : ℤ) = 1/125 := by
  sorry

-- P05: p-adic Interpolation
theorem S14_P05 : (24 : ℤ) % 5 = 4 ∧ (25 : ℤ) % 25 = 0 := by
  sorry

-- CH: Introduction to Iwasawa Theory
theorem S14_CH : 
    (Nat.totient 5 = 4) ∧ 
    (∃ (ζ : ℂ), ζ^5 = 1 ∧ ζ ≠ 1 ∧ 1 + ζ + ζ^2 + ζ^3 + ζ^4 = 0) ∧ 
    (IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ)) := by
  sorry

end HW_IUT1_S14
```

---

## Return Template

### 1) Summary
**Achievement Status**: [Pass/Needs Revision]  
**Overall Feedback**: For Session 14's applications of p-adic numbers, you demonstrated [percentage]% understanding. Particularly, your grasp of [p-adic L-functions/local zeta/Iwasawa theory] is [strong/weak], and further proficiency is needed in [applied aspects/theoretical depth].

### 2) Automatic Check Results
- Build Status: [Success/Failure (with error details)]
- `sorry` Remaining: [None/Present (problem number)]  
- Type Consistency: [All consistent/inconsistent points]

### 3) Problem-Specific Feedback

**S14_P01** (10 points, [?] points earned)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Separate both conditions using `constructor` and verify with `decide`]
- Mathematical Perspective: Understanding of p-adic L-function fundamentals [clear/unclear]

**S14_P02** (10 points, [?] points earned)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Simplify 15/120 and compute the p-adic norm]
- Mathematical Perspective: Comprehension of Kummer congruences [good/needs review]

**S14_P03** (10 points, [?] points earned)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Use `Fintype.card_prod` and `Fintype.card_option`]
- Mathematical Perspective: Understanding of local zeta functions [adequate/inadequate]

**S14_P04** (10 points, [?] points earned)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Compute using `zpow_neg` and `norm_num`]
- Mathematical Perspective: Understanding of p-adic measures [certain/uncertain]

**S14_P05** (10 points, [?] points earned)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Verify each condition with `decide`]
- Mathematical Perspective: Conceptual understanding of p-adic interpolation [deep/superficial]

**S14_CH** (15 points, [?] points earned)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Prove each condition separately, using properties of cyclotomic polynomials]
- Structural Insight: Understanding of foundational concepts in Iwasawa theory [excellent/needs improvement]

### 4) Next Steps
1. **Deepening p-adic L-Functions**: Clarify the relationship with the Riemann zeta function
2. **Path to Iwasawa Main Conjecture**: Understand connections with the class number formula
3. **Preparation for Summary**: Synthesize the path from ring theory to number theory in Session 15
