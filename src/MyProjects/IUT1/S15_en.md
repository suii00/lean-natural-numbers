# Session 15 Assignments (Foundations 5 + Challenges) — IUT1 Comprehensive Review

## Foundational Problems

### P01: The Bridge Between Ring Theory and Number Theory
**Learning Objective**: Understand how the structure theorems of rings determine number-theoretic properties  
**Problem Statement**: Since ℤ is a principal ideal domain, verify that for any non-zero ideal I, there exists some n ∈ ℤ such that I = (n). Furthermore, demonstrate how this property relates to the uniqueness of prime factorization.  
**Lean Goal**: `theorem Z_is_PID : ∀ I : Ideal ℤ, I ≠ ⊥ → ∃ n : ℤ, I = Ideal.span {n}`  
**Hints**:
- Subgroups of ℤ are of the form nℤ
- Utilize the well-ordering principle

### P02: From Local to Global Properties
**Learning Objective**: Comprehend the principle of reconstructing global properties from local ones  
**Problem Statement**: Prove that if integers a and b satisfy a ≡ b (mod p) for all primes p, then a = b. This can be regarded as a limiting version of the Chinese Remainder Theorem.  
**Lean Goal**: `theorem local_to_global : ∀ a b : ℤ, (∀ p : ℕ, Nat.Prime p → (a : ZMod p) = b) → a = b`  
**Hints**:
- a - b is divisible by every prime
- The only integer satisfying this condition is 0

### P03: The Significance of p-adic Completeness
**Learning Objective**: Understand how different completion of ℚ yield distinct mathematical structures  
**Problem Statement**: Verify that x² = 2 has no solution in ℚ but does have a solution in ℚ₇. Specifically, starting with 3² ≡ 2 (mod 7), demonstrate the existence of a solution in ℚ₇ using Hensel's Lemma.  
**Lean Goal**: `theorem sqrt_two_in_Q7 : (3 : ZMod 7)^2 = 2 ∧ ∃ f : ℕ → ZMod 7, (∀ n, f (n+1) % 7 = f n) ∧ (∀ n, (f n)^2 = 2)`  
**Hints**:
- Apply Hensel's Lemma iteratively
- Construct a coherent sequence

### P04: A Unified Perspective on Cyclotomic Fields
**Learning Objective**: Recognize that cyclotomic fields are central objects in algebraic number theory  
**Problem Statement**: For the cyclotomic polynomial Φₙ(X), verify that its degree is φ(n) by considering the case n = 12. Show that Φ₁₂(X) = X⁴ - X² + 1, and demonstrate that deg Φ₁₂ = 4 = φ(12).  
**Lean Goal**: `theorem cyclotomic_degree_12 : Polynomial.degree (cyclotomic 12 ℚ) = 4`  
**Hints**:
- Calculate φ(12) = φ(4·3) = φ(4)·φ(3) = 2·2 = 4
- Compute using the inclusion-exclusion principle

### P05: Preview of Class Field Theory
**Learning Objective**: Foreshadow the correspondence between abelian extensions and congruence subgroups  
**Problem Statement**: In ℚ(√-5), prove that 2 is not a prime element. Specifically, while 2 = (1 + √-5)(1 - √-5)/3 does not hold, verify that 6 = 2·3 = (1 + √-5)(1 - √-5).  
**Lean Goal**: `theorem non_UFD_example : ∃ (α β : ℤ[√-5]), α * β = 6 ∧ ¬IsPrime α ∧ ¬IsPrime β ∧ ¬IsUnit α ∧ ¬IsUnit β`  
**Hints**:
- Use the norm N(a + b√-5) = a² + 5b²
- Examine the two possible factorizations of 6

### Challenge Problems

### CH: Introduction to IUT Theory
**Learning Objective**: Comprehend the number-theoretic phenomena motivating the Inter-Universal Teichmüller Theory  
**Problem Statement**: Consider a special case of the abc conjecture. For a = 1, b = 2ⁿ - 1, c = 2ⁿ, prove the following:
1. Verify that gcd(a, b) = 1
2. Evaluate rad(abc) = rad(2ⁿ(2ⁿ-1))
3. Demonstrate that c < rad(abc)² holds in many cases
4. However, show that there exist infinitely many n for which c > rad(abc)^(1+ε)

Discuss how this phenomenon illustrates the "entanglement between addition and multiplication," which is the central problem addressed by IUT theory.

**Lean Goal**: `theorem abc_special_case : ∃ n : ℕ, let a := 1; let b := 2^n - 1; let c := 2^n; Nat.Coprime a b ∧ c < (Finset.prod (Finset.filter Nat.Prime (Finset.range (a*b*c + 1))) id)^2`  
**Hints**:
- rad is the product of prime factors (ignoring multiplicities)
- The prime factors of 2^n - 1 depend on n

---

## Template for Submission Lean File (S15)

```lean
import Mathlib

namespace HW_IUT1_S15

-- P01: The Bridge Between Ring Theory and Number Theory
theorem S15_P01 : ∀ I : Ideal ℤ, I ≠ ⊥ → ∃ n : ℤ, I = Ideal.span {n} := by
  sorry

-- P02: From Local to Global Properties
theorem S15_P02 : ∀ a b : ℤ, 
    (∀ p : ℕ, Nat.Prime p → (a : ZMod p) = b) → a = b := by
  sorry

-- P03: The Significance of p-adic Completeness
theorem S15_P03 : (3 : ZMod 7)^2 = 2 ∧ 
    ∃ f : ℕ → ZMod 7, (∀ n, f (n+1) % 7 = f n) ∧ (∀ n, (f n)^2 = 2) := by
  sorry

-- P04: A Unified Perspective on Cyclotomic Fields
theorem S15_P04 : Polynomial.degree (cyclotomic 12 ℚ) = 4 := by
  sorry

-- P05: Preview of Class Field Theory (Simplified Version)
theorem S15_P05 : ∃ (a b : ℤ), 
    (a^2 + 5*b^2 = 6) ∧ (a ≠ ±1 ∨ b ≠ 0) ∧ (a ≠ ±2 ∨ b ≠ 0) ∧ (a ≠ ±3 ∨ b ≠ 0) := by
  sorry

-- CH: Introduction to IUT Theory
theorem S15_CH : ∃ n : ℕ, 
    let a := 1
    let b := 2^n - 1
    let c := 2^n
    Nat.Coprime a b ∧ 
    c < (Finset.prod (Finset.filter Nat.Prime (Finset.range (a*b*c + 1))) id)^2 := by
  sorry

end HW_IUT1_S15
```

---

## Return Template

### 1) Summary
**Achievement Status**: [Pass/Needs Revision]  
**Overall Feedback**: Throughout the IUT1 course, I have achieved [X%] level of understanding, progressing from foundational ring theory through p-adic number theory to perspectives on modern number theory. My [theoretical comprehension/computational skills/formalization abilities] have developed [remarkably/steadily].

### 2) Automatic Check Results
- Build Status: [Success/Failure (with error details)]
- `sorry` Remaining: [None/Present (problem number)]  
- Type Consistency: [All consistent/inconsistent points]

### 3) Problem-Specific Feedback

**S15_P01** (10 points [?] points)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Use `Submodule.isPrincipal`]
- Mathematical Perspective: Essential understanding of principal ideal domains [clear/unclear]

**S15_P02** (10 points [?] points)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Derive from uniqueness of prime factorization]
- Mathematical Perspective: Grasp of the local-global principle [strong/needs review]

**S15_P03** (10 points [?] points)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Indicate iterative application of Hensel's Lemma]
- Mathematical Perspective: Understanding of p-adic completion significance [sufficient/insufficient]

**S15_P04** (10 points [?] points)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Use `Polynomial.degree_cyclotomic`]
- Mathematical Perspective: Structure understanding of cyclotomic fields [certain/uncertain]

**S15_P05** (10 points [?] points)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Provide concrete factorization]
- Mathematical Perspective: Understanding of non-UFDs [deep/superficial]

**S15_CH** (15 points [?] points)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Construct examples for small n]
- Structural Insight: Perspective on the abc conjecture and IUT theory [excellent/needs improvement]

### 4) Overall Course Evaluation
1. **Acquired Skills**: Ability to apply abstract concepts from ring theory to concrete number-theoretic problems
2. **Areas of Growth**: Refinement of formalization rigor and critical thinking skills
3. **Future Prospects**: Preparation for tackling IUT theory proper and advancement to more advanced number theory
