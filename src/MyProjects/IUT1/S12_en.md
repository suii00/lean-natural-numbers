# Session 12 Assignments (Foundations 5 + Challenges) — IUT1

## Foundational Problems

### P01: Calculating p-adic Valuations
**Learning Objective**: Compute the p-adic valuation of integers  
**Problem Statement**: Prove that for the integer 360 = 2³ × 3² × 5, the 2-adic valuation v₂(360) = 3, 3-adic valuation v₃(360) = 2, and 5-adic valuation v₅(360) = 1.  
**Lean Objective**: `theorem padic_valuation_360 : padicValNat 2 360 = 3 ∧ padicValNat 3 360 = 2 ∧ padicValNat 5 360 = 1`  
**Hints**:
- `padicValNat p n` represents the maximum number of times n can be divided by p
- Can be computed using `norm_num`

### P02: Properties of p-adic Norms
**Learning Objective**: Understand fundamental properties of p-adic norms  
**Problem Statement**: For the 5-adic norm, demonstrate that |25|₅ = 1/25. In general, |p^n|ₚ = p^(-n).  
**Lean Objective**: `theorem padic_norm_25 : padicNorm 5 25 = 1 / 25`  
**Hints**:
- Since 25 = 5², v₅(25) = 2
- |25|₅ = 5^(-2) = 1/25

### P03: Calculating p-adic Distances
**Learning Objective**: Comprehend how p-adic distances differ from standard distances  
**Problem Statement**: For the 3-adic distance, prove that d₃(26, 35) = |26 - 35|₃ = |9|₃ = 1/9.  
**Lean Objective**: `theorem padic_distance : padicNorm 3 (26 - 35) = 1 / 9`  
**Hints**:
- 26 - 35 = -9 = -3²
- |-9|₃ = |9|₃ = 3^(-2)

### P04: First Terms of p-adic Expansions
**Learning Objective**: Understand p-adic expansions of integers  
**Problem Statement**: For the integer 17, show that the first three digits in its 3-adic expansion are 17 = 1 + 2×3 + 2×3² + ... In other words, verify that 17 ≡ 1 (mod 3), 17 ≡ 7 (mod 9), and 17 ≡ 25 (mod 27).  
**Lean Objective**: `theorem padic_expansion_17 : 17 % 3 = 1 ∧ 17 % 9 = 8 ∧ 17 % 27 = 17`  
**Hints**:
- Correction: 17 = 1×3⁰ + 2×3¹ + 2×3² = 1 + 6 + 18 = 25 is incorrect
- Correct expansion: 17 = 2×3⁰ + 2×3¹ + 1×3² = 2 + 6 + 9 = 17

### P05: Preparation for Hensel's Lemma
**Learning Objective**: Understand the principle of constructing true solutions from p-adically close solutions  
**Problem Statement**: From the solution x ≡ 3 (mod 7) for x² ≡ 2 (mod 7), verify that we can construct a solution for x² ≡ 2 (mod 49). Specifically demonstrate that x = 10 is a solution.  
**Lean Objective**: `theorem hensel_lifting : (3 : ℤ)^2 % 7 = 2 ∧ (10 : ℤ)^2 % 49 = 2`  
**Hints**:
- 3² = 9 ≡ 2 (mod 7)
- Since 10 = 3 + 7×1, we have 10² = 100 = 2×49 + 2

### Challenge Problems

### CH: Density of p-adic Integers
**Learning Objective**: Understand the structure and density of ℤₚ within ℚₚ  
**Problem Statement**: For the 5-adic integers ℤ₅, prove that 2 is a unit (invertible element) and its inverse's 3-adic expansion's first three digits are 3 + 2×5 + 2×5² (mod 125). That is, demonstrate 2×63 ≡ 1 (mod 125) and explain that this implies 2⁻¹ ∈ ℤ₅.  
**Lean Objective**: `theorem padic_unit_inverse : (2 : ZMod 125) * 63 = 1 ∧ Nat.Coprime 2 5 ∧ ∃ (u : (ZMod 5)ˣ), (u : ZMod 5) = 2`  
**Hints**:
- Since gcd(2, 5) = 1, 2 is a unit in ℤ₅
- 2×63 = 126 = 125 + 1 ≡ 1 (mod 125)
- Higher-order terms are determined recursively

---

## Template for Submission Lean File (S12)

```lean
import Mathlib

namespace HW_IUT1_S12

-- P01: Calculating p-adic valuations
theorem S12_P01 : padicValNat 2 360 = 3 ∧ padicValNat 3 360 = 2 ∧ padicValNat 5 360 = 1 := by
  sorry

-- P02: Properties of p-adic norms
theorem S12_P02 : padicNorm 5 25 = 1 / 25 := by
  sorry

-- P03: Calculating p-adic distances
theorem S12_P03 : padicNorm 3 (26 - 35 : ℤ) = 1 / 9 := by
  sorry

-- P04: First terms of p-adic expansions (revised)
theorem S12_P04 : 17 % 3 = 2 ∧ 17 % 9 = 8 ∧ 17 % 27 = 17 := by
  sorry

-- P05: Preparation for Hensel's Lemma
theorem S12_P05 : (3 : ℤ)^2 % 7 = 2 ∧ (10 : ℤ)^2 % 49 = 2 := by
  sorry

-- CH: Density of p-adic integers
theorem S12_CH : (2 : ZMod 125) * 63 = 1 ∧ 
    Nat.Coprime 2 5 ∧ 
    ∃ (u : (ZMod 5)ˣ), (u : ZMod 5) = 2 := by
  sorry

end HW_IUT1_S12
```

---

## Return Template

### 1) Summary
**Achievement Status**: [Pass/Needs Revision]  
**Overall Feedback**: Your understanding of p-adic numbers in Session 12 demonstrates [X%] comprehension. Specific strengths/weaknesses include: [p-adic valuations/p-adic norms/p-adic expansions] requiring [stronger/weaker] development in [computational aspects/conceptual understanding].

### 2) Automatic Check Results
- Build Status: [Success/Failure (with error details)]
- `sorry` Remaining: [None/Present (problem number)]  
- Type Consistency: [Fully consistent/inconsistent areas]

### 3) Problem-Specific Feedback

**S12_P01** (10 points [?] points)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Separate each valuation using `constructor` and verify with `norm_num` or `decide`]
- Mathematical Perspective: Clarity of understanding p-adic valuation definition [Clear/Unclear]

**S12_P02** (10 points [?] points)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Use `padicNorm.eq_zpow_of_nonzero` or compute directly]
- Mathematical Perspective: Understanding of fundamental properties of p-adic norms [Strong/Needs review]

**S12_P03** (10 points [?] points)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Compute the difference first before applying the norm]
- Mathematical Perspective: Understanding of non-Archimedean nature of p-adic distances [Satisfactory/Insufficient]

**S12_P04** (10 points [?] points)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Compute each residue using `decide`]
- Mathematical Perspective: Understanding of p-adic expansion construction method [Certain/Uncertain]

**S12_P05** (10 points [?] points)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Separate both conditions using `constructor` and verify with `norm_num`]
- Mathematical Perspective: Understanding of Hensel's Lemma principle [Deep/Superficial]

**S12_CH** (15 points [?] points)
- Correctness: [Correct/Incorrect]
- Lean Advice: [Example: Prove each condition separately; construct unit existence using `Units.mk`]
- Structural Insight: Understanding of unit group in ℤₚ [Excellent/Needs improvement]

### 4) Next Steps
1. **Understanding p-adic completion**: Construction via Cauchy sequences and completeness
2. **Structure of local fields**: Field structure and extensions of ℚₚ
3. **Preparation for applications**: Bridge to p-adic analysis and local-global principles in Session 13
