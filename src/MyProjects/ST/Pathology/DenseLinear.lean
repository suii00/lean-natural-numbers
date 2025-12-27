import Mathlib.Data.Set.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic

/-!
# Structure Tower Pathology Examples: Dense Linear Order

「線形順序だけでは minLayer の well-definedness には不十分」を示す例。

## 主要な知見
- Index = ℚ（有理数、稠密線形順序）
- 被覆性・単調性は成立
- しかし S_x := {q | x ∈ layer q} に **least が存在しない**

これは PDF 定理5.1の修正を要する：
「線形順序」→「各 S_x に least が存在する」または「整列集合」
-/

namespace Pathology.DenseLinear

open Set

/-!
## denseLinearNoLeast

**設計**:
- Index = ℚ (線形順序だが整列でない)
- X = ℚ
- layer q = {x | x < q}

**性質**:
1. covering: ∀ x, ∃ q, x ∈ layer q（q = x + 1 で充足）
2. monotone: ∀ p ≤ q, layer p ⊆ layer q（lt_of_lt_of_le で成立）
3. least 不在: x = 0 に対し、任意の q > 0 に q/2 を作ると 0 < q/2 < q
-/

/-- 稠密線形順序塔の層定義 -/
def denseLinearLayer (q : ℚ) : Set ℚ := {x | x < q}

/-- 被覆性：任意の x に対して x + 1 で被覆される -/
theorem denseLinearLayer_covering : ∀ x : ℚ, ∃ q : ℚ, x ∈ denseLinearLayer q := by
  intro x
  use x + 1
  simp only [denseLinearLayer, mem_setOf_eq]
  linarith

/-- 単調性：p ≤ q ⟹ layer p ⊆ layer q -/
theorem denseLinearLayer_monotone :
    ∀ {p q : ℚ}, p ≤ q → denseLinearLayer p ⊆ denseLinearLayer q := by
  intro p q hpq x hx
  simp only [denseLinearLayer, mem_setOf_eq] at hx ⊢
  exact lt_of_lt_of_le hx hpq

/-- S_0 の定義：0 が属する層の添字集合 -/
def S_zero : Set ℚ := {q | (0 : ℚ) ∈ denseLinearLayer q}

/-- S_0 = {q | 0 < q} -/
theorem S_zero_eq : S_zero = {q : ℚ | 0 < q} := by
  ext q
  simp only [S_zero, denseLinearLayer, mem_setOf_eq]

/-- S_0 に least が存在しないことの証明：
    任意の q ∈ S_0 に対し、q/2 ∈ S_0 かつ q/2 < q -/
theorem S_zero_has_no_least : ¬ ∃ m : ℚ, m ∈ S_zero ∧ ∀ q ∈ S_zero, m ≤ q := by
  intro ⟨m, hm_in, hm_least⟩
  -- m ∈ S_0 means 0 < m
  rw [S_zero_eq] at hm_in hm_least
  simp only [mem_setOf_eq] at hm_in hm_least
  -- m/2 ∈ S_0 かつ m/2 < m を示す
  have h_half_pos : (0 : ℚ) < m / 2 := by linarith
  have h_half_lt : m / 2 < m := by linarith
  -- m が最小なので m ≤ m/2 のはず
  have h_contra : m ≤ m / 2 := hm_least (m / 2) h_half_pos
  -- しかし m/2 < m なので矛盾
  linarith

/-- minLayer が well-defined でないことの直接的な帰結 -/
theorem denseLinear_no_minLayer_for_zero :
    ¬ ∃ q₀ : ℚ, (0 : ℚ) ∈ denseLinearLayer q₀ ∧
      ∀ q : ℚ, (0 : ℚ) ∈ denseLinearLayer q → q₀ ≤ q := by
  intro ⟨q₀, hq₀_mem, hq₀_min⟩
  simp only [denseLinearLayer, mem_setOf_eq] at hq₀_mem hq₀_min
  -- q₀/2 も条件を満たす
  have h_half : (0 : ℚ) < q₀ / 2 := by linarith
  have h_contra : q₀ ≤ q₀ / 2 := hq₀_min (q₀ / 2) h_half
  linarith

end Pathology.DenseLinear
