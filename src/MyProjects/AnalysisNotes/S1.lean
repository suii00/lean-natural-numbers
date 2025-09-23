import Mathlib

/-!
# Session S1: 区間積分の基本則

`S1.md` の記述を Lean で形式化する。区間を有向な順序対としてまとめ、そこから射（関数）を扱う最小限の枠組みを用意した上で、積分に関する基本的な性質を証明していく。
-/

noncomputable section

open scoped Interval Topology BigOperators
open MeasureTheory
open Set

namespace Zen
namespace Analysis1
namespace S1

/-- 有向区間を表す順序対。 -/
structure IntervalPair where
  endpoints : ℝ × ℝ
  ordered : endpoints.1 ≤ endpoints.2

namespace IntervalPair

@[simp]
def left (I : IntervalPair) : ℝ := I.endpoints.1

@[simp]
def right (I : IntervalPair) : ℝ := I.endpoints.2

lemma left_le_right (I : IntervalPair) : I.left ≤ I.right := I.ordered

@[simp]
lemma left_mk (a b : ℝ) (h : a ≤ b) :
    (IntervalPair.mk ⟨a, b⟩ h).left = a := rfl

@[simp]
lemma right_mk (a b : ℝ) (h : a ≤ b) :
    (IntervalPair.mk ⟨a, b⟩ h).right = b := rfl

end IntervalPair

/-- 区間と射（関数）をセットにした簡単な構造。 -/
structure IntervalMorphism where
  obj : IntervalPair
  arrow : ℝ → ℝ

namespace IntervalMorphism

variable (Φ : IntervalMorphism)

@[simp]
def carrier : Set ℝ := Icc Φ.obj.left Φ.obj.right

end IntervalMorphism

section

variable {f g : ℝ → ℝ}

/-- 補助: `IntervalIntegrable` を部分区間へ引き継ぐ。 -/
lemma intervalIntegrable_split {a b c : ℝ} {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) (h₁ : a ≤ c) (h₂ : c ≤ b) :
    IntervalIntegrable f volume a c ∧ IntervalIntegrable f volume c b := by
  refine ⟨?_, ?_⟩
  · refine ⟨hf.1.mono_set (Ioc_subset_Ioc le_rfl h₂), ?_⟩
    simpa [Ioc_eq_empty_of_le h₁] using
      (integrableOn_empty : IntegrableOn f (∅ : Set ℝ))
  · refine ⟨hf.1.mono_set (Ioc_subset_Ioc h₁ le_rfl), ?_⟩
    simpa [Ioc_eq_empty_of_le h₂] using
      (integrableOn_empty : IntegrableOn f (∅ : Set ℝ))/-- Q1: 定数関数の区間積分。 -/
@[simp]
theorem s1_q1 (a b c : ℝ) (_h : a ≤ b) :
    ∫ x in a..b, c = c * (b - a) := by
  simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
    (intervalIntegral.integral_const (μ := volume) (a := a) (b := b) (c := c))

/-- Q2: 恒等写像の区間積分。 -/
@[simp]
theorem s1_q2 (a b : ℝ) (_h : a ≤ b) :
    ∫ x in a..b, x = (1 / 2) * (b ^ 2 - a ^ 2) := by
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (integral_id (a := a) (b := b))

/-- Q3: 区間の分割による積分の加法性。 -/
theorem s1_q3 (a b c : ℝ) (f : ℝ → ℝ) (h_le : a ≤ c ∧ c ≤ b)
    (hf : IntervalIntegrable f volume a b) :
    ∫ x in a..b, f x = (∫ x in a..c, f x) + (∫ x in c..b, f x) := by
  classical
  obtain ⟨h₁, h₂⟩ := h_le
  obtain ⟨hf_ac, hf_cb⟩ := intervalIntegrable_split (f := f) hf h₁ h₂
  have h_split :=
    intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (a := a) (b := c) (c := b) hf_ac hf_cb
  simpa using h_split.symm

/-- Q4: 奇関数の対称区間での積分は 0。 -/
theorem s1_q4 (a : ℝ) (f : ℝ → ℝ) (_h_cont : ContinuousOn f (Icc (-a) a))
    (h_odd : ∀ x, f (-x) = -f x) :
    ∫ x in -a..a, f x = 0 := by
  classical
  set I := ∫ x in -a..a, f x
  have h_comp :=
    intervalIntegral.integral_comp_neg (f := f) (a := -a) (b := a)
  have h_fun : (fun x : ℝ => f (-x)) = fun x => -f x := by
    funext x; simpa [h_odd x]
  have h_neg : (∫ x in -a..a, -f x) = I := by
    simpa [h_fun] using h_comp
  have h_eq : -I = I := by
    simpa using ((intervalIntegral.integral_neg (f := f) (a := -a) (b := a)).symm.trans h_neg)
  have h_sum := congrArg (fun t : ℝ => t + I) h_eq
  have h_sum' : I + I = (0 : ℝ) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_sum.symm
  have h_mul : (2 : ℝ) * I = 0 := by
    simpa [two_mul] using h_sum'
  have hI : I = 0 := by
    have := mul_eq_zero.mp h_mul
    refine this.resolve_left two_ne_zero
  simpa [I] using hI

/-- Q5: 連続関数の単調比較による積分の大小関係。 -/
theorem s1_q5 (a b : ℝ) (f g : ℝ → ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (h_le : ∀ x ∈ Icc a b, f x ≤ g x) :
    ∫ x in a..b, f x ≤ ∫ x in a..b, g x := by
  classical
  have hf_int : IntervalIntegrable f volume a b :=
    hf.intervalIntegrable_of_Icc (μ := volume) hab
  have hg_int : IntervalIntegrable g volume a b :=
    hg.intervalIntegrable_of_Icc (μ := volume) hab
  refine intervalIntegral.integral_mono_on (μ := volume) hab hf_int hg_int ?_
  simpa using h_le

/-- Challenge: 三角形の面積公式の積分的証明。 -/
theorem s1_challenge (b h : ℝ) (hb : 0 < b) (hh : 0 < h) :
    ∫ x in 0..b, (h / b) * x = 1 / 2 * b * h := by
  classical
  have hb' : b ≠ 0 := ne_of_gt hb
  have h_const :=
    intervalIntegral.integral_const_mul (μ := volume) (a := 0) (b := b)
      (r := h / b) (f := fun x : ℝ => x)
  have h_id := s1_q2 (a := 0) (b := b) hb.le
  have : ∫ x in 0..b, (h / b) * x = (h / b) * (∫ x in 0..b, x) := by
    simpa using h_const
  calc
    ∫ x in 0..b, (h / b) * x
        = (h / b) * (∫ x in 0..b, x) := this
    _ = (h / b) * (1 / 2 * b ^ 2) := by
          simpa [sub_eq_add_neg, zero_pow two_ne_zero] using
            congrArg (fun t => (h / b) * t) h_id
    _ = 1 / 2 * b * h := by
      field_simp [hb', mul_comm, mul_left_comm, mul_assoc]

end

end S1
end Analysis1
end Zen












