import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Basic

/-!
# Layer 1: WithMin Selection Layer

WithTop ℕ の rank を ℕ に降ろす条件付き変換層。

## 核心原則

1. **Rank（不等式）を主役とする**: 普遍性は不等式で表現
2. **WithMin は条件付きビュー**: 条件が揃ったときのみ ℕ に降ろす
3. **問題の隔離**: 確率論での停止時刻の問題をこの層に集約

## 降ろしの条件

- 被覆性: ∀ x, ∃ n : ℕ, rank x ≤ n
- 決定性: rank x ≤ n が決定可能（Decidable）
- 非計算性の受容: Nat.find の使用を明示的に

-/

namespace GCWithMin

open Classical

/-! ## 基本構造の再定義（Layer 2 との互換性） -/

structure Ranked (α : Type*) (X : Type*) where
  rank : X → α

namespace Ranked

variable {α : Type*} {X : Type*}

def layer [Preorder α] (R : Ranked α X) (n : α) : Set X :=
  {x | R.rank x ≤ n}

end Ranked

/-! ## WithTop → ℕ への降ろし -/

section WithTopToNat

variable {X : Type*}

/-- rank が有限であることの証明を伴う Ranked -/
structure RankedFinite (X : Type*) extends Ranked (WithTop ℕ) X where
  /-- 全ての要素のrankが有限 -/
  finite_rank : ∀ x, ∃ n : ℕ, rank x ≤ n

namespace RankedFinite

variable (R : RankedFinite X)

/-- minLayer の定義（Nat.find を使用） -/
noncomputable def minLayer (x : X) : ℕ :=
  Nat.find (R.finite_rank x)

/-- minLayer は rank 以下 -/
theorem rank_le_minLayer (x : X) : R.rank x ≤ R.minLayer x := by
  unfold minLayer
  exact Nat.find_spec (R.finite_rank x)

/-- minLayer は最小 -/
theorem minLayer_minimal (x : X) (n : ℕ) (h : R.rank x ≤ n) :
    R.minLayer x ≤ n := by
  unfold minLayer
  exact Nat.find_min' (R.finite_rank x) h

/-- rank が ℕ 値の場合、minLayer は rank と一致 -/
theorem minLayer_eq_of_nat {rank_nat : X → ℕ} 
    (h : R.rank = fun x => (rank_nat x : WithTop ℕ)) (x : X) :
    R.minLayer x = rank_nat x := by
  have hle1 : rank_nat x ≤ R.minLayer x := by
    have := R.rank_le_minLayer x
    rw [h] at this
    exact WithTop.coe_le_coe.mp this
  have hle2 : R.minLayer x ≤ rank_nat x := by
    apply R.minLayer_minimal
    rw [h]
    exact le_rfl
  exact le_antisymm hle2 hle1

/-- 層への所属と minLayer の関係 -/
theorem mem_layer_iff_le_minLayer (n : ℕ) (x : X) :
    x ∈ R.toRanked.layer (n : WithTop ℕ) ↔ R.minLayer x ≤ n := by
  unfold Ranked.layer minLayer
  constructor
  · intro h
    exact R.minLayer_minimal x n h
  · intro h
    have := R.rank_le_minLayer x
    exact le_trans this (WithTop.coe_le_coe.mpr h)

end RankedFinite

end WithTopToNat

/-! ## StructureTowerWithMin への変換 -/

section ToTowerWithMin

variable {X : Type*}

/-- WithMin を持つ構造塔の簡易定義 -/
structure SimpleTowerWithMin (X : Type*) where
  layer : ℕ → Set X
  covering : ∀ x, ∃ n, x ∈ layer n
  monotone : ∀ {i j}, i ≤ j → layer i ⊆ layer j
  minLayer : X → ℕ
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  minLayer_minimal : ∀ x i, x ∈ layer i → minLayer x ≤ i

/-- RankedFinite から SimpleTowerWithMin を構成 -/
noncomputable def RankedFinite.toTowerWithMin (R : RankedFinite X) :
    SimpleTowerWithMin X where
  layer n := R.toRanked.layer (n : WithTop ℕ)
  covering := by
    intro x
    use R.minLayer x
    exact (R.mem_layer_iff_le_minLayer _ x).mpr (le_refl _)
  monotone := by
    intro i j hij x hx
    unfold Ranked.layer at hx ⊢
    exact le_trans hx (WithTop.coe_le_coe.mpr hij)
  minLayer := R.minLayer
  minLayer_mem := by
    intro x
    exact (R.mem_layer_iff_le_minLayer _ x).mpr (le_refl _)
  minLayer_minimal := by
    intro x i hx
    exact (R.mem_layer_iff_le_minLayer i x).mp hx

end ToTowerWithMin

/-! ## 具体例1: 有限集合のサイズ -/

section FinsetCardExample

variable {α : Type*}

/-- Finset のサイズは常に有限 -/
def finsetCardRanked : RankedFinite (Finset α) where
  toRanked := {
    rank := fun S => (S.card : WithTop ℕ)
  }
  finite_rank := fun S => ⟨S.card, le_refl _⟩

/-- minLayer は card と一致 -/
theorem finsetCardRanked_minLayer_eq_card (S : Finset α) :
    (@finsetCardRanked α).minLayer S = S.card := by
  apply finsetCardRanked.minLayer_eq_of_nat
  rfl

/-- 計算例（非計算的だが型は通る） -/
noncomputable example : (@finsetCardRanked ℕ).minLayer {1, 2, 3} = 3 := by
  rw [finsetCardRanked_minLayer_eq_card]
  rfl

end FinsetCardExample

/-! ## 具体例2: リストの長さ -/

section ListLengthExample

variable {α : Type*}

/-- List の長さは常に有限 -/
def listLengthRanked : RankedFinite (List α) where
  toRanked := {
    rank := fun l => (l.length : WithTop ℕ)
  }
  finite_rank := fun l => ⟨l.length, le_refl _⟩

/-- minLayer は length と一致 -/
theorem listLengthRanked_minLayer_eq_length (l : List α) :
    (@listLengthRanked α).minLayer l = l.length := by
  apply listLengthRanked.minLayer_eq_of_nat
  rfl

end ListLengthExample

/-! ## 具体例3: 自然数の恒等 -/

section NatIdentityExample

/-- 自然数の恒等 rank -/
def natIdentityRanked : RankedFinite ℕ where
  toRanked := {
    rank := fun n => (n : WithTop ℕ)
  }
  finite_rank := fun n => ⟨n, le_refl _⟩

/-- minLayer は id と一致 -/
theorem natIdentityRanked_minLayer_eq_id (n : ℕ) :
    natIdentityRanked.minLayer n = n := by
  apply natIdentityRanked.minLayer_eq_of_nat
  rfl

/-- 層の特徴付け -/
example : 5 ∈ natIdentityRanked.toRanked.layer 5 := by
  unfold Ranked.layer natIdentityRanked
  simp

example : 5 ∈ natIdentityRanked.toRanked.layer 10 := by
  unfold Ranked.layer natIdentityRanked
  simp
  omega

end NatIdentityExample

/-! ## 確率論への応用: 停止時刻 -/

section StoppingTimeExample

/-
停止時刻の問題がこの層に隔離される理由：

1. **WithTop版**: τ : Ω → WithTop ℕ（常に定義可能）
   - 層: {ω | τ ω ≤ n} ∈ ℱ_n（可測性）
   - 普遍性は不等式で表現される

2. **ℕ版**: τ : Ω → ℕ（有限性条件が必要）
   - 条件: ∀ ω, ∃ n, τ ω ≤ n（a.s. 有限）
   - Nat.find で minLayer を構成
   - 非計算性を明示的に受容

この設計により：
- Layer 2-4 は純粋に代数的（WithTop ℕ）
- Layer 1 のみが停止時刻の有限性を扱う
- 問題の所在が明確
-/

-- 確率空間の型（プレースホルダー）
variable (Ω : Type*)

/-- 停止時刻の WithTop 版（常に定義可能） -/
structure StoppingTimeWithTop (Ω : Type*) where
  τ : Ω → WithTop ℕ
  measurable : ∀ n : ℕ, ∀ ω, (τ ω ≤ n) → True  -- 簡略化した可測性条件

/-- a.s. 有限な停止時刻のみが ℕ 版を持つ -/
structure StoppingTimeFinite (Ω : Type*) extends StoppingTimeWithTop Ω where
  almost_surely_finite : ∀ ω, ∃ n : ℕ, τ ω ≤ n

/-- ℕ 版の停止時刻への変換 -/
noncomputable def StoppingTimeFinite.toNat (τ : StoppingTimeFinite Ω) :
    Ω → ℕ :=
  fun ω => Nat.find (τ.almost_surely_finite ω)

/-- 変換後の値は元のτ以下 -/
theorem StoppingTimeFinite.toNat_le (τ : StoppingTimeFinite Ω) (ω : Ω) :
    (τ.τ ω : WithTop ℕ) ≤ τ.toNat ω := by
  unfold toNat
  exact Nat.find_spec (τ.almost_surely_finite ω)

end StoppingTimeExample

/-! ## 決定性の問題 -/

section Decidability

variable {X : Type*}

/-- 決定可能な rank を持つ RankedFinite -/
structure RankedFiniteDecidable (X : Type*) extends RankedFinite X where
  /-- rank の比較が決定可能 -/
  rank_decidable : ∀ x n, Decidable (rank x ≤ (n : WithTop ℕ))

/-
Decidable 版があれば、原理的には計算可能な minLayer を定義できる。
しかし、実際には：

1. Nat.find は依然として非計算的（存在性からの構成）
2. 計算可能版には別のアプローチが必要（WellFounded.fix など）
3. Layer 1 の役割は「降ろしの正当性」の確保であり、計算可能性ではない

計算可能性が必要な場合は、具体的な rank 関数ごとに
直接 def で minLayer を定義するのが実用的。
-/

end Decidability

end GCWithMin
