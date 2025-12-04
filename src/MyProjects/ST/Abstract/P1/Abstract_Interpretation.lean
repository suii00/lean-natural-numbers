import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Lattice

/-
# 構造塔と抽象解釈：符号抽象化の階層

プログラム静的解析における「符号抽象化」を、
構造塔 (StructureTowerWithMin) として実装した最小例。
-/

namespace SignAbstractionTower

/-- 符号抽象化の抽象値 -/
inductive AbstractValue : Type
  | top : AbstractValue           -- ⊤（任意の値）
  | neg : AbstractValue           -- 負
  | zero : AbstractValue          -- ゼロ
  | pos : AbstractValue           -- 正
  | concrete : ℤ → AbstractValue  -- 具体値
deriving DecidableEq

open AbstractValue

/-- その値を区別するのに必要な最小精度 (= minLayer) -/
def precisionLevel : AbstractValue → ℕ
  | top => 0
  | neg => 1
  | zero => 1
  | pos => 1
  | concrete _ => 2

/-- ℕ 添字版の簡約 StructureTowerWithMin -/
structure SimpleTowerWithMin where
  carrier : Type
  layer : ℕ → Set carrier
  covering : ∀ x, ∃ n, x ∈ layer n
  monotone : ∀ {i j}, i ≤ j → layer i ⊆ layer j
  minLayer : carrier → ℕ
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  minLayer_minimal : ∀ x n, x ∈ layer n → minLayer x ≤ n

/-- 一般の rank 関数から構造塔を得る標準構成 -/
def towerFromRank {α : Type} (ρ : α → ℕ) : SimpleTowerWithMin :=
{ carrier := α
  layer := fun n => {x | ρ x ≤ n}
  covering := by
    intro x; exact ⟨ρ x, by simp⟩
  monotone := by
    intro i j hij x hx; exact le_trans hx hij
  minLayer := ρ
  minLayer_mem := by intro x; simp
  minLayer_minimal := by intro x n hx; simpa using hx }

/-- 符号抽象化の構造塔 -/
def signAbstractionTower : SimpleTowerWithMin :=
  towerFromRank precisionLevel

lemma mem_layer_iff (x : AbstractValue) (n : ℕ) :
    x ∈ signAbstractionTower.layer n ↔ precisionLevel x ≤ n := by
  rfl

/-! ## 基本例 -/

example : top ∈ signAbstractionTower.layer 0 := by
  simp [mem_layer_iff, precisionLevel]

example : pos ∈ signAbstractionTower.layer 1 := by
  simp [mem_layer_iff, precisionLevel]

example : concrete 42 ∈ signAbstractionTower.layer 2 := by
  simp [mem_layer_iff, precisionLevel]

example : signAbstractionTower.minLayer top = 0 := by rfl
example : signAbstractionTower.minLayer neg = 1 := by rfl
example : signAbstractionTower.minLayer (concrete 5) = 2 := by rfl

lemma layer0_subset_layer1 :
    signAbstractionTower.layer 0 ⊆ signAbstractionTower.layer 1 := by
  intro x hx; exact signAbstractionTower.monotone (by decide : 0 ≤ 1) hx

lemma layer1_subset_layer2 :
    signAbstractionTower.layer 1 ⊆ signAbstractionTower.layer 2 := by
  intro x hx; exact signAbstractionTower.monotone (by decide : 1 ≤ 2) hx

/-! ## 抽象化関数と判定関数 -/

def abstractToSign : ℤ → AbstractValue
  | n => if n < 0 then neg else if n = 0 then zero else pos

lemma abstractToSign_precision (n : ℤ) :
    precisionLevel (abstractToSign n) = 1 := by
  by_cases hneg : n < 0
  · simp [abstractToSign, hneg, precisionLevel]
  · by_cases hz : n = 0
    · simp [abstractToSign, hneg, hz, precisionLevel]
    · have hpos : 0 < n := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hz)
      simp [abstractToSign, hneg, hz, hpos.ne', precisionLevel]

def isPositive : AbstractValue → Option Bool
  | top => none
  | neg => some false
  | zero => some false
  | pos => some true
  | concrete n => some (n > 0)

example : isPositive (concrete 5) = some true := by simp [isPositive]
example : isPositive pos = some true := by rfl
example : isPositive top = none := by rfl

end SignAbstractionTower
