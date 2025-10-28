import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

noncomputable section

open scoped BigOperators

namespace HW_S14_P01

/-!
# Harville Model (Simplified)
各馬の勝率を `p : Fin n → ℝ` で表す。
以下を仮定する：
1. `∀ i, 0 < p i`
2. `∑ i, p i = 1`
-/

/-- Harville順序確率（長さ2） --/
def harville2 {n : ℕ} (p : Fin n → ℝ) (i j : Fin n) : ℝ :=
  p i * (p j / (1 - p i))

/-- Harville順序確率（長さ3） --/
def harville3 {n : ℕ} (p : Fin n → ℝ) (i j k : Fin n) : ℝ :=
  p i * (p j / (1 - p i)) * (p k / (1 - p i - p j))

/-- 仮定: 確率の基本条件 --/
structure ProbVec (n : ℕ) where
  p : Fin n → ℝ
  pos : ∀ i, 0 < p i
  sum_eq_one : ∑ i, p i = 1

/-- (検証) 2頭順序確率の全和が1になることを確認せよ。 --/
lemma sum_harville2_eq_one {n : ℕ} (P : ProbVec n) (h : 1 < n) :
  ∑ i : Fin n, (∑ j : Fin n, if i = j then 0 else harville2 P.p i j) = 1 := by
  -- TODO: 証明を `Finset.sum` の操作で補う
  sorry

/-
TODO:
1. `harville2` の合計が 1 になることを証明せよ。
2. 3頭モデル `harville3` に拡張せよ。
-/

end HW_S14_P01

end
