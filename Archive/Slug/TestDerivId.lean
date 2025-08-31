import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add

-- TDD Phase 1: 和の微分法則確認
#check deriv_add
#check @deriv_add
#print deriv_add

-- 定数関数の微分確認
#check deriv_const
#check @deriv_const

-- TDD Phase 2: 実際の適用テスト
variable (a b : ℝ) (x : ℝ)

-- テスト1: 微分可能性の確認
#check differentiableAt_fun_id
#check differentiableAt_const
#check DifferentiableAt.const_mul
-- テスト2: deriv_const の実際の適用
#check deriv_const x b