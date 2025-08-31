-- Mode: explore
-- Goal: "Chain\claude.txt課題の最小動作版とAPIレベル学習"

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace MyProjects.Calculus.Chain.Minimal

-- =================== 基本API学習成功版 ===================

/-- 準備: 恒等関数の微分 ✅ -/
theorem deriv_id_explicit : ∀ x : ℝ, deriv (fun x => x) x = 1 := by
  intro x
  exact deriv_id x

/-- 課題1: c*x の微分は c ✅ -/
theorem deriv_const_mul_id (c : ℝ) : 
  ∀ x : ℝ, deriv (fun x => c * x) x = c := by
  intro x
  rw [deriv_const_mul]
  · simp [deriv_id'']
  · exact differentiableAt_id

/-- 課題2: (2x)^2 の微分 = 8x （最も直接的なアプローチ）✅ -/
theorem deriv_comp_linear_square :
  ∀ x : ℝ, deriv (fun x => (2 * x) ^ 2) x = 8 * x := by
  intro x
  -- 直接計算: (2x)^2 を展開
  simp only [pow_two]
  -- (2*x) * (2*x) = 4*x^2
  have h : ∀ t : ℝ, (2 * t) * (2 * t) = 4 * t ^ 2 := by
    intro t
    ring
  simp [h, deriv_const_mul (differentiableAt_pow), deriv_pow_field 2]
  ring

-- =================== API学習成果の記録 ===================

-- ✅ 成功したAPI使用パターン（3/8課題 = 37.5%）:
-- 1. deriv_id: 恒等関数の基本微分
-- 2. deriv_const_mul: 定数倍微分法則
-- 3. deriv_pow_field: べき乗関数の微分（直接形）
-- 4. simp + ring: 代数的変形による関数等価性

-- 🎯 学習成果:
-- - 基本微分API の確実な使用法習得
-- - 型システム制約下でのsimp活用技法
-- - 展開による合成関数回避アプローチ

-- ❌ 継続困難課題（5/8課題 = 62.5%）:
-- 4. deriv_x_plus_one_squared: (x+1)^2 の微分
-- 5. deriv_sqrt_linear: √(2x+1) の微分  
-- 6. exp_2x_deriv_explicit: e^(2x) の微分
-- 7. manual_chain_rule: 一般連鎖律
-- 8. chain_rule_example: 具体的連鎖律適用

-- 📚 claude.txt との比較:
-- 期待: 段階的アプローチによる連鎖律マスター
-- 現実: 基本微分は成功、真の連鎖律（deriv.comp）は継続困難

-- 💡 次期学習戦略:
-- - deriv.comp の正確な使用法の詳細調査
-- - より単純な合成関数での成功例蓄積
-- - HasDerivAt レベルでの連鎖律理解

end MyProjects.Calculus.Chain.Minimal