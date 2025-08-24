/-
課題H: 戦術習得による構成的証明
段階1: use戦術の習得
-/

import Mathlib.RingTheory.Ideal.Basic

namespace TacticLearning

variable {R : Type*} [CommRing R]

/-! ## 段階1: use戦術の習得 -/

-- 戦術習得1: 理想の交集合が理想であることの存在証明
lemma ideal_inter_is_ideal (I J : Ideal R) : 
    ∃ K : Ideal R, K = I ⊓ J := by
  use I ⊓ J  -- use戦術: 証人を提供すると、定義的等式は自動解決される

-- 戦術習得2: より一般的な存在証明
lemma ideal_exists_containing (r : R) : 
    ∃ I : Ideal R, r ∈ I := by
  use ⊤      -- use戦術: 全体理想を証人として提供
  trivial    -- trivial戦術: 自明な証明

-- 戦術習得3: 複数の条件を満たす理想の存在
lemma ideal_exists_containing_both (r s : R) : 
    ∃ I : Ideal R, r ∈ I ∧ s ∈ I := by
  use ⊤           -- use戦術: 全体理想を証人として提供  
  constructor     -- constructor戦術: ∧を2つの目標に分解
  · trivial       -- 第1目標: r ∈ ⊤
  · trivial       -- 第2目標: s ∈ ⊤

end TacticLearning