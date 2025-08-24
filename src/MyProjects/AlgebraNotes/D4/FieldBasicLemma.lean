-- Mode: explore  
-- Goal: "体の最も基本的な性質を一つ実装し、コンパイル成功させる"

import Mathlib.Algebra.Field.Basic

/-!
# 体論探索 - 第一補題

Explore mode: 一つの出力 = 一つの補題
-/

namespace FieldExploration

variable {F : Type*} [Field F]

/--
体の基本性質: 1 ≠ 0
体の定義的特徴として、1と0は異なる元である

## 教育価値
D3での環論経験を活かし、体の特殊性（0でない元は全て可逆）を理解
-/
lemma field_one_ne_zero : (1 : F) ≠ 0 := 
  one_ne_zero

-- TODO: reason="可逆元の性質探索", missing_lemma="field_inv_properties", priority=high

end FieldExploration