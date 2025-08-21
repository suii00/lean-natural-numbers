/-
課題H: 動作する小さな理論
ブルバキ美学 < 形式化の現実
-/

import Mathlib.RingTheory.Ideal.Basic

namespace WorkingMinimal

variable {R : Type*} [CommRing R]

-- 動作する最小の定理1: イデアルの基本性質
theorem ideal_zero_mem (I : Ideal R) : (0 : R) ∈ I := I.zero_mem

-- 動作する最小の定理2: イデアルの加法閉性  
theorem ideal_add_mem (I : Ideal R) {a b : R} (ha : a ∈ I) (hb : b ∈ I) : 
    a + b ∈ I := I.add_mem ha hb

-- 動作する最小の定理3: 包含関係の反射性
theorem ideal_le_refl (I : Ideal R) : I ≤ I := le_refl I

-- 動作する最小の定理4: 包含関係の推移性
theorem ideal_le_trans {I J K : Ideal R} (hij : I ≤ J) (hjk : J ≤ K) : 
    I ≤ K := le_trans hij hjk

end WorkingMinimal