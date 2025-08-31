-- Mode: explore
-- Goal: "ガロア拡大の基本性質を一つ実装し、探索成果を記録する"

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Separable

/-!
# ガロア理論基礎探索 - claude2.txt実装

## 探索目標
claude2.txtで提案された7段階構築の第1段階を実装

## 段階1: ガロア拡大の基本構造
分離可能かつ正規な拡大の特徴付け

## Educational Value
- ガロア理論への入門点
- 分離性と正規性の理解
- Mathlib APIの活用法学習
-/

namespace GaloisBasicExplore

variable {K F : Type*} [Field K] [Field F] [Algebra F K]

/-- ガロア拡大の特徴付け補題 
分離可能かつ正規な拡大はガロア拡大である -/
theorem galois_extension_basic_characterization [FiniteDimensional F K] :
  IsGalois F K ↔ Algebra.IsSeparable F K ∧ Normal F K := by
  -- Mathlibに既存の定理 isGalois_iff を使用
  exact isGalois_iff

/-- ガロア群の基本性質：有限ガロア拡大のガロア群は有限 -/
lemma galois_group_finite_of_finite_extension 
  [FiniteDimensional F K] [IsGalois F K] :
  Finite (K ≃ₐ[F] K) := by
  -- library_search候補: Fintype.finite, AlgEquiv.fintype
  haveI : Fintype (K ≃ₐ[F] K) := AlgEquiv.fintype F K
  infer_instance
  
/-- 探索成果記録：Mathlib API進化の発見
## 発見事項
1. IsGalois型クラスが整備されている
2. Normal F K が Mathlib 4.3+ で利用可能
3. AlgEquiv.fintype が自動的に有限性を提供
4. isGalois_iff定理が分離可能性と正規性の同値を提供

## エラーパターン
- IsGalois.mkは存在しない→isGalois_iffを使用
- Normal vs IsNormal の混同を避ける
- FiniteDimensional制約の明示が必要
-/
def exploration_notes : String := 
  "ガロア理論API: IsGalois型クラスとNormal述語の統合的利用"

#check IsGalois.to_isSeparable
#check IsGalois.to_normal
#check AlgEquiv.fintype

end GaloisBasicExplore