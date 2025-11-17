import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import MyProjects.ST.CAT2_complete

universe u v

namespace StructureTowerWithMin

variable {T : StructureTowerWithMin.{u, v}}

/-- 構造塔を添字 i より上で切断する操作
幾何学的には「塔を水平に切って上半分を取る」イメージ -/
def sliceAbove (T : StructureTowerWithMin.{u, v}) (i : T.Index) :
    StructureTowerWithMin.{u, v} where
  -- 修正1: Subtype を使用（正しい！）
  carrier := {x : T.carrier // i ≤ T.minLayer x}
  
  -- 修正2: ここも Subtype にする（// を使う）
  Index := {j : T.Index // i ≤ j}
  
  indexPreorder := inferInstance
  
  -- 修正3: シンプルな形に（型推論を活用）
  layer j := {x | x.val ∈ T.layer j.val}
  
  -- 完璧な証明！
  covering := by
    intro x
    obtain ⟨k, hk⟩ := T.covering x.val
    have hik : i ≤ k := by
      calc
        i ≤ T.minLayer x.val := x.property
        _ ≤ k := T.minLayer_minimal x.val k hk
    use ⟨k, hik⟩
    exact hk
  
  -- 正しい証明！
  monotone := by
    intro j₁ j₂ hjj
    intro x hx
    exact T.monotone hjj hx
  
  minLayer := fun x => ⟨T.minLayer x.val, x.property⟩
  
  -- 正しい証明！
  minLayer_mem := by
    intro x
    exact T.minLayer_mem x.val
  
  -- 正しい証明！
  minLayer_minimal := by
    intro x j hx
    exact T.minLayer_minimal x.val j.val hx

end StructureTowerWithMin
