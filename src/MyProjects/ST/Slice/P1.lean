import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import MyProjects.ST.CAT2_complete
-- CAT2_complete.lean から StructureTowerWithMin をインポートしたと仮定

namespace StructureTowerWithMin

variable {T : StructureTowerWithMin.{u, v}}

/-- 構造塔を添字 i より上で切断する操作
幾何学的には「塔を水平に切って上半分を取る」イメージ -/
def sliceAbove (T : StructureTowerWithMin.{u, v}) (i : T.Index) :
    StructureTowerWithMin.{u, v} where
  -- エラー1: carrier の型が正しくない
  carrier := {x : T.carrier // i ≤ T.minLayer x}

  Index := {j : T.Index | i ≤ j}

  indexPreorder := inferInstance

  layer j := T.layer j.val ∩ {x : T.carrier | i ≤ T.minLayer x}

  -- エラー2: covering の証明が不完全
  covering := by
    intro x
    -- x は sliceAbove の carrier なので i ≤ T.minLayer x.val
    obtain ⟨k, hk⟩ := T.covering x.val
    have hik : i ≤ k := by
      calc
        i ≤ T.minLayer x.val := x.property
        _ ≤ k := T.minLayer_minimal x.val k hk
    use ⟨k, hik⟩
    refine ⟨hk, x.property⟩

  monotone := by
    intro j₁ j₂ hjj
    intro x hx
    -- エラー3: ここの証明が論理的に不完全
    refine ⟨T.monotone hjj hx.1, hx.2⟩

  minLayer := fun x => ⟨T.minLayer x.val, x.property⟩

  minLayer_mem := by
    intro x
    constructor
    · exact T.minLayer_mem x.val
    · exact x.property

  minLayer_minimal := by
    intro x j hx
    exact T.minLayer_minimal x.val j.val hx.1

end StructureTowerWithMin
