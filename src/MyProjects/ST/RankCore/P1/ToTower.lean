import MyProjects.ST.Rank.P3.RankTower
import MyProjects.ST.RankCore.P1.List

/-!
Bridge from `Core` to `StructureTowerWithMin`.

Key defs: `toTowerWithMin`, `rank_tower_rank`.
Example: `x ∈ (toTowerWithMin T).layer (T.rank x)`.
-/

-- RankCore/ToTower.lean
namespace RankCore

def toTowerWithMin {α : Type*} (T : Core α) : StructureTowerWithMin where
  carrier := α
  layer := fun n => layer T n
  covering := by
    intro x
    refine ⟨T.rank x, ?_⟩
    simp [layer]
  monotone := by
    intro i j hij x hx
    exact le_trans hx hij
  minLayer := T.rank
  minLayer_mem := by
    intro x
    simp [layer]
  minLayer_minimal := by
    intro x i hx
    exact hx

-- 往復の確認（既存のrankFromTower_towerFromRankを再現）
theorem rank_tower_rank {α : Type*} (T : Core α) (x : α) :
    (toTowerWithMin T).minLayer x = T.rank x := rfl

example {α : Type*} (T : Core α) (x : α) :
    x ∈ (toTowerWithMin T).layer (T.rank x) := by
  exact (toTowerWithMin T).minLayer_mem x

end RankCore
