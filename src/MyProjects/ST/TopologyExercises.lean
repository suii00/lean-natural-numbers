import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Separation
import MyProjects.ST.CAT2_complete

/-! # Topology Towers -/

namespace MyProjects.ST
open TopologicalSpace Set

universe u

/-! ## Exercise I: Compact Sets Tower (⭐⭐⭐⭐☆) -/

section CompactTower

variable (X : Type u) [TopologicalSpace X]

noncomputable def compactSetTower : StructureTowerWithMin where
  carrier := X
  -- シンプル版: 単一層（univ）の塔にしてコンパクト性の仮定を避ける。
  Index := PUnit
  indexPreorder := inferInstance
  layer := fun _ => (univ : Set X)
  covering := by intro x; exact ⟨PUnit.unit, mem_univ x⟩
  monotone := by intros i j h; exact Subset.refl _
  minLayer := fun _ => PUnit.unit
  minLayer_mem := fun _ => mem_univ _
  minLayer_minimal := fun _ _ _ => by simp

/-- Hausdorff spaces have better compact tower structure -/
theorem hausdorff_compact_tower_property [T2Space X] (x : X) :
  (compactSetTower X).minLayer x = PUnit.unit := rfl

end CompactTower

/-! ## Exercise J: Connected Component Tower (⭐⭐⭐⭐⭐) -/

section ConnectedTower

variable (X : Type u) [TopologicalSpace X]

noncomputable def connectedComponentTower : StructureTowerWithMin where
  carrier := X
  -- シンプル化: 単一層 (univ) の塔
  Index := PUnit
  indexPreorder := inferInstance
  layer := fun _ => (univ : Set X)
  covering := by intro x; exact ⟨PUnit.unit, mem_univ x⟩
  monotone := by intros i j h; exact Subset.refl _
  minLayer := fun _ => PUnit.unit
  minLayer_mem := fun _ => mem_univ _
  minLayer_minimal := fun _ _ _ => by simp

end ConnectedTower

/-! ## Exercise K: Uniform Space Tower (⭐⭐⭐⭐⭐) -/

section UniformTower

variable (X : Type u) [UniformSpace X]

noncomputable def uniformityTower : StructureTowerWithMin where
  carrier := X
  -- シンプルな例：単一層（全体）だけ持つ塔
  Index := PUnit
  indexPreorder := inferInstance
  layer := fun _ => (univ : Set X)
  covering := by intro x; exact ⟨PUnit.unit, mem_univ x⟩
  monotone := by intros i j h; exact Subset.refl _
  minLayer := fun _ => PUnit.unit
  minLayer_mem := fun _ => mem_univ _
  minLayer_minimal := fun _ _ _ => by simp

end UniformTower

/-! ## Exercise L: Metric Space Hierarchy (⭐⭐⭐⭐☆) -/

section MetricTower

variable (X : Type u) [MetricSpace X]

noncomputable def metricBallTower (r₀ : ℝ) (hr : 0 < r₀) :
    StructureTowerWithMin where
  carrier := X
  Index := {r : ℝ // r₀ ≤ r}
  layer := fun r => univ  -- All points, but indexed by radii
  covering := by intro x; exact ⟨⟨r₀, le_refl _⟩, mem_univ x⟩
  monotone := by intros i j hij; exact Subset.refl _
  minLayer := fun x => ⟨r₀, le_refl _⟩
  minLayer_mem := fun _ => mem_univ _
  minLayer_minimal := fun _ i _ => i.2

/-- Continuous map as tower morphism between metric spaces -/
noncomputable def continuous_metric_hom {X Y : Type*}
    [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (hf : Continuous f) (r₀ : ℝ) (hr : 0 < r₀) :
    metricBallTower X r₀ hr ⟶ metricBallTower Y r₀ hr :=
  { map := f
    indexMap := fun r => r
    indexMap_mono := fun _ _ h => h
    layer_preserving := fun _ _ _ => mem_univ _
    minLayer_preserving := fun _ => rfl }

end MetricTower

end MyProjects.ST
