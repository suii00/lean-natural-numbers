import Mathlib.Data.Nat.Lattice
import MyProjects.ST.RankCore.P1.List

/-!
Graph distance rank (toy model).

Key defs: `Graph`, `reachableIn`, `graphDistCore`, `constRankCore`.
Example: constant rank makes every layer equal to `Set.univ` above the bound.
-/

-- RankCore/GraphDist.lean
namespace RankCore

structure Graph (V : Type*) where
  adj : V → V → Prop

def reachableIn {V : Type*} (_G : Graph V) (_start _v : V) (_n : ℕ) : Prop := True -- TODO

noncomputable def graphDistCore {V : Type*} (G : Graph V) (start : V) : Core V where
  rank := by
    classical
    intro v
    by_cases h : ∃ n, reachableIn G start v n
    · exact Nat.find h
    · exact 0  -- 未到達（仮）

-- 病理例：定数ランク
def constRankCore (α : Type*) (k : ℕ) : Core α where
  rank := fun _ => k

-- この場合、layer 0 = layer 1 = ... = univ（全部同じ）
lemma const_layer_eq {α : Type*} (k : ℕ) :
    ∀ n, k ≤ n → layer (constRankCore α k) n = Set.univ := by
  intro n hn
  ext x
  simp [layer, constRankCore, hn]

-- 設計上の警告：HomDが過剰に緩む
example {α β : Type*} : ∀ (f : α → β),
    ∃ (φ : RankHomD (constRankCore α 0) (constRankCore β 0)),
      φ.map = f := by
  intro f
  exact ⟨{
    map := f
    layer_map_exists := fun _ => ⟨0, by
      intro x hx
      simp [layer, constRankCore] at hx ⊢
    ⟩
  }, rfl⟩

end RankCore
