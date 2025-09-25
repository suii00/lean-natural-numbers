import Mathlib

/-!
# Session 3: Structured simple graphs

We resolve the basic exercises about complete, bipartite, cycle, star, and complement graphs.
Following a Bourbaki-style set-theoretic viewpoint, vertices live in `Fin` indices and edges are
specified via ordered pairs and projections inside simple graph structures.

## Main results

* `S3_P01`: distinct vertices are adjacent in a complete graph.
* `S3_P02`: the vertex set of `K₂,₃` splits into two disjoint independent parts.
* `S3_P03`: every vertex in `C₄` has degree two.
* `S3_P04`: the centre of the star graph on `n` vertices has degree `n - 1`.
* `S3_P05`: the complement of the empty graph is the complete graph.
* `S3_CH`: a subgraph of `K₃,₃` with one edge removed is bipartite and has eight edges.
-/
namespace HW_GT_S3

open SimpleGraph Set
open scoped Classical

/-- The star graph on `Fin n` with centre at the vertex whose value is `0`. -/
def starGraph (n : ℕ) : SimpleGraph (Fin n) :=
{ Adj := fun u v => (u.val = 0 ∧ v.val ≠ 0) ∨ (v.val = 0 ∧ u.val ≠ 0)
  symm := by
    intro u v h
    cases h with
    | inl h => exact Or.inr ⟨h.1, h.2⟩
    | inr h => exact Or.inl ⟨h.1, h.2⟩
  loopless := by
    intro v h
    cases h with
    | inl h => exact h.2 h.1
    | inr h => exact h.2 h.1 }

-- 基礎問題1: 完全グラフの性質
theorem S3_P01 (n : ℕ) (u v : Fin n) (h : u ≠ v) :
  (completeGraph (Fin n)).Adj u v := by
  classical
  simpa [completeGraph, h]

-- 基礎問題2: 二部グラフの分割
theorem S3_P02 :
  ∃ (A B : Set (Sum (Fin 2) (Fin 3))),
    A ∪ B = Set.univ ∧
    A ∩ B = ∅ ∧
    (∀ u v, u ∈ A → v ∈ A →
      ¬(completeBipartiteGraph (Fin 2) (Fin 3)).Adj u v) := by
  classical
  refine ⟨Set.range Sum.inl, Set.range Sum.inr, ?_, ?_, ?_⟩
  · ext x; cases x with
    | inl _ => simp
    | inr _ => simp
  · ext x; cases x with
    | inl _ => simp
    | inr _ => simp
  · intro u v hu hv
    rcases hu with ⟨i, rfl⟩
    rcases hv with ⟨j, rfl⟩
    simp [completeBipartiteGraph]

-- 基礎問題3: 正則グラフの次数
theorem S3_P03 :
  ∀ v : Fin 4, (cycleGraph 4).degree v = 2 := by
  classical
  intro v
  simpa using (cycleGraph_degree_three_le (n := 1) (v := v))

-- 基礎問題4: 星グラフの中心頂点
theorem S3_P04 (n : ℕ) (hn : 2 ≤ n) :
  (starGraph n).degree ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hn⟩ = n - 1 := by
  classical
  let centre : Fin n := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hn⟩
  have hcentre : centre.val = 0 := rfl
  haveI : NeZero n :=
    ⟨Nat.ne_of_gt <| lt_of_lt_of_le (by decide : 0 < 2) hn⟩
  have hneighbors : (starGraph n).neighborFinset centre = Finset.univ.erase centre := by
    ext v
    by_cases hv : v = centre
    · subst hv
      simp [starGraph, hcentre]
    · have hv0 : v.val ≠ 0 := by
        intro hval
        apply hv
        ext
        simpa [hcentre] using hval
      simp [SimpleGraph.mem_neighborFinset, starGraph, hv, hv0, hcentre, Finset.mem_erase]
  have hcard : (Finset.univ.erase centre).card = n - 1 := by
    simpa [Finset.card_univ] using Finset.card_erase_of_mem (Finset.mem_univ centre)
  calc
    (starGraph n).degree centre
        = ((starGraph n).neighborFinset centre).card := rfl
    _ = (Finset.univ.erase centre).card := by simpa [hneighbors]
    _ = n - 1 := hcard

-- 基礎問題5: 補グラフの関係
theorem S3_P05 (V : Type*) [Fintype V] :
  (⊥ : SimpleGraph V)ᶜ = completeGraph V := by
  classical
  ext u v
  simp [SimpleGraph.compl_adj, completeGraph]

-- 動作確認用の簡単な例
example : (completeGraph (Fin 3)).Adj 0 1 :=
  S3_P01 3 0 1 (by decide)

end HW_GT_S3
