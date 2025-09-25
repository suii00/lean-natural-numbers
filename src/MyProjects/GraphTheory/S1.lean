import Mathlib

/-!
# Graph Theory S1

This module formalizes the first set of exercises on simple graphs. The focus
is on symmetry of adjacency, basic degree computations, concrete adjacency
checks, reachability, complements, and the handshake lemma.
-/
namespace HW_GT_S1

open SimpleGraph
open scoped BigOperators

-- 基礎問題1: グラフの対称性
theorem S1_P01 (V : Type*) (G : SimpleGraph V) (u v : V) :
  G.Adj u v → G.Adj v u := by
  intro huv
  have hsymm : G.Adj u v ↔ G.Adj v u := G.adj_comm u v
  exact hsymm.mp huv

-- 基礎問題2: 完全グラフの次数
theorem S1_P02 :
  ∀ v : Fin 3, (completeGraph (Fin 3)).degree v = 2 := by
  classical
  intro v
  fin_cases v <;> decide

-- 基礎問題3: サイクルグラフの隣接性
theorem S1_P03 :
  let C4 := cycleGraph 4
  C4.Adj 0 1 ∧ ¬C4.Adj 0 2 := by
  intro C4
  classical
  refine ⟨?_, ?_⟩
  · simpa [C4] using (by decide : (cycleGraph 4).Adj (0 : Fin 4) (1 : Fin 4))
  · simpa [C4] using (by decide : ¬(cycleGraph 4).Adj (0 : Fin 4) (2 : Fin 4))

-- 基礎問題4: 到達可能性の反射性
theorem S1_P04 (V : Type*) (G : SimpleGraph V) (v : V) :
  G.Reachable v v := by
  classical
  exact ⟨Walk.nil⟩

-- 基礎問題5: 補グラフの性質
theorem S1_P05 (V : Type*) (G : SimpleGraph V) (u v : V) :
  G.Adj u v → ¬Gᶜ.Adj u v := by
  classical
  intro huv
  simp [SimpleGraph.compl_adj, huv]

-- チャレンジ: ハンドシェイク補題
theorem S1_CH (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
  (∑ v : V, G.degree v) = 2 * G.edgeFinset.card := by
  classical
  simpa using G.sum_degrees_eq_twice_card_edges

example : (completeGraph (Fin 3)).degree 0 = 2 :=
  S1_P02 0

end HW_GT_S1
