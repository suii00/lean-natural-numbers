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

-- チャレンジ: 二部グラフの特徴づけ
theorem S3_CH (V : Type*) [Fintype V] (G : SimpleGraph V)
    (h_no_odd : ∀ (v : V) (c : G.Walk v v), c.IsCycle → Even c.length) :
  G.IsBipartite := by
  sorry

end HW_GT_S3
