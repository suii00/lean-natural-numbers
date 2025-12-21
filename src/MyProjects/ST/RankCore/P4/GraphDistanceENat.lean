import Mathlib.Data.ENat.Basic
import MyProjects.ST.RankCore.Basic

/-!
# GraphDistanceENat (A4 skeleton)

A noncomputable example where the rank is a graph distance valued in `ENat` (ℕ∞).
This file is intentionally lightweight: it provides

- a minimal `SimpleGraph` (adjacency relation),
- an inductive `PathLen` predicate (existence of a path of length `n`),
- a distance defined via `Nat.find` (hence `noncomputable` in practice),
- a `Ranked ENat V` structure: vertices ranked by distance from a fixed source.

## Notes
* This is the only A4 example that *intentionally* tolerates `Nat.find` / noncomputable choices.
* Later, you can replace `PathLen` by a more standard notion (Walk/Path, etc.) without changing the API.
-/

namespace ST

universe u

namespace GraphDistanceENat

/-- Minimal directed graph structure. -/
structure SimpleGraph (V : Type u) where
  adj : V → V → Prop

variable {V : Type u} (G : SimpleGraph V)

/-- `PathLen G n s t` means: there is a directed path of length `n` from `s` to `t`. -/
inductive PathLen : ℕ → V → V → Prop
  | refl (v : V) : PathLen 0 v v
  | step {n : ℕ} {v w u : V} : G.adj v w → PathLen n w u → PathLen (n+1) v u

/-- The (least) path length from `s` to `t`, given a proof of reachability. -/
noncomputable def distNat (s t : V) (h : ∃ n, PathLen (G := G) n s t) : ℕ := by
  classical
  exact Nat.find h

lemma distNat_spec (s t : V) (h : ∃ n, PathLen (G := G) n s t) :
    PathLen (G := G) (distNat (G := G) s t h) s t := by
  classical
  exact Nat.find_spec h

/-- Minimality: any path length bounds the chosen witness. -/
lemma distNat_min (s t : V) (h : ∃ n, PathLen (G := G) n s t) :
    ∀ m, PathLen (G := G) m s t → distNat (G := G) s t h ≤ m := by
  classical
  intro m hm
  exact Nat.find_min' h hm

/-- Rank a vertex by its distance from a fixed source `s` (valued in `ENat`). -/
noncomputable def graphDistanceRanked (s : V)
    (hconn : ∀ v : V, ∃ n, PathLen (G := G) n s v) : Ranked ENat V where
  rank := fun v => (distNat (G := G) s v (hconn v) : ENat)

/-- Sanity check: the source has rank 0 (using the trivial path of length 0). -/
lemma rank_source (s : V) (hconn : ∀ v : V, ∃ n, PathLen (G := G) n s v) :
    (graphDistanceRanked (G := G) s hconn).rank s = 0 := by
  -- `distNat s s` can be chosen as 0; we show the rank is `ofNat 0`.
  -- This lemma is intentionally weak and uses only minimality.
  classical
  have h0 : PathLen (G := G) 0 s s := PathLen.refl (G := G) s
  have hx : distNat (G := G) s s (hconn s) ≤ 0 := distNat_min (G := G) s s (hconn s) 0 h0
  have : distNat (G := G) s s (hconn s) = 0 := Nat.le_zero.mp hx
  simp [graphDistanceRanked, this]

end GraphDistanceENat

end ST
