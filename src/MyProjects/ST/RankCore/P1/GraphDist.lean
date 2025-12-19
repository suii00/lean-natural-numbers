import Mathlib
import MyProjects.ST.RankCore.P1.List

/-!
Computable graph distance rank (finite graph).

Key defs: `FinGraph`, `pathLength`, `finGraphCore`, `lineGraph3`.
Example: `finGraphCore lineGraph3 0 |>.rank 2 = 2`.
-/

-- RankCore/GraphDist.lean
namespace RankCore

/-- Finite graph on `Fin n`, adjacency as `Bool`. -/
structure FinGraph (n : ℕ) where
  adj : Fin n → Fin n → Bool

def neighbors {n : ℕ} (G : FinGraph n) (v : Fin n) : List (Fin n) :=
  (List.finRange n).filter (fun w => G.adj v w)

def bfsAux {n : ℕ} (G : FinGraph n) (target : Fin n) :
    Nat → Nat → List (Fin n) → Finset (Fin n) → Option Nat
  | fuel, depth, frontier, visited =>
      if target ∈ frontier then
        some depth
      else
        match fuel with
        | 0 => none
        | fuel + 1 =>
            let next := frontier.flatMap (neighbors G)
            let next' := next.filter (fun w => decide (w ∉ visited))
            let visited' := visited ∪ next'.toFinset
            bfsAux G target fuel (depth + 1) next' visited'

/-- BFS shortest path length, with fuel `n` for termination. -/
def pathLength {n : ℕ} (G : FinGraph n) (start target : Fin n) : Option ℕ :=
  bfsAux G target n 0 [start] ({start} : Finset (Fin n))

def finGraphCore {n : ℕ} (G : FinGraph n) (start : Fin n) : Core (Fin n) where
  rank := fun v => (pathLength G start v).getD n  -- 未到達なら n

def lineGraph3 : FinGraph 3 where
  adj := fun i j => decide (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1)

#eval (finGraphCore lineGraph3 0).rank 2  -- 2

end RankCore
