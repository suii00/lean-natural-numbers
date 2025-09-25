import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Session 2: Basic Graph Theory Facts

We formalize several elementary properties of simple graphs following a set-theoretic
viewpoint: vertices live in a universe and adjacency/neighbor relations are realised as
structures on ordered pairs. Each lemma exposes one of the introductory exercises for
Session 2, and the final statement constructs the composition of graph homomorphisms.
-/
namespace HW_GT_S2

open SimpleGraph Set

-- 基礎問題1: 頂点の存在性
theorem S2_P01 (V : Type*) (G : SimpleGraph V) (u v : V) :
  G.Adj u v → u ∈ (Set.univ : Set V) ∧ v ∈ (Set.univ : Set V) := by
  intro _
  exact ⟨by simp, by simp⟩

-- 基礎問題2: 辺数の上界
theorem S2_P02 (G : SimpleGraph (Fin 3)) [Fintype G.edgeSet] :
  G.edgeFinset.card ≤ 3 := by
  classical
  have h := SimpleGraph.card_edgeFinset_le_card_choose_two (G := G)
  have hChoose : (Fintype.card (Fin 3)).choose 2 = 3 := by decide
  simpa [Nat.card_eq_fintype_card, Fintype.card_coe, Fintype.card_fin, hChoose] using h

-- 基礎問題3: 空グラフの性質
theorem S2_P03 (V : Type*) (u v : V) :
  ¬(⊥ : SimpleGraph V).Adj u v := by
  simp

-- 基礎問題4: 部分グラフの関係
theorem S2_P04 (V : Type*) (G₁ G₂ : SimpleGraph V) (h : G₁ ≤ G₂) (u v : V) :
  G₁.Adj u v → G₂.Adj u v := by
  intro huv
  exact h huv

-- 基礎問題5: 近傍集合の性質
theorem S2_P05 (V : Type*) (G : SimpleGraph V) (u v : V) :
  v ∈ G.neighborSet u → G.Adj u v := by
  intro hv
  simpa [SimpleGraph.mem_neighborSet] using hv

-- チャレンジ: グラフ準同型の合成
theorem S2_CH (V₁ V₂ V₃ : Type*)
    (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) (G₃ : SimpleGraph V₃)
    (f : G₁ →g G₂) (g : G₂ →g G₃) :
  ∃ h : G₁ →g G₃, ∀ v, h v = g (f v) := by
  refine ⟨g.comp f, ?_⟩
  intro v
  rfl

-- 動作確認用の簡単な例
example (G : SimpleGraph (Fin 3)) :
    ∃ h : G →g G, ∀ v, h v = v := by
  classical
  simpa using
    S2_CH (V₁ := Fin 3) (V₂ := Fin 3) (V₃ := Fin 3)
      (G₁ := G) (G₂ := G) (G₃ := G)
      (f := SimpleGraph.Hom.id)
      (g := SimpleGraph.Hom.id)

end HW_GT_S2
