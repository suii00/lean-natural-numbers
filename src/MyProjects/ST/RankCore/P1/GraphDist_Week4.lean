import MyProjects.ST.RankCore.P1.GraphDist

/-!
# GraphDist: RankCore via Graph Distance (Week 4 Implementation)

目標: #eval 例を20個以上生成し、多様性を実証する。

設計原則:
- 完全に計算可能（noncomputable なし）
- Bool 隣接行列で有限グラフを表現
- BFS アルゴリズムで最短距離を計算
- 多様なグラフ例（パス・完全・スター・サイクル・非連結）
-/

namespace RankCore

/-! ## 距離の略記 -/

def distance {n : ℕ} (G : FinGraph n) (start target : Fin n) : ℕ :=
  if start = target then 0 else (finGraphCore G start).rank target

/-! ## 具体例カタログ -/

section Examples

/-! ### 例1: パスグラフ P₄ (0-1-2-3) -/

def pathGraph4 : FinGraph 4 where
  adj i j := 
    (i.val + 1 = j.val) || (j.val + 1 = i.val)

def pathGraph4Core : Core (Fin 4) := finGraphCore pathGraph4 0

#eval pathGraph4Core.rank 0  -- 0（始点）
#eval pathGraph4Core.rank 1  -- 1
#eval pathGraph4Core.rank 2  -- 2
#eval pathGraph4Core.rank 3  -- 3（終点）

/-! ### 例2: 完全グラフ K₄ -/

def completeGraph4 : FinGraph 4 where
  adj i j := i ≠ j

def completeGraph4Core : Core (Fin 4) := finGraphCore completeGraph4 0

#eval completeGraph4Core.rank 0  -- 0（始点）
#eval completeGraph4Core.rank 1  -- 1（直接到達）
#eval completeGraph4Core.rank 2  -- 1
#eval completeGraph4Core.rank 3  -- 1

/-! ### 例3: スターグラフ S₅ (中心0、葉1-4) -/

def starGraph5 : FinGraph 5 where
  adj i j := 
    (i.val = 0 && j.val > 0) || (j.val = 0 && i.val > 0)

def starGraph5Core_center : Core (Fin 5) := finGraphCore starGraph5 0

#eval starGraph5Core_center.rank 0  -- 0（中心）
#eval starGraph5Core_center.rank 1  -- 1（葉）
#eval starGraph5Core_center.rank 4  -- 1

def starGraph5Core_leaf : Core (Fin 5) := finGraphCore starGraph5 1

#eval starGraph5Core_leaf.rank 0  -- 1（中心へ）
#eval starGraph5Core_leaf.rank 1  -- 0（自分）
#eval starGraph5Core_leaf.rank 2  -- 2（1→0→2）
#eval starGraph5Core_leaf.rank 4  -- 2（1→0→4）

/-! ### 例4: サイクル C₅ (0-1-2-3-4-0) -/

def cycleGraph5 : FinGraph 5 where
  adj i j := 
    (i.val + 1) % 5 = j.val || (j.val + 1) % 5 = i.val

def cycleGraph5Core : Core (Fin 5) := finGraphCore cycleGraph5 0

#eval cycleGraph5Core.rank 0  -- 0
#eval cycleGraph5Core.rank 1  -- 1
#eval cycleGraph5Core.rank 2  -- 2（中間点）
#eval cycleGraph5Core.rank 3  -- 2（反対側も距離2）
#eval cycleGraph5Core.rank 4  -- 1（逆方向1ステップ）

/-! ### 例5: 非連結グラフ（成分{0,1}, {2,3}） -/

def disconnectedGraph4 : FinGraph 4 where
  adj i j := 
    (i.val ≤ 1 && j.val ≤ 1 && i ≠ j) ||
    (i.val ≥ 2 && j.val ≥ 2 && i ≠ j)

def disconnectedGraph4Core : Core (Fin 4) := finGraphCore disconnectedGraph4 0

#eval disconnectedGraph4Core.rank 0  -- 0（始点）
#eval disconnectedGraph4Core.rank 1  -- 1（同じ成分）
#eval disconnectedGraph4Core.rank 2  -- 4（到達不能 → n）
#eval disconnectedGraph4Core.rank 3  -- 4（到達不能）

/-! ### 例6: 三角形 + 孤立点 -/

def trianglePlusOne : FinGraph 4 where
  adj i j := 
    i.val < 3 && j.val < 3 && i ≠ j

def trianglePlusOneCore : Core (Fin 4) := finGraphCore trianglePlusOne 0

#eval trianglePlusOneCore.rank 0  -- 0
#eval trianglePlusOneCore.rank 1  -- 1
#eval trianglePlusOneCore.rank 2  -- 1
#eval trianglePlusOneCore.rank 3  -- 4（孤立）

end Examples

/-! ## 層の基本定理 -/

section LayerTheorems

variable {n : ℕ} (G : FinGraph n) (start : Fin n)

def graphCore : Core (Fin n) := { rank := distance G start }

lemma mem_layer_iff_distance (v : Fin n) (k : ℕ) :
    v ∈ layer (graphCore G start) k ↔ distance G start v ≤ k := Iff.rfl

lemma layer_monotone {k m : ℕ} (hkm : k ≤ m) :
    layer (graphCore G start) k ⊆ layer (graphCore G start) m := by
  intro v hv
  simp [layer] at hv ⊢
  exact Nat.le_trans hv hkm

lemma distance_self : distance G start start = 0 := by
  simp [distance]

lemma start_in_layer_zero :
    start ∈ layer (graphCore G start) 0 := by
  simp [layer, graphCore, distance]

end LayerTheorems

end RankCore

/-!
## #eval カウント（現時点）

例1 パスグラフ:     4例
例2 完全グラフ:     4例
例3 スターグラフ:   7例（中心始点3例 + 葉始点4例）
例4 サイクル:       5例
例5 非連結:         4例
例6 三角形+孤立:    4例

合計: **28例**

目標20例を達成。多様性の実証完了。
-/
