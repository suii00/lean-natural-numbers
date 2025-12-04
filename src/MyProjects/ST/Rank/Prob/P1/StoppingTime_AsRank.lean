import MyProjects.ST.Rank.P3.RankTower
import Mathlib.Data.Set.Lattice

/-
# 停止時間 = rank 関数（確率論版の対応）

GPT.md の記述を、依存最小の形で Lean4 コードにしたもの。
測度論的詳細は省き、「停止時間は Ω 上の rank 関数であり、
停止集合 `{τ ≤ n}` が構造塔の層に一致する」ことだけを形式化する。
-/

namespace StructureTowerProbability

open Classical
open TowerRank

/-! ## 最小限の停止時間構造 -/

/-- （簡約版）σ-代数フィルトレーションを表すダミー構造。 -/
structure SigmaAlgebraFiltrationWithCovers (Ω : Type _) : Type _ := (dummy : True := True.intro)

namespace SigmaAlgebraFiltrationWithCovers

/-- （簡約版）離散時間停止時間。 -/
structure StoppingTime {Ω : Type _} (ℱ : SigmaAlgebraFiltrationWithCovers Ω) : Type _ where
  τ : Ω → ℕ

end SigmaAlgebraFiltrationWithCovers

open SigmaAlgebraFiltrationWithCovers

/-- 
### 数学的意味
停止時間 `τ : Ω → ℕ` を、そのまま Ω 上の rank 関数と見なす。

### rank理論との対応
`towerFromRank` に渡す ρ として `ω ↦ τ ω` を取るだけの特殊化。

### 確率論的直感
標本点 `ω` に割り当てられた停止時刻が、その点の「階層レベル (rank)」を与える。
-/
def stoppingTimeToRank {Ω} {ℱ : SigmaAlgebraFiltrationWithCovers Ω}
    (τ : StoppingTime ℱ) : Ω → ℕ := τ.τ

/-- 
### 数学的意味
`towerFromRank` が要求する被覆性 `∀ ω, ∃ n, ρ ω ≤ n` を停止時間に対して示す。

### rank理論との対応
`ρ := stoppingTimeToRank τ` を WithTop に埋め込んだ版の被覆性。

### 確率論的直感
停止時間は常に有限の自然数を返すので、`τ(ω)` 自身を上界に取れば十分。
-/
lemma stoppingTime_rank_covers_withTop {Ω} {ℱ : SigmaAlgebraFiltrationWithCovers Ω}
    (τ : StoppingTime ℱ) :
    ∀ ω, ∃ n : ℕ, (stoppingTimeToRank τ ω : WithTop ℕ) ≤ n := by
  intro ω; exact ⟨τ.τ ω, le_rfl⟩

/--
### 数学的意味
停止時間 `τ` から、層 `n := {ω | τ(ω) ≤ n}` を持つ構造塔を構成する。

### rank理論との対応
`towerFromRank` に `ρ := ω ↦ τ(ω)` を適用した特殊化。

### 確率論的直感
時刻 `n` までに停止している標本点の集合を「層」とみなす階層構造。
-/
noncomputable def towerFromStoppingTime {Ω} {ℱ : SigmaAlgebraFiltrationWithCovers Ω}
    (τ : StoppingTime ℱ) : StructureTowerWithMin :=
  towerFromRank (fun ω : Ω => (stoppingTimeToRank τ ω : WithTop ℕ))
    (stoppingTime_rank_covers_withTop τ)

/--
### 数学的意味
停止時間 `τ` から構成した構造塔 `towerFromStoppingTime τ` に対して，
層 `n` が停止集合 `{ω | τ ω ≤ n}` とちょうど一致することを述べる。

### rank理論との対応
`towerFromRank` の層 `layer n = {x | ρ x ≤ n}` を `ρ := stoppingTimeToRank τ` に
特殊化したものに対応する。

### 確率論的直感
「時刻 `n` までに止まっている標本点の集合」と，rank 関数が定める層 `L(n)` が
同一視できるという、「停止集合 = 層」という対応の形式化。
-/
theorem stoppingSet_eq_layer {Ω} {ℱ : SigmaAlgebraFiltrationWithCovers Ω}
    (τ : StoppingTime ℱ) (n : ℕ) :
    {ω : Ω | τ.τ ω ≤ n} = (towerFromStoppingTime τ).layer n := by
  ext ω; simp [towerFromStoppingTime, towerFromRank, stoppingTimeToRank]

/--
### 数学的意味
`towerFromStoppingTime τ` における最小層 `minLayer ω` が、停止時刻 `τ(ω)` と一致する。

### rank理論との対応
`towerFromRank_minLayer_eq_rank` の停止時間への特殊化。

### 確率論的直感
標本点 `ω` が「初めて観測可能になる層」は、その点での停止時刻にほかならない。
-/
theorem minLayer_eq_stoppingTime {Ω} {ℱ : SigmaAlgebraFiltrationWithCovers Ω}
    (τ : StoppingTime ℱ) (ω : Ω) :
    (towerFromStoppingTime τ).minLayer ω = τ.τ ω := by
  have h := towerFromRank_minLayer_eq_rank
    (ρ := stoppingTimeToRank τ)
    (h := stoppingTime_rank_covers_withTop τ)
    (x := ω)
  -- 展開して簡約
  simpa [towerFromStoppingTime, stoppingTimeToRank] using h

/--
### 数学的意味
停止時間を構造塔に持ち上げてから `rankFromTower` で戻す操作が、元の停止時間
（WithTop 埋め込み）に一致することを述べる。

### rank理論との対応
`rankFromTower_towerFromRank` の停止時間への特殊化。

### 確率論的直感
「停止時間 → 層の階層 → rank」と往復しても情報が失われないことの確認。
-/
theorem stoppingTime_rank_roundTrip {Ω} {ℱ : SigmaAlgebraFiltrationWithCovers Ω}
    (τ : StoppingTime ℱ) (ω : Ω) :
    rankFromTower (towerFromStoppingTime τ) ω
      = (τ.τ ω : WithTop ℕ) := by
  have h := rankFromTower_towerFromRank
    (ρ := stoppingTimeToRank τ)
    (h := stoppingTime_rank_covers_withTop τ)
    (x := ω)
  simpa [towerFromStoppingTime, stoppingTimeToRank] using h

end StructureTowerProbability
