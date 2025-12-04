import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-
# Rank Functions and Structure Towers: The Canonical Correspondence

構造塔（StructureTowerWithMin）とランク関数（`X → WithTop ℕ`）の
双方向対応を示すファイル。ブルバキ的に「階層＝ランク」の正規形を与える。
-/

/-- 最小層を持つ構造塔（添字は ℕ に固定した簡約版） -/
structure StructureTowerWithMin where
  carrier : Type*
  layer : ℕ → Set carrier
  covering : ∀ x : carrier, ∃ i : ℕ, x ∈ layer i
  monotone : ∀ {i j : ℕ}, i ≤ j → layer i ⊆ layer j
  minLayer : carrier → ℕ
  minLayer_mem : ∀ x, x ∈ layer (minLayer x)
  minLayer_minimal : ∀ x i, x ∈ layer i → minLayer x ≤ i

namespace TowerRank

open Classical

/-! ## Part 1: Rank 関数から構造塔へ（順方向） -/

section RankToTower

variable {X : Type*}

/-- rank 関数から構造塔を構成する基本構成。 -/
noncomputable def towerFromRank (ρ : X → WithTop ℕ)
    (h_covers : ∀ x, ∃ n : ℕ, ρ x ≤ n) :
    StructureTowerWithMin where
  carrier := X
  layer n := {x : X | ρ x ≤ n}
  covering := by
    intro x
    obtain ⟨n, hn⟩ := h_covers x
    exact ⟨n, hn⟩
  monotone := by
    intro i j hij x hx
    exact le_trans hx (WithTop.coe_le_coe.mpr hij)
  minLayer := fun x => Nat.find (h_covers x)
  minLayer_mem := by
    intro x
    change ρ x ≤ Nat.find (h_covers x)
    exact Nat.find_spec (h_covers x)
  minLayer_minimal := by
    intro x i hx
    exact Nat.find_min' (h_covers x) hx

/-- layer の明示的な特徴付け -/
lemma towerFromRank_layer_eq (ρ : X → WithTop ℕ) (h : ∀ x, ∃ n : ℕ, ρ x ≤ n)
    (n : ℕ) :
    (towerFromRank ρ h).layer n = {x : X | ρ x ≤ n} := rfl

/-- minLayer の明示的な特徴付け -/
lemma towerFromRank_minLayer_eq (ρ : X → WithTop ℕ) (h : ∀ x, ∃ n : ℕ, ρ x ≤ n)
    (x : X) :
    (towerFromRank ρ h).minLayer x = Nat.find (h x) := rfl

/-- minLayer が実際にランクと一致する（ρ が ℕ 値のとき） -/
lemma towerFromRank_minLayer_eq_rank (ρ : X → ℕ)
    (h : ∀ x, ∃ n : ℕ, (ρ x : WithTop ℕ) ≤ n) (x : X) :
    (towerFromRank (fun x => (ρ x : WithTop ℕ)) h).minLayer x = ρ x := by
  have hmin : Nat.find (h x) ≤ ρ x := by
    -- witness n = ρ x
    have hx : (ρ x : WithTop ℕ) ≤ ρ x := le_rfl
    exact Nat.find_min' (h x) hx
  have hmax : ρ x ≤ Nat.find (h x) := by
    have hx := Nat.find_spec (h x)
    exact WithTop.coe_le_coe.mp hx
  exact le_antisymm hmin hmax

/-- 要素が層に属する ⇔ ランクがその層以下 -/
lemma mem_towerFromRank_layer_iff (ρ : X → WithTop ℕ)
    (h : ∀ x, ∃ n : ℕ, ρ x ≤ n) (x : X) (n : ℕ) :
    x ∈ (towerFromRank ρ h).layer n ↔ ρ x ≤ n := Iff.rfl

end RankToTower

/-! ## Part 2: 構造塔から Rank 関数へ（逆方向） -/

section TowerToRank

/-- 構造塔から rank 関数を抽出する（minLayer を WithTop に埋め込むだけ）。 -/
def rankFromTower (T : StructureTowerWithMin) :
    T.carrier → WithTop ℕ :=
  fun x => (T.minLayer x : WithTop ℕ)

/-- rank ≤ n であることの特徴付け -/
lemma rankFromTower_le_iff (T : StructureTowerWithMin) (x : T.carrier) (n : ℕ) :
    rankFromTower T x ≤ n ↔ x ∈ T.layer n := by
  constructor
  · intro h
    have hnat : T.minLayer x ≤ n := by
      exact WithTop.coe_le_coe.mp h
    exact T.monotone hnat (T.minLayer_mem x)
  · intro hx
    have hnat : T.minLayer x ≤ n := T.minLayer_minimal x n hx
    exact WithTop.coe_le_coe.mpr hnat

/-- rankFromTower は minLayer 以下（実際は等しい） -/
lemma rankFromTower_le_minLayer (T : StructureTowerWithMin) (x : T.carrier) :
    rankFromTower T x ≤ T.minLayer x := by
  exact WithTop.coe_le_coe.mpr (le_rfl : T.minLayer x ≤ T.minLayer x)

end TowerToRank

/-! ## Part 3: 正規形定理と往復の整合性 -/

section NormalForm

variable {X : Type*}

/-- 順方向の往復：rank → tower → rank が恒等的 -/
theorem rankFromTower_towerFromRank (ρ : X → ℕ)
    (h : ∀ x, ∃ n : ℕ, (ρ x : WithTop ℕ) ≤ n) (x : X) :
    rankFromTower (towerFromRank (fun x => (ρ x : WithTop ℕ)) h) x = ρ x := by
  -- towerFromRank_minLayer_eq_rank で minLayer = ρ を得て、あとは埋め込みを外すだけ。
  have hmin := towerFromRank_minLayer_eq_rank (ρ := ρ) h x
  simp [rankFromTower, hmin]

/-- 逆方向の往復：tower → rank → tower が層ごとに一致 -/
theorem towerFromRank_rankFromTower (T : StructureTowerWithMin) :
    ∀ n : ℕ, (towerFromRank (rankFromTower T) (fun x => ⟨T.minLayer x, le_rfl⟩)).layer n =
      T.layer n := by
  intro n
  ext x
  constructor
  · intro hx
    exact (rankFromTower_le_iff T x n).1 hx
  · intro hx
    exact (rankFromTower_le_iff T x n).2 hx

end NormalForm

/-! ## Part 4: Vec2Q への応用 -/

section Vec2QApplication

/-- Vec2Q の定義（再掲） -/
def Vec2Q : Type := ℚ × ℚ

/-- minBasisCount の定義（再掲） -/
noncomputable def minBasisCount (v : Vec2Q) : ℕ :=
  if v.1 = 0 ∧ v.2 = 0 then 0
  else if v.1 = 0 ∨ v.2 = 0 then 1
  else 2

/-- minBasisCount は常に 2 以下なので被覆性を満たす -/
lemma minBasisCount_covers : ∀ v : Vec2Q, ∃ n : ℕ, (minBasisCount v : WithTop ℕ) ≤ n := by
  intro v
  refine ⟨minBasisCount v, le_rfl⟩

/-- minBasisCount から作る塔の存在を述べる例 -/
example :
    ∃ (linearSpanTower : StructureTowerWithMin),
      linearSpanTower = towerFromRank
        (fun v => (minBasisCount v : WithTop ℕ)) minBasisCount_covers := by
  refine ⟨_, rfl⟩

end Vec2QApplication

/-! ## Part 5: 他の具体例 -/

section OtherExamples

/-- 自然数の恒等ランク関数 -/
def natRank : ℕ → ℕ := id

/-- この場合の被覆性は自明 -/
lemma natRank_covers : ∀ n : ℕ, ∃ m : ℕ, (natRank n : WithTop ℕ) ≤ m := by
  intro n
  exact ⟨n, le_rfl⟩

/-- natRank から作った塔の層を具体的に記述 -/
example :
    (towerFromRank (fun n => (natRank n : WithTop ℕ)) natRank_covers).layer =
      fun n => {k : ℕ | k ≤ n} := by
  funext n; ext k; constructor <;> intro hk <;>
    simpa [towerFromRank, natRank] using hk

/-- 有限集合 {1, 2, ..., n} の部分集合のランク = 濃度 -/
def cardinalityRank (n : ℕ) (S : Finset (Fin n)) : ℕ := S.card

lemma cardinalityRank_covers (n : ℕ) :
    ∀ S : Finset (Fin n), ∃ m : ℕ, (cardinalityRank n S : WithTop ℕ) ≤ m := by
  intro S
  have h : S.card ≤ n := by
    -- |S| ≤ |Fin n| = n
    simpa [Fintype.card_fin] using (Finset.card_le_univ (s := S))
  exact ⟨n, WithTop.coe_le_coe.mpr h⟩

end OtherExamples

end TowerRank
