import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Closure
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import MyProjects.ST.Rank.P3.RankTower

/-!
# GenRankTower.lean
Galois接続からランク関数を導出し、StructureTowerWithMinを構成するフレームワーク。
-/

open Set Order
open TowerRank

/-!
================================================================================
Layer 4: GC Core (Galois Connection to Closure)
Galois接続から閉包作用素を導出する層
================================================================================
-/
namespace Layer4_GC

variable {α β : Type*} [PartialOrder α] [Preorder β]

/--
Galois接続から閉包作用素 (Closure Operator) を構成する。
これは標準的な構成 l ⊣ u ⇒ c = u ∘ l である。
-/
def closureFromGC (l : α → β) (u : β → α) (gc : GaloisConnection l u) :
    ClosureOperator α where
  toFun := u ∘ l
  monotone' := by
    intro x y h
    simp only [Function.comp_apply]
    exact gc.monotone_u (gc.monotone_l h)
  le_closure' := by
    intro x
    simp only [Function.comp_apply]
    exact gc.le_u_l x
  idempotent' := by
    intro x
    simp only [Function.comp_apply]
    -- u(l(u(l(x)))) = u(l(x)) using GC properties
    apply le_antisymm
    · -- u(l(u(l(x)))) ≤ u(l(x)) comes from l(u(l(x))) ≤ l(x) by counit
      exact gc.monotone_u (gc.l_u_le (l x))
    · exact gc.monotone_u (gc.monotone_l (gc.le_u_l x))

/--
案A: 同一束上の Pre-Closure Step。
まだ冪等ではない単調拡大写像 f から、反復による安定化を考えるための構造。
-/
structure PreClosureStep (α : Type*) [Preorder α] where
  toFun : α → α
  monotone : Monotone toFun
  extensive : ∀ x, x ≤ toFun x

end Layer4_GC

/-!
================================================================================
Layer 3: Rank Derivation (GC_to_Rank)
閉包や生成元から Rank (WithTop ℕ) を定義する層
================================================================================
-/
namespace Layer3_Rank

open Layer4_GC

variable {ι α : Type*} [CompleteLattice α]

/--
Rank Type 1: Generator Rank (rankGen)
生成元 (Set ι) と対象 α の間の Galois接続 (l ⊣ u) があるとき、
要素 x を生成する最小の有限集合のサイズをランクとする。
-/
noncomputable def rankGen (l : Set ι → α) (x : α) : WithTop ℕ :=
  sInf {n : WithTop ℕ | ∃ S : Finset ι, (S.card : WithTop ℕ) ≤ n ∧ l S = x}

/--
Rank Type 2: Stabilization Rank (rankStab)
PreClosureStep f に対して、f^[n] x が安定する（最小のステップ数。
-/
noncomputable def rankStab (f : PreClosureStep α) (x : α) : WithTop ℕ :=
  sInf {n : WithTop ℕ | ∃ m : ℕ, (m : WithTop ℕ) = n ∧ f.toFun^[m] x = f.toFun^[m + 1] x}

/-! ### Covering/Properties Lemmas (Proofs can use sorry) -/

/-- rankGen が有限であるための十分条件：x が有限生成であること -/
lemma rankGen_finite_of_fg (l : Set ι → α) (x : α)
    (h_fg : ∃ S : Finset ι, l S = x) :
    rankGen l x < ⊤ := by
  obtain ⟨S, hS⟩ := h_fg
  have h_mem : (S.card : WithTop ℕ) ∈ {n : WithTop ℕ | ∃ S : Finset ι, (S.card : WithTop ℕ) ≤ n ∧ l S = x} := by
    use S, le_rfl, hS
  have h_bdd : BddBelow {n : WithTop ℕ | ∃ S : Finset ι, (S.card : WithTop ℕ) ≤ n ∧ l S = x} := by
    use ⊥
    intro y hy
    exact bot_le
  have h_le : rankGen l x ≤ (S.card : WithTop ℕ) := csInf_le h_bdd h_mem
  exact lt_of_le_of_lt h_le (WithTop.coe_lt_top S.card)

/-- rankStab の単調性は一般には自明ではないため、対象の性質に依存する -/
lemma rankStab_le_of_stabilizes (f : PreClosureStep α) (x : α) (n : ℕ)
    (h_stab : f.toFun^[n] x = f.toFun^[n + 1] x) :
    rankStab f x ≤ n := by
  have h_mem : (n : WithTop ℕ) ∈ {n : WithTop ℕ | ∃ m : ℕ, (m : WithTop ℕ) = n ∧ f.toFun^[m] x = f.toFun^[m + 1] x} := by
    use n, rfl, h_stab
  have h_bdd : BddBelow {n : WithTop ℕ | ∃ m : ℕ, (m : WithTop ℕ) = n ∧ f.toFun^[m] x = f.toFun^[m + 1] x} := by
    use ⊥
    intro y hy
    exact bot_le
  exact csInf_le h_bdd h_mem

end Layer3_Rank

/-!
================================================================================
Layer 2: Rank Normal Form (Connection to Structure Tower)
RankTower.lean の towerFromRank を利用して正規形を構成する層
================================================================================
-/
namespace Layer2_NormalForm

-- ユーザー定義の StructureTowerWithMin を使用すると仮定
-- ここでは RankTower.lean の towerFromRank をラップする

variable {X : Type*}
variable (ρ : X → WithTop ℕ) -- 抽象化されたランク関数

/--
ランク関数から、まだ minLayer (ℕ) を確定させない「WithTop版」の層構造を定義する。
(注意: StructureTowerWithMin は ℕ への写像を要求するため、
 ここでは WithTop ℕ から ℕ への降格条件を満たす場合のみを扱うアダプターを定義する)
-/
noncomputable def towerFromRankWithCondition
    (h_finite : ∀ x, ∃ n : ℕ, ρ x ≤ n) :
    StructureTowerWithMin :=
  TowerRank.towerFromRank ρ h_finite

end Layer2_NormalForm

/-!
================================================================================
Layer 1: WithMin Selection (Conditional Downgrade)
条件が整った場合にのみ Nat.find を発動させて確定的な自然数ランクを得る層
================================================================================
-/
namespace Layer1_Selection

open Layer3_Rank

variable {ι α : Type*} [CompleteLattice α]

/--
Generator Rank の有限性保証。
「全ての要素が有限生成である」という仮定 (Finite Generation) のもとで、
WithTop ℕ ではなく ℕ を返すランク関数を構成する。
-/
lemma rankGen_is_nat (l : Set ι → α)
    (h_all_fg : ∀ x : α, ∃ S : Finset ι, l S = x) :
    ∀ x, ∃ n : ℕ, rankGen l x ≤ n := by
  intro x
  obtain ⟨S, hS⟩ := h_all_fg x
  have h_mem : (S.card : WithTop ℕ) ∈ {n : WithTop ℕ | ∃ S : Finset ι, (S.card : WithTop ℕ) ≤ n ∧ l S = x} := by
    use S, le_rfl, hS
  have h_bdd : BddBelow {n : WithTop ℕ | ∃ S : Finset ι, (S.card : WithTop ℕ) ≤ n ∧ l S = x} := by
    use ⊥
    intro y hy
    exact bot_le
  have h_le : rankGen l x ≤ (S.card : WithTop ℕ) := csInf_le h_bdd h_mem
  exact ⟨S.card, h_le⟩

/--
条件付きで StructureTowerWithMin を構築するファクトリ関数。
ユーザーは「全ての対象が有限生成である」という証明を渡すだけでよい。
-/
noncomputable def buildGenTower (l : Set ι → α)
    (h_all_fg : ∀ x : α, ∃ S : Finset ι, l S = x) :
    StructureTowerWithMin :=
  TowerRank.towerFromRank
    (rankGen l)
    (rankGen_is_nat l h_all_fg)

end Layer1_Selection

/-!
================================================================================
Layer 0: Cat/Glue (Optional)
圏論的な接続や秩序論の補完
================================================================================
-/
namespace Layer0_Glue

open Layer3_Rank Layer1_Selection

variable {ι α : Type*} [CompleteLattice α]

/--
GC と 構造塔の整合性チェック (Meta-property)。
生成された塔において、layer n の要素は「n個以下の生成元で生成可能」であることの確認。
-/
example (l : Set ι → α) (h_fg : ∀ x, ∃ S : Finset ι, l S = x) (n : ℕ) (x : α) :
    x ∈ (buildGenTower l h_fg).layer n ↔
    ∃ S : Finset ι, S.card ≤ n ∧ l S = x := by
  -- StructureTowerWithMin の仕様 (layer n = {x | ρ x ≤ n}) に基づく
  change rankGen l x ≤ n ↔ _
  constructor
  · intro h
    -- rankGenの定義より、inf S ≤ n ならば... (ここは詳細なlatticeの性質が必要)
    sorry -- Proof of logic utilizing properties of sInf in WithTop ℕ
  · intro h
    obtain ⟨S, hcard, hgen⟩ := h
    have h_mem : (S.card : WithTop ℕ) ∈ {n : WithTop ℕ | ∃ S : Finset ι, (S.card : WithTop ℕ) ≤ n ∧ l S = x} := by
      use S, le_rfl, hgen
    have h_bdd : BddBelow {n : WithTop ℕ | ∃ S : Finset ι, (S.card : WithTop ℕ) ≤ n ∧ l S = x} := by
      use ⊥
      intro y hy
      exact bot_le
    have h_le : rankGen l x ≤ (S.card : WithTop ℕ) := csInf_le h_bdd h_mem
    exact le_trans h_le (WithTop.coe_le_coe.mpr hcard)

end Layer0_Glue
