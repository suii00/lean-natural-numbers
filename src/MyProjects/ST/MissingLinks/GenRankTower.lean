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
Galois接続から閉包作用素 (Closure Operator) を構成する標準構成。

## 構成の詳細
Galois接続 `l ⊣ u` から、**左側 (α) 上の閉包作用素** `c := u ∘ l : α → α` を定義する。

- `l : α → β` は下随伴（"生成"/"自由構成"方向）
- `u : β → α` は上随伴（"忘却"/"underlying"方向）
- 合成 `u ∘ l : α → α` が α 上の閉包作用素となる

**注意**: 閉包は **α 側に乗る**。β 側の双対（余閉包）は `l ∘ u : β → β` となるが、
これは一般には閉包作用素ではなく、余閉包作用素 (co-closure) となる。

## 圏論的解釈（モナド構造）
この構成は、随伴 `l ⊣ u` から誘導される **モナド** `T := u ∘ l` に他ならない：
- unit: `η_x : x ≤ u(l(x))` (gc.le_u_l)
- multiplication: `μ_x : u(l(u(l(x)))) → u(l(x))` (counit `l ∘ u ≤ id` から誘導)
- monad 則（結合律・単位律）は GC の性質から自動的に成立

## 典型的用途
- `α = Set ι`（生成元の集合）、`β = Subobject X`（部分対象の格子）のとき、
  `u ∘ l` は「生成元集合 S を、S が生成する部分対象 l(S) の underlying 集合 u(l(S)) に送る」
  という生成閉包を与える。
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

注：この定義は生成関数 l のみに依存するが、典型的には l が GC の左随伴として
与えられることを想定している（rankGenFromGC 参照）。
-/
noncomputable def rankGen (l : Set ι → α) (x : α) : WithTop ℕ :=
  sInf {n : WithTop ℕ | ∃ S : Finset ι, (S.card : WithTop ℕ) ≤ n ∧ l S = x}

/--
Galois接続から直接ランク関数を導出する（GC → Rank の接着点）。

GC の **両辺を活用**：u x を「x の候補生成元集合」として、
その部分集合 S ⊆ u x で l S = x を満たす最小の有限集合のサイズをランクとする。

**重要な事実**：GC の性質 (gc.le_u_l) により、l S = x ならば S ⊆ u x が自動的に成立するため、
この制約付き定義は rankGen と **同値** である（rankGenFromGC_eq_rankGen 参照）。

この定義の意義：
- API として GC の両辺（l と u）を使うことを明示
- u x が「x を生成しうる元の集合」という意味を持つことを表現
- 理論的には冗長だが、導出の鎖（GC → 候補集合 → ランク）を可視化
-/
noncomputable def rankGenFromGC {α : Type*} [CompleteLattice α]
    (l : Set ι → α) (u : α → Set ι) (gc : GaloisConnection l u) (x : α) : WithTop ℕ :=
  sInf {n : WithTop ℕ | ∃ S : Finset ι, (↑S : Set ι) ⊆ u x ∧ (S.card : WithTop ℕ) ≤ n ∧ l S = x}

/--
rankGenFromGC と rankGen の同値性。

証明の核心：l S = x ならば、GC の unit (gc.le_u_l) より S ≤ u (l S) = u x。
したがって、制約 S ⊆ u x は自動的に満たされ、両定義の集合は一致する。
-/
lemma rankGenFromGC_eq_rankGen {α : Type*} [CompleteLattice α]
    (l : Set ι → α) (u : α → Set ι) (gc : GaloisConnection l u) (x : α) :
    rankGenFromGC l u gc x = rankGen l x := by
  -- 両辺の sInf の引数集合が一致することを示す
  have h_set_eq : {n : WithTop ℕ | ∃ S : Finset ι, (↑S : Set ι) ⊆ u x ∧ (S.card : WithTop ℕ) ≤ n ∧ l S = x} =
                  {n : WithTop ℕ | ∃ S : Finset ι, (S.card : WithTop ℕ) ≤ n ∧ l S = x} := by
    ext n
    constructor
    · intro ⟨S, _, hcard, hS⟩
      exact ⟨S, hcard, hS⟩
    · intro ⟨S, hcard, hS⟩
      refine ⟨S, ?_, hcard, hS⟩
      -- l S = x から S ⊆ u x を導く（GC の性質）
      calc (↑S : Set ι)
          ≤ u (l S) := gc.le_u_l S
        _ = u x := by rw [hS]
  unfold rankGenFromGC rankGen
  rw [h_set_eq]

/--
Rank Type 2: Stabilization Rank (rankStab)
PreClosureStep f に対して、f^[n] x が安定する（不動点に達する）**最小のステップ数**。

意味：単調拡大写像 f を反復適用したとき、f^[n](x) = f^[n+1](x) が初めて成立する n の値。
- f が閉包作用素から来る場合、これは「閉包に到達するまでの段数」を測る
- 構造塔の文脈では、「被覆段数」や「層の安定化段数」に対応する

注：この rank は f の冪等性がない場合でも定義できるが、一般には ⊤（無限）になりうる。
f が ClosureOperator から来る場合、1段で安定するため rankStab ≤ 1 となる。
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
  have h_le : rankGen l x ≤ (S.card : WithTop ℕ) := sInf_le h_mem
  exact lt_of_le_of_lt h_le (WithTop.coe_lt_top S.card)

/-- rankStab の単調性は一般には自明ではないため、対象の性質に依存する -/
lemma rankStab_le_of_stabilizes (f : PreClosureStep α) (x : α) (n : ℕ)
    (h_stab : f.toFun^[n] x = f.toFun^[n + 1] x) :
    rankStab f x ≤ n := by
  have h_mem : (n : WithTop ℕ) ∈ {n : WithTop ℕ | ∃ m : ℕ, (m : WithTop ℕ) = n ∧ f.toFun^[m] x = f.toFun^[m + 1] x} := by
    use n, rfl, h_stab
  exact sInf_le h_mem

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
  have h_le : rankGen l x ≤ (S.card : WithTop ℕ) := sInf_le h_mem
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

/-- 補助述語：「n 個以下の生成元で x を生成できる」 -/
private def GenPred (l : Set ι → α) (x : α) (n : ℕ) : Prop :=
  ∃ S : Finset ι, S.card ≤ n ∧ l S = x

/--
核心補題：rankGen ≤ n と「n 個以下の生成集合の存在」の同値性。

証明戦略（Nat.find による最小値の構成的取り出し）：
1. 有限生成性から、GenPred を満たす n が存在する
2. Nat.find で最小の m を取る
3. rankGen の sInf が実際にこの最小値 m を達成することを示す
4. rankGen ≤ n ↔ m ≤ n ↔ GenPred (., ., n) を得る

これにより、sInf の一般論だけでは難しい「inf が集合の最小元」を、
ℕ の well-foundedness から構成的に証明する。
-/
lemma rankGen_le_iff_exists
    (l : Set ι → α) (x : α) (h_fg : ∃ S : Finset ι, l S = x) (n : ℕ) :
    rankGen l x ≤ n ↔ ∃ S : Finset ι, S.card ≤ n ∧ l S = x := by
  -- まず「どこかでは生成できる」ので GenPred が満たされる n が存在
  have hex : ∃ k : ℕ, GenPred l x k := by
    obtain ⟨S, hS⟩ := h_fg
    exact ⟨S.card, S, le_rfl, hS⟩

  -- Nat.find で最小の m を取る（Classical を使用）
  open Classical in
  let m : ℕ := Nat.find hex
  have hm_spec : GenPred l x m := Nat.find_spec hex
  have hm_min : ∀ k : ℕ, GenPred l x k → m ≤ k := fun k hk => Nat.find_min' hex hk

  -- rankGen = m を示す（最小値達成）
  have hrank : rankGen l x = (m : WithTop ℕ) := by
    apply le_antisymm
    -- (≤) inf ≤ m は、m が集合に入ることから
    · have hmem : (m : WithTop ℕ) ∈
          {n : WithTop ℕ | ∃ S : Finset ι, (S.card : WithTop ℕ) ≤ n ∧ l S = x} := by
        obtain ⟨S, hcard, hS⟩ := hm_spec
        exact ⟨S, WithTop.coe_le_coe.mpr hcard, hS⟩
      exact sInf_le hmem
    -- (≥) m は下界：任意の候補 y に m ≤ y
    · refine le_sInf ?_
      intro y hy
      obtain ⟨S, hcard, hS⟩ := hy
      -- y の場合分け
      by_cases hy_top : y = ⊤
      · rw [hy_top]; exact le_top
      · -- y < ⊤ なら、ある k : ℕ で y = k
        obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hy_top
        rw [← hk]
        have hk_ge : S.card ≤ k := WithTop.coe_le_coe.mp (hk ▸ hcard)
        have : m ≤ k := hm_min k ⟨S, hk_ge, hS⟩
        exact WithTop.coe_le_coe.mpr this

  constructor
  · intro h
    -- rankGen ≤ n から m ≤ n
    have hm_le_n : m ≤ n := WithTop.coe_le_coe.mp (hrank ▸ h)
    obtain ⟨S, hSm, hS⟩ := hm_spec
    exact ⟨S, le_trans hSm hm_le_n, hS⟩
  · intro h
    obtain ⟨S, hcard, hS⟩ := h
    -- S が集合に入るので inf ≤ S.card ≤ n
    have hmem : (S.card : WithTop ℕ) ∈
        {n : WithTop ℕ | ∃ S : Finset ι, (S.card : WithTop ℕ) ≤ n ∧ l S = x} := by
      exact ⟨S, le_rfl, hS⟩
    calc rankGen l x
        ≤ (S.card : WithTop ℕ) := sInf_le hmem
      _ ≤ (n : WithTop ℕ) := WithTop.coe_le_coe.mpr hcard

/--
GC と 構造塔の整合性チェック (Meta-property)。
生成された塔において、layer n の要素は「n個以下の生成元で生成可能」であることの確認。

証明：上記の rankGen_le_iff_exists 補題を直接適用。
-/
example (l : Set ι → α) (h_fg : ∀ x, ∃ S : Finset ι, l S = x) (n : ℕ) (x : α) :
    x ∈ (buildGenTower l h_fg).layer n ↔
    ∃ S : Finset ι, S.card ≤ n ∧ l S = x := by
  -- StructureTowerWithMin の仕様 (layer n = {x | ρ x ≤ n}) に基づく
  change rankGen l x ≤ n ↔ _
  exact rankGen_le_iff_exists l x (h_fg x) n

end Layer0_Glue
