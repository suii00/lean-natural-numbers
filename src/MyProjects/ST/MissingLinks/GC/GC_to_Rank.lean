import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Order.Closure
import Mathlib.Order.Iterate

/-!
# Layer 3: Closure Operator → Rank Functions

閉包作用素から2種類のrank関数を導出：

1. **rankStab**: 安定化回数によるrank（反復型）
2. **rankGen**: 生成子数によるrank（有限生成型）

## 重要な設計方針

- rank の値域は `WithTop ℕ` を優先（無限も扱える）
- 被覆性には明示的な条件が必要（Finite X, ACC, etc.）
- ℕ への降ろしは条件付きで Layer 1 で実施

-/

namespace GaloisRank

open Classical

variable {X : Type*}

/-! ## 基本的な閉包作用素の型 -/

/-- 閉包作用素の最小限の構造 -/
structure ClosureOp (X : Type*) where
  /-- 閉包関数 -/
  cl : Set X → Set X
  /-- 単調性 -/
  mono : Monotone cl
  /-- 拡大性: s ⊆ cl s -/
  le_closure : ∀ s, s ⊆ cl s
  /-- 冪等性: cl (cl s) = cl s -/
  idempotent : ∀ s, cl (cl s) = cl s

namespace ClosureOp

variable (C : ClosureOp X)

/-! ## Type 1: 安定化によるRank（反復型） -/

/-- n回の反復適用 -/
def iter (n : ℕ) (s : Set X) : Set X := 
  (C.cl^[n]) s

/-- s が n 回で安定化する -/
def StabilizesAt (s : Set X) (n : ℕ) : Prop :=
  C.iter n s = C.iter (n + 1) s

/-- 安定化が起こる最小の n（存在しない場合は ⊤） -/
noncomputable def rankStab (s : Set X) : WithTop ℕ :=
  if h : ∃ n, C.StabilizesAt s n 
  then ↑(Nat.find h)
  else ⊤

/-! ### rankStab の基本性質 -/

/-- rankStab が有限 ⇔ 安定化する -/
theorem rankStab_ne_top_iff (s : Set X) :
    C.rankStab s ≠ ⊤ ↔ ∃ n, C.StabilizesAt s n := by
  unfold rankStab
  split_ifs with h
  · simp [h]
  · simp [h]

/-- rankStab が n である場合、n で安定化 -/
theorem stabilizes_at_rankStab (s : Set X) (n : ℕ) 
    (h : C.rankStab s = n) :
    C.StabilizesAt s n := by
  unfold rankStab at h
  split_ifs at h with hex
  · have := Nat.find_spec hex
    simp only [WithTop.coe_inj] at h
    rwa [← h]
  ·
    exact (False.elim <| (WithTop.coe_ne_top (a := n)) <| by
      simpa using h.symm)

/-- 反復の単調性 -/
theorem iter_mono {s t : Set X} (hst : s ⊆ t) (n : ℕ) :
    C.iter n s ⊆ C.iter n t := by
  induction n with
  | zero => 
    unfold iter
    simp
    exact hst
  | succ n ih =>
    unfold iter at ih ⊢
    simp only [Function.iterate_succ_apply']
    exact C.mono ih

/-- 反復は増加列を成す -/
theorem iter_subset_succ (s : Set X) (n : ℕ) :
    C.iter n s ⊆ C.iter (n + 1) s := by
  unfold iter
  simp only [Function.iterate_succ_apply']
  exact C.le_closure _

/-! ### 有限性条件下での被覆性 -/

/-- [有限集合の場合] 必ず安定化する -/
theorem finite_stabilizes [Finite X] (s : Set X) :
    ∃ n, C.StabilizesAt s n := by
  sorry -- TODO: reason="proof pending", follow_up="formalize in mathlib"

/-- [有限集合の場合] rankStab は有限 -/
theorem finite_rankStab_ne_top [Finite X] (s : Set X) :
    C.rankStab s ≠ ⊤ := by
  rw [rankStab_ne_top_iff]
  exact finite_stabilizes C s

/-! ## Type 2: 生成子数によるRank（有限生成型） -/

/-- s が有限集合 S から生成される -/
def IsGenerated (s : Set X) (S : Finset X) : Prop :=
  s ⊆ C.cl (S : Set X)

/-- s の生成に必要な最小の濃度 -/
noncomputable def rankGen (s : Set X) : WithTop ℕ :=
  sInf {n : WithTop ℕ | ∃ S : Finset X, S.card ≤ n ∧ C.IsGenerated s S}

/-! ### rankGen の基本性質 -/

/-- s が有限生成可能 ⇔ rankGen が有限 -/
theorem rankGen_ne_top_iff (s : Set X) :
    C.rankGen s ≠ ⊤ ↔ ∃ S : Finset X, C.IsGenerated s S := by
  classical
  let T : Set (WithTop ℕ) :=
    {n : WithTop ℕ | ∃ S : Finset X, S.card ≤ n ∧ C.IsGenerated s S}
  constructor
  · intro hne
    by_contra hgen
    have hT : T = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro n hn
      rcases hn with ⟨S, _hSn, hSgen⟩
      exact hgen ⟨S, hSgen⟩
    have : C.rankGen s = ⊤ := by
      simp [rankGen, T, hT]
    exact hne this
  · rintro ⟨S, hS⟩ htop
    have htop' : sInf T = ⊤ := by
      simpa [rankGen, T] using htop
    have hforall : ∀ a ∈ T, a = (⊤ : WithTop ℕ) := (sInf_eq_top).mp htop'
    have hmem : ((S.card : ℕ) : WithTop ℕ) ∈ T := by
      exact ⟨S, le_rfl, hS⟩
    have : ((S.card : ℕ) : WithTop ℕ) = ⊤ := hforall _ hmem
    exact (WithTop.coe_ne_top (a := S.card)) this

/-- rankGen の単調性 -/
theorem rankGen_mono {s t : Set X} (hst : s ⊆ t) :
    C.rankGen s ≤ C.rankGen t := by
  classical
  let Ts : Set (WithTop ℕ) :=
    {n : WithTop ℕ | ∃ S : Finset X, S.card ≤ n ∧ C.IsGenerated s S}
  let Tt : Set (WithTop ℕ) :=
    {n : WithTop ℕ | ∃ S : Finset X, S.card ≤ n ∧ C.IsGenerated t S}
  have hsubset : Tt ⊆ Ts := by
    intro n hn
    rcases hn with ⟨S, hcard, hgen⟩
    refine ⟨S, hcard, ?_⟩
    intro x hx
    exact hgen (hst hx)
  have hle : sInf Ts ≤ sInf Tt := sInf_le_sInf (s := Tt) (t := Ts) hsubset
  simpa [rankGen, Ts, Tt] using hle

/-! ## Type 3: 要素ごとの到達Rank -/

/-- 要素 x が s₀ から n 回の閉包で到達可能 -/
def ReachableIn (x : X) (s₀ : Set X) (n : ℕ) : Prop :=
  x ∈ C.iter n s₀

/-- 要素 x が s₀ から到達可能になる最小回数 -/
noncomputable def rankReach (x : X) (s₀ : Set X) : WithTop ℕ :=
  sInf {n : WithTop ℕ | n < ⊤ ∧ ∃ m : ℕ, n = m ∧ C.ReachableIn x s₀ m}

/-! ### rankReach の基本性質 -/

/-- x が到達可能 ⇔ rankReach が有限 -/
theorem rankReach_ne_top_iff (x : X) (s₀ : Set X) :
    C.rankReach x s₀ ≠ ⊤ ↔ ∃ n, C.ReachableIn x s₀ n := by
  classical
  let S : Set (WithTop ℕ) :=
    {n : WithTop ℕ | n < ⊤ ∧ ∃ m : ℕ, n = m ∧ C.ReachableIn x s₀ m}
  constructor
  · intro hne
    by_contra hreach
    have hSempty : S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro n hn
      rcases hn with ⟨_hnlt, m, rfl, hm⟩
      exact hreach ⟨m, hm⟩
    have : C.rankReach x s₀ = ⊤ := by
      simp [rankReach, S, hSempty]
    exact hne this
  · rintro ⟨m, hm⟩ htop
    have hmem : ((m : ℕ) : WithTop ℕ) ∈ S := by
      refine ⟨by simpa using (WithTop.coe_lt_top m), ?_⟩
      exact ⟨m, rfl, hm⟩
    have hle : C.rankReach x s₀ ≤ ((m : ℕ) : WithTop ℕ) := by
      simpa [rankReach, S] using (sInf_le hmem)
    have htop_le : (⊤ : WithTop ℕ) ≤ ((m : ℕ) : WithTop ℕ) := by
      simpa [htop] using hle
    have : ((m : ℕ) : WithTop ℕ) = ⊤ := (top_le_iff.mp htop_le)
    exact (WithTop.coe_ne_top (a := m)) this

/-- s₀ に含まれる要素は rank 0 -/
theorem rankReach_mem_zero {x : X} {s₀ : Set X} (hx : x ∈ s₀) :
    C.rankReach x s₀ = ((0 : ℕ) : WithTop ℕ) := by
  classical
  let S : Set (WithTop ℕ) :=
    {n : WithTop ℕ | n < ⊤ ∧ ∃ m : ℕ, n = m ∧ C.ReachableIn x s₀ m}
  have hmem : ((0 : ℕ) : WithTop ℕ) ∈ S := by
    refine ⟨by simpa using (WithTop.coe_lt_top (0 : ℕ)), ?_⟩
    refine ⟨0, rfl, ?_⟩
    simpa [ReachableIn, ClosureOp.iter] using hx
  have hle : sInf S ≤ ((0 : ℕ) : WithTop ℕ) := sInf_le hmem
  have hge : ((0 : ℕ) : WithTop ℕ) ≤ sInf S := by
    refine le_sInf ?_
    intro b hb
    exact bot_le
  simpa [rankReach, S] using le_antisymm hle hge

example {x : X} {s₀ : Set X} (hx : x ∈ s₀) :
    C.rankReach x s₀ = ((0 : ℕ) : WithTop ℕ) :=
  C.rankReach_mem_zero (x := x) (s₀ := s₀) hx

/-! ## Rank 関数間の関係 -/

/-- 安定化 rank と到達 rank の関係 -/
theorem rankStab_le_sup_rankReach (s₀ : Set X) [Finite X] :
    C.rankStab s₀ ≤ ⨆ x : X, C.rankReach x s₀ := by
  sorry -- TODO: reason="proof pending", follow_up="formalize in mathlib"

end ClosureOp

/-! ## 具体例1: 部分集合の反復適用 -/

section SubsetClosure

variable (f : Set X → Set X) 
  (hf_mono : Monotone f)
  (hf_le : ∀ s, s ⊆ f s)
  (hf_idem : ∀ s, f (f s) = f s)

/-- 任意の閉包作用から ClosureOp を構成 -/
def mkClosureOp : ClosureOp X where
  cl := f
  mono := hf_mono
  le_closure := hf_le
  idempotent := hf_idem

/-- 空集合からの安定化例 -/
example [Finite X] : 
    (mkClosureOp f hf_mono hf_le hf_idem).rankStab ∅ ≠ ⊤ := by
  apply ClosureOp.finite_rankStab_ne_top

end SubsetClosure

/-! ## 具体例2: 整数の絶対値による閉包 -/

section IntAbsClosure

/-- 整数集合の閉包：絶対値が最大の要素まで含む -/
def intAbsCl (s : Set ℤ) : Set ℤ :=
  if s.Nonempty then
    {z : ℤ | ∃ w ∈ s, |z| ≤ |w|}
  else
    ∅

/-- intAbsCl は単調 -/
theorem intAbsCl_mono : Monotone intAbsCl := by
  sorry -- TODO: reason="proof pending", follow_up="formalize in mathlib"

/-- intAbsCl は拡大的 -/
theorem intAbsCl_le (s : Set ℤ) : s ⊆ intAbsCl s := by
  sorry -- TODO: reason="proof pending", follow_up="formalize in mathlib"

/-- intAbsCl は冪等的 -/
theorem intAbsCl_idem (s : Set ℤ) : intAbsCl (intAbsCl s) = intAbsCl s := by
  sorry -- TODO: reason="proof pending", follow_up="formalize in mathlib"

/-- ℤ の閉包作用素 -/
def intAbsClosureOp : ClosureOp ℤ :=
  mkClosureOp intAbsCl intAbsCl_mono intAbsCl_le intAbsCl_idem

/-- 単集合の安定化は1回 -/
example (n : ℤ) : 
    intAbsClosureOp.StabilizesAt {n} 1 := by
  sorry -- TODO: reason="proof pending", follow_up="formalize in mathlib"

end IntAbsClosure

/-! ## 具体例3: 自然数の上界閉包 -/

section NatUpperClosure

/-- 自然数集合の閉包：最大値以下の全要素 -/
def natUpperCl (s : Set ℕ) : Set ℕ :=
  if h : s.Nonempty ∧ BddAbove s then
    {n : ℕ | n ≤ sSup s}
  else
    s

theorem natUpperCl_mono : Monotone natUpperCl := by
  sorry -- TODO: reason="proof pending", follow_up="formalize in mathlib"

theorem natUpperCl_le (s : Set ℕ) : s ⊆ natUpperCl s := by
  sorry -- TODO: reason="proof pending", follow_up="formalize in mathlib"

theorem natUpperCl_idem (s : Set ℕ) : 
    natUpperCl (natUpperCl s) = natUpperCl s := by
  sorry -- TODO: reason="proof pending", follow_up="formalize in mathlib"

def natUpperClosureOp : ClosureOp ℕ :=
  mkClosureOp natUpperCl natUpperCl_mono natUpperCl_le natUpperCl_idem

/-- 有限集合は1回で安定 -/
example (S : Finset ℕ) : 
    natUpperClosureOp.StabilizesAt (S : Set ℕ) 1 := by
  sorry -- TODO: reason="proof pending", follow_up="formalize in mathlib"

end NatUpperClosure

end GaloisRank
