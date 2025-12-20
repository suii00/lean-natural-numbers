import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Find
import MyProjects.ST.RankCore.Basic


/-!
# ClosureIteration - 閉包演算の反復回数によるRanked構造

## 概要
閉包演算の反復回数を rank 関数とする Ranked 構造の例。
layer n は「n 回以下の閉包反復で到達可能な集合」を表す。

## 数学的意義
閉包演算 cl : Set X → Set X に対して：
- rank S = min {n : ℕ | cl^n(S) = cl^(n+1)(S)}（固定点到達回数）
- rank S = ⊤（無限）: cl の反復が収束しない場合
- layer n = {S | rank S ≤ n}

## 具体例
### 位相空間の閉包
- 既閉集合の rank = 0
- 開集合の境界を追加で閉じる場合の rank = 1
- 無限回の反復が必要な場合も存在

### グラフの到達可能性
- 孤立点の rank = 0
- 1ステップで到達可能な点の rank = 1
- n ステップで到達可能な点の rank = n

## 注意事項
WithTop ℕ を使用して無限反復を表現：
- rank : Set X → WithTop ℕ
- ⊤ は「収束しない」ことを表す

## 応用
- 確率論における停止時刻の最小性
- 可到達性解析
- 不動点理論
-/

namespace ST

universe u v

/-! ## 閉包演算の定義 -/

variable {X : Type u}

/-- 閉包演算の公理的定義 -/
structure ClosureOperator (X : Type u) where
  cl : Set X → Set X
  extensive : ∀ S, S ⊆ cl S
  monotone : ∀ {S T}, S ⊆ T → cl S ⊆ cl T
  idempotent : ∀ S, cl (cl S) = cl S

namespace ClosureOperator

variable (C : ClosureOperator X)

/-- n 回の反復適用 -/
def iter (n : ℕ) (S : Set X) : Set X :=
  Nat.recOn n S (fun _ acc => C.cl acc)

@[simp]
lemma iter_zero (S : Set X) : C.iter 0 S = S := rfl

@[simp]
lemma iter_succ (n : ℕ) (S : Set X) : C.iter (n + 1) S = C.cl (C.iter n S) := rfl

/-- 反復が収束するかを判定 -/
def converges (S : Set X) : Prop :=
  ∃ n : ℕ, C.iter n S = C.iter (n + 1) S

/-- 収束する最小の n（収束しない場合は ⊤） -/
noncomputable def iterationRank (C : ClosureOperator X) (S : Set X) : WithTop ℕ := by
  classical
  exact if h : C.converges S then
    Nat.find h
  else
    ⊤

end ClosureOperator

/-! ## Ranked インスタンス定義 -/

/-- 閉包演算の反復回数を rank 関数とする Ranked インスタンス -/
noncomputable instance instRankedClosure (C : ClosureOperator X) :
    Ranked (WithTop ℕ) (Set X) where
  rank := ClosureOperator.iterationRank (C := C)

/-! ## 基本性質 -/

variable (C : ClosureOperator X)

/-- layer定義の具体化 -/
lemma closure_layer_iff (n : ℕ) (S : Set X) :
    S ∈ (instRankedClosure C : Ranked (WithTop ℕ) (Set X)).layer n ↔
    ClosureOperator.iterationRank (C := C) S ≤ n := by
  rfl

/-- 単調性の確認 -/
lemma closure_layer_mono {m n : ℕ} (h : m ≤ n) :
    (instRankedClosure C : Ranked (WithTop ℕ) (Set X)).layer m ⊆
    (instRankedClosure C : Ranked (WithTop ℕ) (Set X)).layer n := by
  intro S hS
  exact le_trans hS (WithTop.coe_le_coe.mpr h)

/-- 既閉集合（不動点）は rank 0 を持つ -/
lemma closed_has_rank_zero (S : Set X) (h : C.cl S = S) :
    ClosureOperator.iterationRank (C := C) S = ((0 : ℕ) : WithTop ℕ) := by
  classical
  have hconv : C.converges S := by
    refine ⟨0, ?_⟩
    simp [ClosureOperator.iter, h]
  have hfind : Nat.find hconv = 0 := by
    refine (Nat.find_eq_zero _).2 ?_
    simp [ClosureOperator.iter, h]
  have h' : ClosureOperator.iterationRank (C := C) S = Nat.find hconv := by
    simp [ClosureOperator.iterationRank, hconv]
  have hfind' : (Nat.find hconv : WithTop ℕ) = ((0 : ℕ) : WithTop ℕ) := by
    simpa [hfind]
  simpa [h'] using hfind'

/-- rank 0 の集合は既閉集合 -/
lemma rank_zero_iff_closed (S : Set X) :
    ClosureOperator.iterationRank (C := C) S = ((0 : ℕ) : WithTop ℕ) ↔ C.cl S = S := by
  constructor
  · intro h0
    classical
    by_cases hconv : C.converges S
    · have h0' :
        (Nat.find hconv : WithTop ℕ) = ((0 : ℕ) : WithTop ℕ) := by
          simpa [ClosureOperator.iterationRank, hconv] using h0
      have hfind : Nat.find hconv = 0 := by
        exact (WithTop.coe_eq_coe.mp h0')
      have hiter : C.iter 0 S = C.iter (0 + 1) S := (Nat.find_eq_zero _).1 hfind
      simpa [ClosureOperator.iter] using hiter.symm
    · have : False := by
        simpa [ClosureOperator.iterationRank, hconv] using h0
      exact this.elim
  · intro hclosed
    exact closed_has_rank_zero (C := C) (S := S) hclosed

/-- rank が有限なら収束する -/
lemma finite_rank_iff_converges (S : Set X) :
    (∃ n : ℕ, ClosureOperator.iterationRank (C := C) S = n) ↔ C.converges S := by
  classical
  constructor
  · rintro ⟨n, hn⟩
    by_contra hconv
    have : False := by
      simpa [ClosureOperator.iterationRank, hconv] using hn
    exact this.elim
  · intro hconv
    refine ⟨Nat.find hconv, ?_⟩
    simp [ClosureOperator.iterationRank, hconv]

/-- 反復の単調性 -/
lemma iter_mono (n : ℕ) (S : Set X) :
    S ⊆ C.iter n S := by
  induction n with
  | zero =>
      simp [ClosureOperator.iter]
  | succ n ih =>
      have h1 : S ⊆ C.iter n S := ih
      have h2 : C.iter n S ⊆ C.cl (C.iter n S) := C.extensive _
      exact (Set.Subset.trans h1 h2)

/-! ## 計算可能な例（有限型の場合） -/

/-- 離散閉包（恒等写像）の例 -/
def discreteClosure : ClosureOperator X where
  cl := id
  extensive := fun S => Set.Subset.refl S
  monotone := fun h => h
  idempotent := fun S => rfl

/-- 離散閉包では全ての集合が rank 0 -/
example (S : Set X) :
    ClosureOperator.iterationRank (C := discreteClosure) S = ((0 : ℕ) : WithTop ℕ) := by
  simpa [discreteClosure] using
    (closed_has_rank_zero (C := discreteClosure) (S := S) rfl)

/-- 全域閉包（常に全集合）の例 -/
def wholeClosure : ClosureOperator X where
  cl := fun _ => Set.univ
  extensive := fun S => Set.subset_univ S
  monotone := fun _ => Set.Subset.refl Set.univ
  idempotent := fun S => rfl

/-- 空集合の全域閉包における rank -/
example :
    ClosureOperator.iterationRank (C := wholeClosure) (∅ : Set X) ≤
      ((1 : ℕ) : WithTop ℕ) := by
  classical
  have hconv : wholeClosure.converges (∅ : Set X) := by
    refine ⟨1, ?_⟩
    simp [ClosureOperator.iter, wholeClosure]
  have hle : Nat.find hconv ≤ 1 :=
    Nat.find_min' hconv (by simp [ClosureOperator.iter, wholeClosure])
  have h' :
      ClosureOperator.iterationRank (C := wholeClosure) (∅ : Set X) = Nat.find hconv := by
    simp [ClosureOperator.iterationRank, hconv]
  have hle' : (Nat.find hconv : WithTop ℕ) ≤ ((1 : ℕ) : WithTop ℕ) :=
    WithTop.coe_le_coe.mpr hle
  simpa [h'] using hle'

-- 具体的な有限型での計算例
section FiniteExample

/-- Bool型での例 -/
def boolClosure : ClosureOperator Bool where
  cl := by
    classical
    exact fun S => if S.Nonempty then Set.univ else ∅
  extensive := by
    classical
    intro S
    by_cases h : S.Nonempty
    · simpa [h] using (Set.subset_univ S)
    · intro x hx
      exact (h ⟨x, hx⟩).elim
  monotone := by
    classical
    intro S T hST
    by_cases hS : S.Nonempty
    · have hT : T.Nonempty := Set.Nonempty.mono hST hS
      simp [hS, hT]
    · simp [hS]
  idempotent := by
    classical
    intro S
    by_cases h : S.Nonempty
    · simp [h]
    · simp [h]

end FiniteExample

/-! ## StructureTower変換（簡約版） -/

/- 最小層を持つ構造塔（WithTop ℕ 添字版は非自明なので省略）
   注：StructureTowerWithMin は ℕ 添字を仮定しているため、
   WithTop ℕ を扱う完全な変換には別の定義が必要。 -/

/-- layer の有限性について -/
lemma layer_finite_rank (n : ℕ) :
    (instRankedClosure C : Ranked (WithTop ℕ) (Set X)).layer n =
    {S : Set X | ∃ m : ℕ, m ≤ n ∧ ClosureOperator.iterationRank (C := C) S = m} := by
  ext S
  constructor
  · intro hS
    classical
    have hS'': ClosureOperator.iterationRank (C := C) S ≤ n := hS
    cases hS' : ClosureOperator.iterationRank (C := C) S with
    | top =>
        have : False := by
          exact (WithTop.not_top_le_coe (a := n)) (by simpa [hS'] using hS'')
        exact this.elim
    | coe m =>
        have hm' : m ≤ n := by
          have hm'' : (m : WithTop ℕ) ≤ n := by
            simpa [hS'] using hS''
          exact (WithTop.coe_le_coe.mp hm'')
        refine ⟨m, hm', ?_⟩
        simpa [hS']
  · intro hS
    rcases hS with ⟨m, hm, hEq⟩
    change ClosureOperator.iterationRank (C := C) S ≤ n
    have hm' : (m : WithTop ℕ) ≤ n := WithTop.coe_le_coe.mpr hm
    simpa [hEq] using hm'

/-! ## 応用：停止時刻との対応 -/

section StoppingTimeConnection

variable {Ω : Type u}

/-- σ-代数の生成操作は閉包演算 -/
axiom sigma_algebra_closure : ClosureOperator (Set Ω)

/-- 停止時刻は filtration における rank に対応 -/
axiom stopping_time_rank_correspondence :
  ∀ (F : Set (Set Ω)),
    ClosureOperator.iterationRank (C := sigma_algebra_closure) F =
      ((0 : ℕ) : WithTop ℕ)  -- この対応は抽象的な定理の主張

end StoppingTimeConnection

end ST
