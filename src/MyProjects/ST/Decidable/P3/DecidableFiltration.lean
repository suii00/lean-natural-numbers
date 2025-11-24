import MyProjects.ST.Decidable.P1.DecidableEvents
import MyProjects.ST.Decidable.P2.DecidableAlgebra

open Classical Prob

/-- 離散フィルトレーション：時刻ごとの有限代数が単調に増加する構造。 -/
structure DecidableFiltration (Ω : Prob.FiniteSampleSpace) where
  timeHorizon : ℕ
  observableAt :
    (t : ℕ) → (h : t ≤ timeHorizon) → Prob.FiniteAlgebra Ω.carrier
  monotone :
    ∀ (s t : ℕ) (hs : s ≤ timeHorizon) (ht : t ≤ timeHorizon),
      s ≤ t → (observableAt s hs) ⊆ₐ (observableAt t ht)

namespace DecidableFiltration

variable {Ω : Prob.FiniteSampleSpace}

/-- 初期の代数（時刻 0）。 -/
def initialAlgebra (ℱ : DecidableFiltration Ω) :
    Prob.FiniteAlgebra Ω.carrier :=
  ℱ.observableAt 0 (Nat.zero_le _)

/-- 最終時刻の代数（timeHorizon）。 -/
def finalAlgebra (ℱ : DecidableFiltration Ω) :
    Prob.FiniteAlgebra Ω.carrier :=
  ℱ.observableAt ℱ.timeHorizon (Nat.le_refl _)

end DecidableFiltration

/-- 停止時間：各時刻 t で {τ ≤ t} が可観測である。 -/
structure StoppingTime {Ω : Prob.FiniteSampleSpace}
    (ℱ : DecidableFiltration Ω) where
  time : Ω.carrier → ℕ
  adapted :
    ∀ (t : ℕ) (ht : t ≤ ℱ.timeHorizon),
      {ω : Ω.carrier | time ω ≤ t} ∈ (ℱ.observableAt t ht).events

namespace StoppingTime

variable {Ω : Prob.FiniteSampleSpace} {ℱ : DecidableFiltration Ω}

/-- 停止時間の点ごとの順序。 -/
instance : LE (StoppingTime ℱ) where
  le τ₁ τ₂ := ∀ ω, τ₁.time ω ≤ τ₂.time ω

lemma le_def {τ₁ τ₂ : StoppingTime ℱ} :
    τ₁ ≤ τ₂ ↔ ∀ ω, τ₁.time ω ≤ τ₂.time ω := Iff.rfl

/-- 定数停止時間 c（c が終端時刻以下）。 -/
def const (ℱ : DecidableFiltration Ω) (c : ℕ) (hc : c ≤ ℱ.timeHorizon) :
    StoppingTime ℱ where
  time := fun _ => c
  adapted := by
    intro t ht
    by_cases hct : c ≤ t
    · have hset : {ω : Ω.carrier | c ≤ t} = (Set.univ : Set Ω.carrier) := by
        ext ω; simp [hct]
      have h := Prob.FiniteAlgebra.has_univ (ℱ.observableAt t ht)
      simpa [hset] using h
    · have hset : {ω : Ω.carrier | c ≤ t} = (∅ : Set Ω.carrier) := by
        ext ω; simp [hct]
      have h := (ℱ.observableAt t ht).has_empty
      have h' : (∅ : Set Ω.carrier) ∈ (ℱ.observableAt t ht).events := by
        simpa [Prob.Event.empty] using h
      simpa [hset] using h'

/-- 停止時間が上から N で抑えられること。 -/
def isBounded (τ : StoppingTime ℱ) (N : ℕ) : Prop :=
  ∀ ω, τ.time ω ≤ N

/-- 定数停止時間はその値で有界。 -/
lemma const_isBounded (ℱ : DecidableFiltration Ω) (c : ℕ) (hc : c ≤ ℱ.timeHorizon) :
    StoppingTime.isBounded (StoppingTime.const ℱ c hc) c := by
  intro ω
  simp [StoppingTime.const]

/-- 2 つの停止時間の min。 -/
def min (τ₁ τ₂ : StoppingTime ℱ) : StoppingTime ℱ where
  time := fun ω => Nat.min (τ₁.time ω) (τ₂.time ω)
  adapted := by
    intro t ht
    have h1 : {ω : Ω.carrier | τ₁.time ω ≤ t} ∈ (ℱ.observableAt t ht).events :=
      τ₁.adapted t ht
    have h2 : {ω : Ω.carrier | τ₂.time ω ≤ t} ∈ (ℱ.observableAt t ht).events :=
      τ₂.adapted t ht
    have hUnion := (ℱ.observableAt t ht).closed_union h1 h2
    classical
    have hset :
        {ω : Ω.carrier | Nat.min (τ₁.time ω) (τ₂.time ω) ≤ t} =
          ({ω | τ₁.time ω ≤ t} ∪ {ω | τ₂.time ω ≤ t}) := by
      ext ω; constructor
      · intro hmin_le_t
        -- min ≤ t ならどちらか一方が t 以下
        have hle : τ₁.time ω ≤ τ₂.time ω ∨ τ₂.time ω ≤ τ₁.time ω :=
          le_total _ _
        cases hle with
        | inl hle =>
            have hmin : Nat.min (τ₁.time ω) (τ₂.time ω) = τ₁.time ω :=
              Nat.min_eq_left hle
            have hineq : τ₁.time ω ≤ t := by
              have h' : Nat.min (τ₁.time ω) (τ₂.time ω) ≤ t := hmin_le_t
              -- 書き換えだけで済ませて simp による min 展開を避ける
              simpa [hmin] using h'
            left; exact hineq
        | inr hle =>
            have hmin : Nat.min (τ₁.time ω) (τ₂.time ω) = τ₂.time ω :=
              Nat.min_eq_right hle
            have hineq : τ₂.time ω ≤ t := by
              have h' : Nat.min (τ₁.time ω) (τ₂.time ω) ≤ t := hmin_le_t
              simpa [hmin] using h'
            right; exact hineq
      · intro hdisj; rcases hdisj with h₁ | h₂
        · exact le_trans (Nat.min_le_left _ _) h₁
        · exact le_trans (Nat.min_le_right _ _) h₂
    simpa [hset, Prob.Event.union] using hUnion

/-- 2 つの停止時間の max。 -/
def max (τ₁ τ₂ : StoppingTime ℱ) : StoppingTime ℱ where
  time := fun ω => Nat.max (τ₁.time ω) (τ₂.time ω)
  adapted := by
    intro t ht
    have h1 : {ω : Ω.carrier | τ₁.time ω ≤ t} ∈ (ℱ.observableAt t ht).events :=
      τ₁.adapted t ht
    have h2 : {ω : Ω.carrier | τ₂.time ω ≤ t} ∈ (ℱ.observableAt t ht).events :=
      τ₂.adapted t ht
    have hInter := Prob.FiniteAlgebra.closed_intersection
      (ℱ := ℱ.observableAt t ht) h1 h2
    classical
    have hset :
        {ω : Ω.carrier | Nat.max (τ₁.time ω) (τ₂.time ω) ≤ t} =
          {ω : Ω.carrier | τ₁.time ω ≤ t ∧ τ₂.time ω ≤ t} := by
      ext ω; constructor
      · intro h
        exact ⟨le_trans (Nat.le_max_left _ _) h, le_trans (Nat.le_max_right _ _) h⟩
      · intro h; rcases h with ⟨h1ω, h2ω⟩
        exact (max_le_iff).2 ⟨h1ω, h2ω⟩
    have hset' :
        {ω : Ω.carrier | τ₁.time ω ≤ t ∧ τ₂.time ω ≤ t} =
          ({ω | τ₁.time ω ≤ t} ∩ {ω | τ₂.time ω ≤ t}) := by
      ext ω; simp
    simpa [hset, hset', Prob.Event.intersection] using hInter

lemma min_le_left (τ₁ τ₂ : StoppingTime ℱ) : min τ₁ τ₂ ≤ τ₁ := by
  intro ω; simp [StoppingTime.min, Nat.min_le_left]

lemma min_le_right (τ₁ τ₂ : StoppingTime ℱ) : min τ₁ τ₂ ≤ τ₂ := by
  intro ω; simp [StoppingTime.min, Nat.min_le_right]

lemma le_max_left (τ₁ τ₂ : StoppingTime ℱ) : τ₁ ≤ max τ₁ τ₂ := by
  intro ω; simp [StoppingTime.max, Nat.le_max_left]

lemma le_max_right (τ₁ τ₂ : StoppingTime ℱ) : τ₂ ≤ max τ₁ τ₂ := by
  intro ω; simp [StoppingTime.max, Nat.le_max_right]

lemma min_isBounded
    (τ₁ τ₂ : StoppingTime ℱ) (N₁ N₂ : ℕ)
    (h1 : isBounded τ₁ N₁) (h2 : isBounded τ₂ N₂) :
    isBounded (min τ₁ τ₂) (Nat.min N₁ N₂) := by
  intro ω
  have h1ω := h1 ω
  have h2ω := h2 ω
  have h_le1 : Nat.min (τ₁.time ω) (τ₂.time ω) ≤ N₁ :=
    le_trans (Nat.min_le_left _ _) h1ω
  have h_le2 : Nat.min (τ₁.time ω) (τ₂.time ω) ≤ N₂ :=
    le_trans (Nat.min_le_right _ _) h2ω
  exact le_min h_le1 h_le2

lemma max_isBounded
    (τ₁ τ₂ : StoppingTime ℱ) (N₁ N₂ : ℕ)
    (h1 : isBounded τ₁ N₁) (h2 : isBounded τ₂ N₂) :
    isBounded (max τ₁ τ₂) (Nat.max N₁ N₂) := by
  intro ω
  have h1ω := h1 ω
  have h2ω := h2 ω
  have h1bound : τ₁.time ω ≤ Nat.max N₁ N₂ :=
    le_trans h1ω (Nat.le_max_left _ _)
  have h2bound : τ₂.time ω ≤ Nat.max N₁ N₂ :=
    le_trans h2ω (Nat.le_max_right _ _)
  exact max_le_iff.mpr ⟨h1bound, h2bound⟩

end StoppingTime

/-- 全時刻で同じ代数を返す「定数フィルトレーション」。 -/
def constFiltration (Ω : Prob.FiniteSampleSpace)
    (F : Prob.FiniteAlgebra Ω.carrier) (N : ℕ) : DecidableFiltration Ω where
  timeHorizon := N
  observableAt := fun _ _ => F
  monotone := by
    intro s t _ _ _; exact Set.Subset.refl _

/-- timeHorizon = 1 の最小例。 -/
def twoStepFiltration (Ω : Prob.FiniteSampleSpace)
    (F0 F1 : Prob.FiniteAlgebra Ω.carrier) (h01 : F0 ⊆ₐ F1) :
    DecidableFiltration Ω where
  timeHorizon := 1
  observableAt := fun t _ =>
    match t with
    | 0 => F0
    | 1 => F1
    | _ => F1 -- t ≤ 1 のため到達しないが、型合わせで F1
  monotone := by
    intro s t hs ht hst
    cases s with
    | zero =>
        cases t with
        | zero =>
            simpa using
              (Prob.FiniteAlgebra.subalgebra_refl (Ω := Ω.carrier) (ℱ := F0))
        | succ t' =>
            have ht0 : t' = 0 := by
              have ht0_le : t' ≤ 0 :=
                Nat.succ_le_succ_iff.mp (by simpa using ht)
              exact Nat.le_antisymm ht0_le (Nat.zero_le _)
            subst ht0
            simpa using h01
    | succ s' =>
        have hs0 : s' = 0 := by
          have hs0_le : s' ≤ 0 :=
            Nat.succ_le_succ_iff.mp (by simpa using hs)
          exact Nat.le_antisymm hs0_le (Nat.zero_le _)
        subst hs0
        have htl : 1 ≤ t := hst
        have ht1 : t = 1 := Nat.le_antisymm ht htl
        subst ht1
        simpa using
          (Prob.FiniteAlgebra.subalgebra_refl (Ω := Ω.carrier) (ℱ := F1))

section Examples

variable (Ω : Prob.FiniteSampleSpace) (F : Prob.FiniteAlgebra Ω.carrier)
variable (F0 F1 : Prob.FiniteAlgebra Ω.carrier) (h01 : F0 ⊆ₐ F1)

/-- const filtration を使った簡単な sanity check。 -/
def exampleFiltration : DecidableFiltration Ω :=
  constFiltration Ω F 3

-- 証明引数は渡さない：型だけ確認する
#check StoppingTime.const (exampleFiltration Ω F) 1
-- ⟹ 1 ≤ (exampleFiltration Ω F).timeHorizon → StoppingTime (exampleFiltration Ω F)

#check StoppingTime.const (exampleFiltration Ω F) 2
-- ⟹ 2 ≤ (exampleFiltration Ω F).timeHorizon → StoppingTime (exampleFiltration Ω F)

/-- twoStepFiltration の簡単な sanity check。 -/

def exampleTwoStep : DecidableFiltration Ω :=
  twoStepFiltration Ω F0 F1 h01

#check exampleTwoStep Ω F0 F1 h01
#check StoppingTime.const (exampleTwoStep Ω F0 F1 h01) 0
#check StoppingTime.const (exampleTwoStep Ω F0 F1 h01) 1


end Examples
