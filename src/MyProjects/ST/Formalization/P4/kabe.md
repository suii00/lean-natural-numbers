noncomputable def stoppedProcess_martingale_of_bdd (M : Martingale μ)
    (τ : Ω → ℕ)
    (hτ :
      ∀ n, @MeasurableSet Ω (M.filtration n) {ω : Ω | τ ω ≤ n})
    (hτ_bdd : ∃ K, ∀ ω, τ ω ≤ K) :
    Martingale μ := by
  classical
  have h_stop_strong :
      ∀ n,
        StronglyMeasurable[M.filtration n]
          (StructureTowerProbability.stopped M.process τ n) :=
    StructureTowerProbability.stopped_stronglyMeasurable_of_stoppingSets
      (ℱ := M.filtration) (X := M.process)
      (hX := M.adapted) (τ := τ) (hτ := hτ)
  have h_stop_int :
      ∀ n,
        Integrable (StructureTowerProbability.stopped M.process τ n) μ :=
    StructureTowerProbability.stopped_integrable_of_bdd
      (ℱ := M.filtration) (X := M.process)
      (hX := M.integrable) (τ := τ) (hτ := hτ) (hτ_bdd := hτ_bdd)
  refine
    { filtration := M.filtration
      process := M.stoppedProcess τ
      adapted := ?_
      integrable := ?_
      martingale := ?_ }
  · intro n
    simpa [Martingale.stoppedProcess] using h_stop_strong n
  · intro n
    simpa [Martingale.stoppedProcess] using h_stop_int n
  · intro n
    classical
    have h_stop_int_n := h_stop_int n
    have h_stop_int_succ := h_stop_int (n + 1)
    have h_diff_int :
        Integrable
          (fun ω =>
            M.stoppedProcess τ (n + 1) ω - M.stoppedProcess τ n ω) μ :=
      h_stop_int_succ.sub h_stop_int_n
    have h_cond_split :
        condExp μ M.filtration n (M.stoppedProcess τ (n + 1)) =ᵐ[μ]
          condExp μ M.filtration n (M.stoppedProcess τ n) +
            condExp μ M.filtration n
              (fun ω =>
                M.stoppedProcess τ (n + 1) ω - M.stoppedProcess τ n ω) := by
      have h_add :=
        (MeasureTheory.condExp_add
            (μ := μ) (m := M.filtration n)
            (hf := h_stop_int_n) (hg := h_diff_int))
      have h_sum :
          (fun ω =>
              M.stoppedProcess τ n ω +
                (M.stoppedProcess τ (n + 1) ω - M.stoppedProcess τ n ω)) =
            fun ω => M.stoppedProcess τ (n + 1) ω := by
        funext ω; simp
      have h_sum_ae :
          (fun ω =>
              M.stoppedProcess τ n ω +
                (M.stoppedProcess τ (n + 1) ω - M.stoppedProcess τ n ω)) =ᵐ[μ]
            fun ω => M.stoppedProcess τ (n + 1) ω :=
        Filter.EventuallyEq.of_eq h_sum
      have h_congr := MeasureTheory.condExp_congr_ae h_sum_ae
      exact h_congr.trans h_add
    have h_stop_meas :
        StronglyMeasurable[M.filtration n] (M.stoppedProcess τ n) := by
      simpa [Martingale.stoppedProcess] using h_stop_strong n
    have h_cond_stop_eq :
        condExp μ M.filtration n (M.stoppedProcess τ n)
          = M.stoppedProcess τ n :=
      MeasureTheory.condExp_of_stronglyMeasurable
        (hm := M.filtration.le n)
        (hf := h_stop_meas)
        (hfi := h_stop_int_n)
    have h_cond_stop :
        condExp μ M.filtration n (M.stoppedProcess τ n)
          =ᵐ[μ] M.stoppedProcess τ n :=
      Filter.EventuallyEq.of_eq h_cond_stop_eq
    have h_diff_fun :
        (fun ω =>
            M.stoppedProcess τ (n + 1) ω - M.stoppedProcess τ n ω)
          =
            fun ω =>
              Set.indicator {ω : Ω | τ ω > n}
                (fun ω =>
                  M.process (n + 1) ω - M.process n ω) ω := by
      funext ω
      simpa [Martingale.stoppedProcess] using
        (Martingale.stoppedProcess_increment_indicator
          (M := M) (τ := τ) (n := n) (ω := ω))
    have h_meas :
        @MeasurableSet Ω (M.filtration n)
          {ω : Ω | τ ω > n} := by
      have h_le := hτ n
      have h_eq :
          {ω : Ω | τ ω > n}
            = ({ω : Ω | τ ω ≤ n})ᶜ := by
        ext ω; simp [Set.mem_setOf_eq, not_le]
      simpa [h_eq] using h_le.compl
    have hΔ_int :
        Integrable
          (fun ω =>
            M.process (n + 1) ω - M.process n ω) μ :=
      (M.integrable (n + 1)).sub (M.integrable n)
    have h_cond_sub :
        condExp μ M.filtration n
            (fun ω =>
              M.process (n + 1) ω - M.process n ω)
          =ᵐ[μ]
            condExp μ M.filtration n (M.process (n + 1)) -
              condExp μ M.filtration n (M.process n) := by
      simpa [condExp] using
        (MeasureTheory.condExp_sub
          (μ := μ) (m := M.filtration n)
          (hf := M.integrable (n + 1))
          (hg := M.integrable n))
    have h_cond_proc_eq :
        condExp μ M.filtration n (M.process n) = M.process n :=
      MeasureTheory.condExp_of_stronglyMeasurable
        (hm := M.filtration.le n)
        (hf := M.adapted n)
        (hfi := M.integrable n)
    have h_cond_proc :
        condExp μ M.filtration n (M.process n) =ᵐ[μ] M.process n :=
      Filter.EventuallyEq.of_eq h_cond_proc_eq
    have hΔ_cond :
        condExp μ M.filtration n
            (fun ω =>
              M.process (n + 1) ω - M.process n ω)
          =ᵐ[μ] 0 := by
      refine h_cond_sub.trans ?_
      have h_diff_zero :
          (fun ω =>
              condExp μ M.filtration n (M.process (n + 1)) ω +
                (-condExp μ M.filtration n (M.process n) ω))
            =ᵐ[μ]
              fun ω =>
                M.process n ω + (-M.process n ω) := by
        refine (M.martingale n).add ?_
        have h_cond_proc_neg :
            (fun ω =>
                -condExp μ M.filtration n (M.process n) ω)
              =ᵐ[μ]
                fun ω =>
                  -M.process n ω := by
          exact h_cond_proc.neg
        exact h_cond_proc_neg
      have h_zero_eq :
          (fun ω =>
              M.process n ω + (-M.process n ω))
            = fun _ => 0 := by
        funext ω; simp
      have h_zero := Filter.EventuallyEq.of_eq h_zero_eq
      exact h_diff_zero.trans h_zero
    have h_indicator :
        condExp μ M.filtration n
            (fun ω =>
              Set.indicator {ω : Ω | τ ω > n}
                (fun ω =>
                  M.process (n + 1) ω - M.process n ω) ω)
          =ᵐ[μ]
        fun ω =>
          Set.indicator {ω : Ω | τ ω > n}
            (fun ω =>
              condExp μ M.filtration n
                (fun ω =>
                  M.process (n + 1) ω - M.process n ω) ω) ω := by
      simpa [condExp] using
        (MeasureTheory.condExp_indicator
          (μ := μ) (m := M.filtration n)
          (hf_int := hΔ_int) (hs := h_meas))
    have h_cond_delta :
        condExp μ M.filtration n
            (fun ω =>
              M.stoppedProcess τ (n + 1) ω - M.stoppedProcess τ n ω)
          =ᵐ[μ] 0 := by
      have h_delta' :
          condExp μ M.filtration n
              (fun ω =>
                M.stoppedProcess τ (n + 1) ω - M.stoppedProcess τ n ω)
            =ᵐ[μ]
              condExp μ M.filtration n
                (fun ω =>
                  Set.indicator {ω : Ω | τ ω > n}
                    (fun ω =>
                      M.process (n + 1) ω - M.process n ω) ω) := by
        refine condExp_congr_ae ?_
        simpa [h_diff_fun]
      refine h_delta'.trans ?_
      refine h_indicator.trans ?_
      have h_indicator_zero :
          (fun ω =>
              Set.indicator {ω : Ω | τ ω > n}
                (fun ω =>
                  condExp μ M.filtration n
                    (fun ω =>
                      M.process (n + 1) ω - M.process n ω) ω) ω) =
           ᵐ[μ]
            fun ω =>
              Set.indicator {ω : Ω | τ ω > n}
                (fun _ : Ω => (0 : ℝ)) ω := by
        refine hΔ_cond.mono ?_
        intro ω hω
        by_cases hmem : ω ∈ {ω : Ω | τ ω > n}
        · simp [Set.indicator_of_mem, hmem, hω]
        · simp [Set.indicator_of_notMem, hmem]
      have h_indicator_zero_eq :
          (fun ω =>
              Set.indicator {ω : Ω | τ ω > n}
                (fun _ : Ω => (0 : ℝ)) ω)
            = fun _ => 0 := by
        funext ω; by_cases hmem : ω ∈ {ω : Ω | τ ω > n}; simp [hmem]
      exact h_indicator_zero.trans (Filter.EventuallyEq.of_eq h_indicator_zero_eq)
    have h_rhs :
        (fun ω =>
            condExp μ M.filtration n (M.stoppedProcess τ n) ω +
              condExp μ M.filtration n
                (fun ω => M.stoppedProcess τ (n + 1) ω - M.stoppedProcess τ n ω) ω)
          =ᵐ[μ] M.stoppedProcess τ n := by
      have h_sum := (h_cond_stop.add h_cond_delta)
      refine h_sum.trans ?_
      have h_final :
          (fun ω => M.stoppedProcess τ n ω + 0) =
            fun ω => M.stoppedProcess τ n ω := by
        funext ω; simp
      exact Filter.EventuallyEq.of_eq h_final
    exact h_cond_split.trans h_rhs

end Martingale