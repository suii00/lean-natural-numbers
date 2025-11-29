/-- 中間ステップ：`E[M_n · 1_{τ=n}]` を `E[M_0]` と `P(τ=n)` に寄せる型だけ。 -/
lemma expected_at_tau_eq_to_probOfEvent
    {Ω : Prob.FiniteSampleSpace} {ℱ : DecidableFiltration Ω}
    (P : Prob.ProbabilityMassFunction Ω)
    (M : SimpleProcess Ω)
    (τ : ComputableStoppingTime ℱ)
    (n : ℕ) :
  Prob.ProbabilityMassFunction.expected P
      (fun ω => M n ω * (if τ.time ω = n then 1 else 0)) =
    Prob.ProbabilityMassFunction.expected P (M 0) *
      Prob.ProbabilityMassFunction.probOfEvent P (eventTauEq (ℱ := ℱ) τ n) := by
  -- TODO: 将来の OST 証明で埋める
  -- ヒント:
  -- 1) `expected_at_tau_eq_as_event` で eventTauEq 版に書き換え
  -- 2) `martingale_expectation_const` から `E[M_n] = E[M_0]` を得る
  -- 3) `expected_indicator` / `expected_indicator_mul` を使い、M を E[M_0] に分離
  sorry