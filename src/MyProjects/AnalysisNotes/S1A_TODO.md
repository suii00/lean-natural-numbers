### TODO（Lean 実装メモ）

- [ ] `S1A.lean:18` 付近の `s1_a_q2` は証明を書き終えたので、`simp` 補題の適用結果を `#check` で確認し `lake build` が通るか最終確認する。
- [ ] `S1A.lean:40` 以降の `s1_a_q5` では `ContinuousOn` から各点での `ContinuousAt` を得た後、`StronglyMeasurableAtFilter` を `ContinuousAt.aestronglyMeasurable` 系の補題に差し替える。
- [ ] `intervalIntegral.continuousWithinAt_primitive` の引数調整用に、`IntervalIntegrable` を `uIcc` へ戻す補題を整理し、`simp [min_eq_left, max_eq_right]` で渡せる形にする。
- [ ] 端点 `x = a, b` の処理では `continuousWithinAt_of_continuousAt`＋`ContinuousOn.continuousAt` を試し、証明を簡潔化できるか検討する。
- [ ] 最後の等式 `(∫ x in a..b, f x) - (b - a) * avg = 0` は `field_simp [avg, hba_ne]` などの補題で処理し、`simp` の未使用引数警告を解消する。
- [ ] `exists_hasDerivAt_eq_zero` の引数順を確認し、`F a = F b` を直接証明してから渡す流れに組み替える。
- [ ] 証明完了後に `lake build MyProjects.AnalysisNotes.S1A` を実行し、必要なら補助補題を別 namespace へ移動する。
