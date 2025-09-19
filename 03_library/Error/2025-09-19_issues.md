# S1.lean 作業で遭遇した問題まとめ

## 主なビルドエラー
- `Continuous.intervalIntegrable` を直接呼び出した際、既定引数が `fun x => m * x` などと一致せず、「Type mismatch」警告が発生。`(continuous_const : Continuous _)` や `continuous_id` に明示的に `μ := MeasureTheory.volume` を渡す必要がある。
- `intervalIntegral.integral_add` の戻り値が `∫ (m * x + n) = (∫ m * x) + ∫ n` 形式で返るため、左辺の `+` を並べ替える追加の `simp [add_comm]` が必要だった。
- `intervalIntegral.integral_const_mul` に引数名 `c` を渡したところ "Invalid argument name" エラー。実際には `r := _` を指定するか、先に `simp` で形を揃える必要がある。
- `intervalIntegral.integral_pow` が未知定数扱いになり、`import Mathlib` だけでは見つからなかった。必要なファイル（`Mathlib/Analysis/SpecialFunctions/Integrability/Basic`）の明示的な import が欠けている可能性。
- `intervalIntegral.integral_comp_neg` などの値替えで得られる式の項順が Lean の既定順序と異なり、`simpa [add_comm]` 等で秩序を合わせないと `Type mismatch` が残る。
- `IntervalIntegrable.const_mul` や `intervalIntegral.integral_add_adjacent_intervals` を使った際、`mono_set` に渡す補題が未整備で、`Set.uIcc_subset_uIcc` の補助補題を自作する必要が生じた。

## 未解決の課題
- 線形関数 `m * x + n` の積分を `intervalIntegral.integral_eq_sub_of_hasDerivAt` を使って証明する方針は残るが、原始関数の評価式の整理（特に 2 倍してから割り戻す処理）が未完成。
- 絶対値関数 `|x|` の積分で、区間分割後の等式整理 (`hsplit`) が `∫(-1..0) + ∫(0..2)` の順序に揃っておらず、`simp` を挟む必要がある。
- even/odd 分解を利用した Challenge の証明で、`Set.EqOn` を用いた integrand 差し替えと `IntervalIntegrable.const_mul` のパラメタ指定が未確定のまま。
- `HasDerivAt` を使った補題作成時、`hasDerivAt_pow` や `hasDerivAt_mul_const` などの組合せで型が一致しない箇所が残存。証明済み補題 (`deriv` 版) を利用するか、対応する `simp` セットを調整する必要がある。

## 補助情報
- 関連ドキュメント
  - [`intervalIntegral.intervalIntegrable_pow`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Integrability/Basic.html#intervalIntegral.intervalIntegrable_pow)
  - [`intervalIntegral.integral_eq_sub_of_hasDerivAt`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.html#intervalIntegral.integral_eq_sub_of_hasDerivAt)
