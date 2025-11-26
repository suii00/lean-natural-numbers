### エラー修正ログ（AlgorithmicMartingale_old.lean : `expected_const`）

- エラー概要：`expected_const` の証明で `NonUnitalNonAssocSemiring ℚ` を合成できず、`Finset.mul_sum` の向きも合わず型が一致しなかった。
- 原因：`ℚ` の環インスタンスを提供する `Mathlib.Algebra.Field.Rat` を import しておらず、`Finset.mul_sum` が返す等式の向きと期待する形が逆だった。
- 修正内容：
  - `Mathlib.Algebra.Field.Rat` を追加インポートし、ℚ の `Semiring`/`NonUnitalNonAssocSemiring` インスタンスを明示的に利用可能にした。
  - `Finset.mul_sum` の結果を `this.symm` で反転し、`hmul` の型を `∑ ω, c * P.pmf ω = c * ∑ ω, P.pmf ω` に整合。
- 修正が正しい理由：`Mathlib.Algebra.Field.Rat` は ℚ の標準環構造を定義しており、これにより `Finset.mul_sum` が要求する型クラスが解決される。等式の向きを反転するだけで内容は同値であり、計算手順は期待値の線形性と有限和の分配法則に沿っている。
- 動作確認：`lake env lean src/MyProjects/ST/Decidable/P5/AlgorithmicMartingale_old.lean` を実行し、該当エラーが解消されることを確認（警告のみ残存）。
- どういう意図でこの実装に至ったかメモ：最小限の変更で局所エラーだけ直す方針。非構造的なコメントアウトや大規模リファクタを避け、導入依存を 1 行追加・計算等式を向き調整するのみで対応した。
