# エラーと対処法まとめ

## `Matrix.dotProduct` 関連エラー
- **症状**: `Unknown constant Matrix.dotProduct`。
- **対処**: 不要な `Matrix.dotProduct` を `simp` 引数から除外し、必要に応じて `norm_num` で計算。

## `b₁` と解ベクトルの不整合
- **症状**: 手計算と Lean 出力が一致しない。
- **対処**: 右辺ベクトルを `![4, 7]` に修正。

## `congrArg` 型不一致
- **症状**: `congrArg (fun v => v 0)` の型が不一致。
- **対処**: 先に `![2, -1, 0] = 0` を示し、その後第 0 成分を参照して矛盾を導出。

## モジュール名の不一致
- **症状**: `Mathlib.LinearAlgebra.dotProduct` が見つからない。
- **対処**: `Mathlib.LinearAlgebra.Matrix.DotProduct` をインポート。

## `norm_num` のみではゴールが解消しない
- **症状**: `No goals to be solved` などの警告。
- **対処**: `(simp ...; try norm_num)` のように前処理で式を簡約。

## `lake build` タイムアウト
- **症状**: 初回ビルドでタイムアウト。
- **対処**: 再度 `lake build` を実行し、依存モジュールビルド完了後は安定。
