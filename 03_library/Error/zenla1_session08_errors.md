# zenla1_session08.lean ビルドエラー整理（2025-09-19）

## 1. 初回 `lake build MyProjects.LinearAlgebra.A1.zenla1_session08`
- `unexpected token 'in'` （36行目, 40行目）: `∑ j in cols` 形式をそのまま書いたため構文エラー。`Finset.sum` を用いる形に書き換えて解消。
- `failed to synthesize Decidable (areColsIndependent …)` / `failed to synthesize Decidable (areRowsIndependent …)`: 古典選言法を使う定義だったので `classical` ブロックを追加し、`Finset.max'` を `noncomputable` 定義で包んで対応。
- `Type mismatch … k : Fin m` → `Fin n`: `isRowEchelon` で行添字と列添字を混同していたため、`i j : Fin m` と `k : Fin n` を分離して定義を修正。
- `failed to compile definition … Real.decidableEq`: `rank`・`rowRank`・`pivotCol`・`nullity` を `noncomputable` 宣言し、Lean が暗黙に `Real` の可決性を要求しないようにした。
- Q3, Q4, Q5 での `unsolved goals`: 各行列要素の具体的な数値計算が不足していたため、後続で `norm_num` や `simp` を使った補題に書き換え。

## 2. 中間ビルド
- `unsolved goals`（case `right.right`）: Q2 の座標ごとの等式から係数を求め切れていなかった。`simp` で得た結果を `hc₁`, `hc₂` として明示し、結論を得る形に修正。
- `A'` に関する等式未証明: Q5 で `A' 0 2 = 4` を直接示すため、`simp` と `norm_num` を組み合わせて値を算出し、非零性を導いた。

## 3. 最終ビルド
- Q3 の `fin_cases` 後に係数比較が解決できず `unsolved goals`: 各場合分けで `simp` / `norm_num` を用い、具体的な積 `2 * 2 = 4` などを補題として明示。
- 最終ビルドは警告 (`try 'simp' instead of 'simpa'`) のみで完了。必要に応じて `simp` への置換を検討可能。

---
全ての `sorry` を除去した後、`lake build MyProjects.LinearAlgebra.A1.zenla1_session08` は成功しました（上記警告のみ）。
