# 遭遇したエラーと対応

- **`unknown module prefix 'Mathlib'`**（`lake env lean zenla1_session07.lean` 実行時）
  - 原因: プロジェクトルート外で Lean を実行し、Lake が設定する依存パスが有効化されていなかった。
  - 対応: リポジトリ直下で `lake build` を実行し、Lake が mathlib などの依存を解決するようにした。

- **`failed to compile definition … consider marking it as 'noncomputable'`**（`det2` や `inv2` 付近）
  - 原因: 実数の逆数を含む定義が計算可能型でないことに起因。
  - 対応: `namespace` 直下に `noncomputable section` を追加して非計算的定義を許容した。

- **`Type mismatch … Mathlib.Meta.NormNum.isNat_eq_false … expected ¬ det2 A = 0`**
  - 原因: `simp` の結果が `True` に簡約され、必要な不等式が得られなかった。
  - 対応: `change A 0 0 * A 1 1 - A 0 1 * A 1 0 ≠ 0` と書き換えてから `norm_num` で直接評価した。

- **`unsolved goals`（Q4 の右逆行列構成時）**
  - 原因: 逆行列候補 `C_inv` の成分が不正確で、行列積の成分がゼロにならなかった。
  - 対応: 成分を `!![1, -1, -2/3; 0, 1/2, -1/6; 0, 0, 1/3]` に修正し、`simp` と `norm_num` で検証した。

- **`Unexpected name 'ZenLA1.Session07' after end`**
  - 原因: `noncomputable section` を追加した際に `end` の対応関係が崩れた。
  - 対応: `end` を 1 行挿入し、`section` と `namespace` の閉じを正しく揃えた。

- **`Unknown identifier 'M'`（Challenge 証明時）**
  - 原因: `let M := …` で導入した識別子を `intro` で上書きしてしまい、以降の `simp` で参照できなくなった。
  - 対応: `intro` を削除し、`simp [M, M_inv, inv2, det2, A]` → `norm_num` に一本化した。

- **`decide` tactic failure for `isInvertible2 A`**
  - 原因: 命題の `Decidable` インスタンスが古典的選択に依存し、`decide` が計算で判定できなかった。
  - 対応: `change … ≠ 0` として明示的に数値評価し、`norm_num` で証明した。
