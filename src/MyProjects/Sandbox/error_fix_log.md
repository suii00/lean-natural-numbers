# エラー修正ログ

- エラー概要：
  - `bad import` によるビルド失敗（`Mathlib.Probability.Distributions.Gaussian` ほか）
  - `Unknown constant EReal.ofReal`
  - `omega` 失敗による Fin インデックスの証明失敗
  - `unexpected identifier; expected 'lemma'`（ドックコメントの形式不備）
  - `AsymptoticallyNormal` が未定義として扱われる（`constant` の扱い）
  - `OfNat (Fin k) 0` など Fin の数値同型の不整合

- 原因：
  - mathlib の当該モジュールはディレクトリ構成で、`Basic` 等の子ファイルを import する必要があった。
  - `EReal` への埋め込みは `EReal.ofReal` ではなく、`(x : EReal)` の coercion を使う設計。
  - `omega` は `Fin` のインデックス生成に必要な不等式を自動で解けなかった。
  - `/- ... -/` はコメントであり、`/-- ... -/` がドックコメント。`constant` の直前にコメントを置くと構文エラーになる。
  - `constant` は `autoImplicit` の影響で未定義扱いになり、関数型として解釈されず失敗。
  - `Fin k` への `0` リテラルは `OfNat` のインスタンスがなく、そのままでは使えない。

- 修正内容：
  - import を実ファイルに合わせて差し替え：
    - `Mathlib.Probability.Distributions.Gaussian.Basic`
    - `Mathlib.MeasureTheory.Integral.Bochner.Basic`
    - `Mathlib.Order.BoundedOrder.Basic`
  - `EReal.ofReal` を `(x : EReal)` へ置換し、`Mathlib.Data.EReal.Basic` を追加。
  - `categoryProbability` のインデックス生成を `omega` 依存から手書きの不等式証明へ変更。
  - `LatentVariableModel` に `hk : 1 < k` を追加し、`k-1` の範囲で安全に index を構成。
  - `AsymptoticallyNormal` を `axiom` に変更（構文エラーと未定義問題を回避）。
  - `categoryProbability` で `j.val` を使った `Nat` レベルの分岐へ再構成。
  - ドックコメントの形式を `axiom` に合わせて修正。

- 修正が正しい理由：
  - すべての import は実在ファイルに対応し、mathlib の構成と整合する。
  - `EReal` への埋め込みは coercion が標準であり、`ofReal` 不在のエラーを解消する。
  - `Fin (k-1)` の index は `k > 1` を前提に構成するのが正しい。
  - `categoryProbability` は「最小・最大・中間カテゴリ」の区分を `Nat` 比較で表現でき、定義意図を保持する。
  - `axiom` 化は「ブルバキ流の公理化」方針と整合し、証明未整備部分の公開 API を維持する。

- 動作確認：
  - `lake build MyProjects.Sandbox.polyserial_correlation` を実行して成功。
  - 警告のみ（未使用変数）で、コンパイルは通過。

- どういう意図でこの実装に至ったかメモ：
  - 数学的本質（正規分布や尤度の解析）は一旦公理として切り分け、集合論的・構造的な API を先に安定化させる方針を採用。
  - mathlib の構成と `Fin` の境界条件を厳密に守ることで、将来の証明追加時に破綻しない土台を作ることを優先。
  - 解析的な補題は後続の証明フェーズへ回しつつ、型の整合性とビルド安定性を先に確保した。
