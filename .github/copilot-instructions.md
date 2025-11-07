 

このリポジトリはLean/Mathlibベースの形式化作業（確率論と構造塔）です。AIアシスタント向けに最短で有用に振る舞うための要点をまとめます。

- 主要な意図: 数学的抽象（Structure Tower）と確率論（フィルトレーション、停止時刻、マルチンゲール）をLeanで形式化すること。多くのファイルはMathlib4のモジュールをimportしています（例: `Probability.lean`, `Phase1_PRAGMATIC.lean`, `Level2_1_Martingale_Guide.lean`）。

- 重要ファイル（参照用）:
  - `src/MyProjects/ST/Probability.lean` — フィルトレーション、minLayer、StoppingTime の基本
  - `src/MyProjects/ST/Phase1_PRAGMATIC.lean` — Mathlib へのブリッジ（toMathlib 等の変換補題あり）
  - `src/MyProjects/ST/Implementation_Guide.md` と `README_Complete_Guide.md` — 実装方針と証明戦略の具体例
  - `src/MyProjects/ST/Level2_1_Martingale_Guide.lean` — レベル2（マルチンゲール）作業の開始点

- コードベース上の明確なパターン:
  - 抽象化優先: 測度論的な詳細は最初に抽象化（axiom / sorry）しておき、後でMathlibの補題へ置き換える流れ。
  - 変換補題: `toMathlib` のような補題を置いて自作の構造と Mathlib の型を橋渡ししている（例: `Phase1_Simplified.lean`）。新たに証明を加える際はまずMathlibへの変換を探す。
  - `minLayer` と `DiscreteFiltration` が中心的な設計要素。停止時刻や最小層の性質を証明する際はこれらの定義を直接参照する。

- 期待されるワークフロー（AIが行う具体的行動）:
  1. 変更は小さく保つ（1つの補題/例/証明を追加）
  2. 既存の `toMathlib` / `filtrationOf` などの橋渡し補題を探し、それを使ってMathlibの結果を活用
  3. `sorry` を使う箇所は明確にコメントし、後でMathlib補題で置換可能かを注記する
  4. 例（`example`）を追加して新補題の「簡単なケース」を検証

- リポジトリ固有の注意点（明示的に扱うべき点）:
  - 多くのファイルで `MeasurableSingletonClass` や `MeasurableSpace` に関する条件が問題になっている（例: `minLayerStoppingTime` の証明）。単点可測性が必要なら `MeasurableSingletonClass` を導入する選択を検討する。
  - 自然フィルトレーションはしばしばより弱い `GeneralFiltration` に落とす方針がとられている。破壊的なAPI変更は避ける。
  - Mathlib の存在を前提にしているため、開発環境では Mathlib4 が利用可能であることが前提（`import Mathlib.*` を解決できる必要がある）。このリポジトリに `lakefile.lean` 等がない場合は、ローカルで Mathlib を用意してからビルドすること。

- 典型的な編集例（参考）:
  - 「停止過程の適合性(adapted)」の補題を細分化して、まず `𝟙_{τ=k}` の可測性を示す補題を追加。
  - `minLayer` の分解補題: `{ω | minLayer ω ≤ n} = ⋃_{k≤n} {ω | minLayer ω = k}` を補題化して使い回す。

- 簡潔なチェックリスト（Pull Request 作成前）:
  - 小さい単位の変更か？（はい）
  - 既存の `toMathlib` / `filtrationOf` 補題を参照しているか？
  - 新しい補題に `example` を1つ追加して基本ケースを検証したか？
  - `sorry` を残す場合、コメントで後で Mathlib 補題に置き換える旨を明記したか？

もし特定のファイルや証明で補助が必要なら、対象ファイルパスと修正したい関数/補題名（例: `src/MyProjects/ST/Phase1_Simplified.lean::stoppedProcessℝBounded_eq_mathlib`）を教えてください。短い候補パッチを作り、テスト用の `example` を追加して検証します。

---
更新履歴: 初版（自動生成） — 参照元: `Implementation_Guide.md`, `README_Complete_Guide.md`, `Phase1_PRAGMATIC.lean`, 各 Lean ファイルの import パターン
