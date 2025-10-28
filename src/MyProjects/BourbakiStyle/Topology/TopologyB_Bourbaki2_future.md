# Topology B 将来の指針

本メモでは、節 B（被覆写像と経路持ち上げ）に関する中長期的な TODO と改善アイデアをまとめる。

## 1. 局所 → 大域の一意性証明
- continuous_unitInterval_to_discrete_const を活用して、liftPathLocalOn_unique を完成させる。
- フォールド構成で使う liftPathOnCover に一意性補題を実装し、build 系の補助関数を整理して API 化する。

## 2. 自然性と図式の整備
- Path.map との相性を明示する自然性補題を追加。
- 被覆写像の射に関して map を組み合わせた図式的性質を 	ikz-cd 数式レベルでも復元し、 Lean で証明可能な形に落とす。

## 3. ドキュメントと例
- liftPathLocal／liftPathOnCover の docstring を拡充し、円周など基本例を example として追加。
- 将来的に mathlib 本体に取り込む際の移植ガイドラインを文章化。

## 4. 構造のリファクタリング
- PathCover を発展させ、区間分割の monotonicity／Shape 情報を追加する検討。
- EvenlyCoveredAt の補助補題（@[simp] 適用候補など）を洗い出し、証明の重複を削減。

## 5. テストと CI
- lake test 相当のスモークテストを追加し、経路持ち上げ API のリグレッションを早期に検出。
- CI を想定したスクリプト化（lake build と簡易 example のコンパイルチェック）。

## 6. 学習リソースとの連携
- 学部向けノートとのリンクを README に追記し、理論的背景と Lean コードのギャップを縮める。
- 将来は動画解説やスライド資料への展開も検討。
