### エラー修正ログ
- エラー概要：`closed_finite_union` の Finset 版実装が未整理でビルド失敗。`evenOddAlgebra` の `closed_union` が自己参照により証明不能。
- 原因：`Finset.insert` 相当の書き方が Lean 4 の `insert` インスタンスと噛み合っておらず、また `evenOddAlgebra` の `simp` が定義自身を展開して循環していた。
- 修正内容：Finset 帰納法で `closed_finset_union` を再実装し、Fintype 版定理をそこから導出する二段構えに統一。`evenOddAlgebra` では 4 ケースを明示的に列挙し、循環しない形で `simp` だけで処理。
- 修正が正しい理由：各ステップで `ℱ.closed_union` を用いた帰納が型チェックを通り、`lake build MyProjects.ST.Decidable.P2.DecidableAlgebra` が完走しているため。
- 動作確認：プロジェクトルートで `lake build MyProjects.ST.Decidable.P2.DecidableAlgebra` を実行し成功を確認。
- どういう意図でこの実装に至ったかメモ：Hom/HomLe を見据えて射の閉性を finset → fintype へ分離し、教育用に証明構造を分かりやすくした。`evenOddAlgebra` も例示の簡潔さを優先し、4 事象の個別列挙に揃えた。
