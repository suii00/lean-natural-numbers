# S13 実装時の主なエラーまとめ

- `padicValRat` まわりの等式生成が未整理のまま `simp` に依存した結果、`padicValRat 5 (5 ^ k) = ↑k` が示せず、`simp` の再帰深度超過警告が発生。
- `padicNorm_from_val` を使う際に指数の符号を取り違え、`padicNorm 5 (1 / 5)` などで `5 ^ (- -1)` といった形が残って型不一致エラーとなった。
- `padicValRat.mul` の適用後に積の順序を書き換えなかったため、`padicValRat 5 (5 * 3)` などで止まり、最終目標 `padicValRat 5 15` と一致せず型不一致になった。
- 強三角不等式の証明では `max (padicNorm 5 15) (padicNorm 5 10)` を具体値へ落とし切れず、`max` と `∨` が残存して不等式を証明できなかった。
- エラー整理後に `git checkout` でファイル復元を試みたが、Git 管理外だったため `pathspec` エラーが発生し、最終的に手動でテンプレートに戻す対応となった。
