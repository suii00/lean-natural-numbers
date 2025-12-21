# エラー修正ログ

- エラー概要：
  - `Nat.mod_lt` の前提型不一致（`b ≠ 0` をそのまま渡していた）
  - `WellFounded.mono` の暗黙引数 `r` が解決できない
  - `gcd` の減少証明で `b % a < b` としており、実際の再帰引数 `a % b` と不一致
  - `gcd_rel` が「現状態→次状態」の向きで定義されており、`WellFounded` の関係（`next < current`）と整合しない

- 原因：
  - `Nat.mod_lt` は `0 < b` を要求するため、`b ≠ 0` を `Nat.pos_of_ne_zero` で変換する必要があった
  - `WellFounded.mono` は `r` と `r'` を明示しないと型推論が失敗した
  - `gcd` の termination 証明の対象が誤っていた（`a % b` が実際の再帰引数）
  - `gcd_rel` の向きが `InvImage (· < ·) gcd_rank` と逆向きだった

- 修正内容：
  - `gcd_rank_decreases` で `Nat.mod_lt a (Nat.pos_of_ne_zero hb)` に修正
  - `gcd_rel` を「次状態 → 現状態」の関係として定義し直し
  - `gcd_rel_rank_lt` 補題を追加し、関係が rank を下げることを明示
  - `gcd_terminates` を `InvImage.wf` と `WellFounded.mono` で構成し、`r`/`r'` を明示
  - `gcd` の減少証明を `a % b < b` に修正
  - 例題 `example : gcd_rel (gcd_step (48, 18)) (48, 18)` を追加

- 修正が正しい理由：
  - `Nat.mod_lt` の前提は `0 < b` なので `b ≠ 0` からの変換が正しい
  - `gcd_rel` を「next, current」にすると `gcd_rank` が厳密減少する関係に一致し、`InvImage (· < ·) gcd_rank` の部分関係として扱える
  - `WellFounded.mono` で部分関係の well-foundedness を得る構成は標準的
  - `gcd` の再帰引数は `a % b` であり、減少証明もそれに一致させる必要がある

- 動作確認：
  - `lake build MyProjects.ST.RankCore.Theorems.P2.GCD_Termination`

- どういう意図でこの実装に至ったかメモ：
  - Bourbaki 的に「関係の向き」と「測度（rank）」を明示し、`InvImage` による well-foundedness を基礎から構成できる形に整理
  - 証明の最小限性を重視し、`gcd_rel` の定義と `rank` の減少のみで停止性を導く構成に統一
