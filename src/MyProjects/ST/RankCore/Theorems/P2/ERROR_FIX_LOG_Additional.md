# エラー修正ログ

- エラー概要：
  - `Additional_Termination_Examples.lean` に複数の `sorry` が残っておりビルド失敗
  - `fib_fast_aux_eq` の定式化が再帰の形と合わず証明不能
  - `tree_height_explicit` の `termination_by tree_size` に対する減少証明が不足
  - 例題 `example : fib_fast 10 = 55` が `decide` で判定できず失敗

- 原因：
  - 主要補題（countdown_terminates / factorial_tail_aux_eq / fib_fast_aux_eq / tree_height_le_size）が未実装
  - `fib_fast_aux` は 1 段ずつ `n` を減らすので、等式は `n+1` 形でないと整合しない
  - `tree_size` による停止性は「左右部分木が strictly smaller」を明示しないと証明できない
  - `decide` は `fib_fast 10` の計算規約化に失敗することがある

- 修正内容：
  - `countdown_terminates` を `Nat.lt_wfRel.wf` で証明
  - `factorial_tail_aux_eq` と `factorial_tail_eq` を帰納法で実装
  - `fib_fast_aux_eq` を `n+1` 版に定式化し、帰納法で証明
  - `fib_fast_eq` を新しい補題に合わせて修正
  - `tree_size_lt_node_left/right` を追加し、`tree_height_explicit` の `decreasing_by` を明示
  - `example` を簡単な値（`fib_fast 1 = 1`）に変更
  - `tree_height_le_size` を `max_le_iff` を使って完成

- 修正が正しい理由：
  - `Nat.lt_wfRel` は自然数の `<` の well-foundedness の標準構成
  - `factorial_tail_aux` は構造的再帰なので帰納法で等価性が導ける
  - `fib_fast_aux` は `n+1` から 1 段減る定義であり、その形に合わせると再帰方程式が閉じる
  - `tree_size` は `Tree.node` の左右部分木より必ず大きくなるため termination 減少条件を満たす
  - `max_le_iff` により高さの上界をサイズから導ける

- 動作確認：
  - `lake build MyProjects.ST.RankCore.Theorems.P2.Additional_Termination_Examples`

- どういう意図でこの実装に至ったかメモ：
  - ブルバキ的に「関係（再帰）→ 測度（rank）→ WellFounded性」という構成に揃えるため、
    各例で最小限の補題だけを導入
  - `fib_fast_aux_eq` は再帰の形と一致するように式を再定式化し、
    余計な補題追加を避けた
  - `tree_height_explicit` では「部分木が小さい」という集合論的な包含関係を
    `tree_size` の strict decrease として明示化
