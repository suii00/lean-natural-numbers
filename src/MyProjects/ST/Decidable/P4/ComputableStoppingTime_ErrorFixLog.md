### エラー修正ログ（ComputableStoppingTime）

- エラー概要：`coinHeadTail.time` の `if b then 0 else 1` で条件が `Prop` を要求され，`b : Bool` がそのまま使えず型エラー（Application type mismatch）が発生していた。
- 原因：`if` は条件に `Prop` を取るため，`Bool` を直接書くと推論に失敗するケースがあり，`ite` の推定先が合わなかった。
- 修正内容：`if` をブールのパターンマッチに置き換え，`time := fun b => match b with | true => 0 | false => 1` と定義し直した。
- 修正が正しい理由：`match` で `Bool` の 2 ケースを明示することで，条件が `Prop` になる誤推論を防ぎつつ同じ計算結果を保証するため。
- 動作確認：`lake env lean src/MyProjects/ST/Decidable/P4/ComputableStoppingTime.lean` を実行し，型エラーが消えたことを確認（警告のみ）。
- どういう意図でこの実装に至ったかメモ：最小の変更でエラーを解消し，停止時間の定義をそのまま活かすためにパターンマッチを選択。`simp` による adapted 証明は従来のまま利用できる。  
