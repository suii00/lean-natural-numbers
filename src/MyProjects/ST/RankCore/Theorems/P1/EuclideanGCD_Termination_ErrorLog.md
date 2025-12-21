# EuclideanGCD_Termination 修正ログ

## エラー概要
- `sorry` が残っていたためビルドが失敗
- `simp` による自動簡約が不安定で `No goals to be solved` / ループ警告が発生
- `gcd_with_proof_eq_gcd` の証明が未完成

## 原因
- `RankCore` 内に「常に rank が減少する」フィールドを置いたため、GCD の「b=0」ケースで矛盾
- `gcd_step_wellfounded` / `Acc` 例が `sorry` のまま
- `gcd_with_proof_eq_gcd` の再帰式が `gcd` の再帰と一致する形で整理されていなかった

## 修正内容
- `gcd_step_wellfounded` を `InvImage.wf` で証明
- `Acc` 例を `WellFounded.apply` で完成
- `RankCore` から「常に減少」を外し、`RankCore.rank_decreases` を補助命題として別定義
- `gcdRankCore` の定義を簡約（条件付き減少補題は別に保持）
- `gcd_with_proof_eq_gcd` を強帰納法で証明し、
  `Nat.gcd_rec` と `Nat.gcd_comm` で再帰の整合を確保
- `simp` ループを避けるため、`nth_rewrite` + `simp [hb]` を採用

## 修正が正しい理由
- `InvImage.wf` は `Nat.lt` の WellFounded を 2 成分の射影へ持ち上げる標準手法
- `gcd_rank_decreases_when_nonzero` は `Nat.mod_lt` により `b ≠ 0` のとき確実に成立
- `gcd_with_proof` の再帰式は `Nat.gcd` の定義と一致し、
  `Nat.gcd_rec` により `gcd a b = gcd (a % b) b` を利用して証明可能

## 動作確認
- `lake build MyProjects.ST.RankCore.Theorems.P1.EuclideanGCD_Termination` ✅
- `#eval gcd_with_proof 48 18 = 6` などの計算例が通る

## どういう意図でこの実装に至ったかメモ
- Bourbaki 的に「必要最小限の構造」へ戻す方針で、
  RankCore から全称的な「減少」仮定を外し、条件付き補題に分離
- 証明の再利用性を高めるため、`InvImage.wf` と `Nat.gcd_rec` に統一
- 教育用途の文脈（Goal-Driven）を保つため、過度な抽象化や魔術的 tactic は避けた
