# Session 7 TODO メモ

## 優先度高
- [ ] **S7_CH の等式再定式化**: `f 6 / f 4 = f 3 / f 2` を積の等式 `algebraMap ℤ R 6 * algebraMap ℤ R 2 = algebraMap ℤ R 3 * algebraMap ℤ R 4` に置き換える。
  - `IsLocalization.eq_mk'_iff_mul_eq` を適用する。
  - 交差乗算を `Submonoid.closure {2,5}` で証明し、`IsLocalization.mk'` と整合させる。
- [ ] **分数表現の補助補題整備**: `IsLocalization.mk'` と `algebraMap` の積表現を相互に行き来する補題を自作する。
  - 例: `mk'_eq_iff_eq` の逆方向を利用し、`mk'` 表現を積の等式に還元する小Lemmaを追加。

## 優先度中
- [ ] **モノイド生成集合の再検討**: $S=\{1,2,4,\dots\}$ のまま扱うか、課題文との整合を保ちつつ $3,5$ が現れる操作に対応できるよう補題を追加する。
  - `Submonoid.powers` の利用を試みる。
  - あるいは $S$ を $\{2^n \mid n \ge 0\}$ に固定したまま `IsLocalization.map_units` で単元性を補う。
- [ ] **ドキュメント整備**: `S7_CH_difficulty.md` を基に、今後の方針と学習項目を整理したノートを継続更新する。

## 優先度低
- [ ] **Field 局所化の練習**: `Localization` が体になるケース (`ℚ` など) で同種の等式を証明し、除算が使える状況との差分を理解する。
- [ ] **自動化の検討**: `simp` / `ring_nf` による平方根計算の効率化や、`norm_num` を活用した整数計算のテンプレート化を進める。

---
更新日: 2025-09-21 / 作成者: CODEX (OpenAI)
