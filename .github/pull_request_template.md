# Summary
<!-- One-line summary in English (Subject is handled by the commit, this is the PR overview). -->

# Motivation / Context (日本語OK)
<!-- 背景・課題・選択理由・代替案など。 -->

# Changes
<!-- 何を変えたか（主要な定義・補題、ファイル、インターフェイス）。 -->

# Proof Strategy (Lean/mathlib)
<!-- 証明方針の要点。term-style/タクティック、多用時は補助補題に分離した旨など。 -->

# Risk & Rollback
<!-- 影響範囲、失敗時のロールバック手順を一言。 -->

# Breaking Change
<!-- 破壊的変更がある場合のみ記入（要事前承認＆下記チェック必須）。なければ N/A。 -->

# Migration Notes
<!-- 破壊的変更時の移行手順。なければ N/A。 -->

# Testing
<!-- 追加した example/小補題テスト、確認方法、再現手順（あれば）。 -->

# Docs
<!-- 追加/更新した module docstring、その他ドキュメント。 -->

# Toolchain
<!-- Lean/mathlib のバンプを含む場合は手順（lake update/build）と結果。なければ N/A。 -->

# Security & Licensing
<!-- 数学データのみ、外部アセットのライセンス記載、機微データなしの確認。 -->

---

## Checklist

- [ ] **Conventional Commits** を遵守（件名=英語・命令形・≤72 chars）
- [ ] **Scopes** は既定セットのいずれか（`algebra`/`analysis`/`topology`/`order`/`number_theory`/`data`/`tactic`/`measure`）
- [ ] **Breaking の可能性を確認**：
  - [ ] 破壊的変更なら **事前承認済み**（リンクを下に記載）
  - [ ] コミット件名は `type!:` を使用し、フッターに **`BREAKING CHANGE:`** を記載
  - [ ] **Rollback plan** を上の「Risk & Rollback」に一言で記載
- [ ] **Build**: `lake build` が成功
- [ ] **Tests**: 変更に関連する **`example` または小さな補題テスト**を少なくとも1つ追加
- [ ] **Docs**: 公開する `def/lemma` に対応して **module docstring** を更新
- [ ] **mathlib API**: 実装前に **Search / Read** で **最新の mathlib API を確認**（要点を「Motivation/Context」に記載）
- [ ] **`sorry` / `trivial`**:
  - [ ] 使用は**最終手段**・**最小限**
  - [ ] 含まれる場合、同一コミット内に **`TODO:`（理由とフォローアップ）** を記載
- [ ] **CI** がグリーン
- [ ] **Reviewer** を1名アサイン（`main` 直行は不可）
- [ ] **Release note**: 週次タグ用のリリース要点（Conventional Commitsから自動生成されるが、補足があれば本文に追記）

---

## Notes / Links
<!-- 承認スレッド、関連Issue/PR、参考資料など。 -->
