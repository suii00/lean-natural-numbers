# プロジェクト ロールバック手順書

## 📋 概要

**作成日**: 2025年8月6日  
**対象**: Mathlib移行後のプロジェクト状態  
**ベースライン**: `v1.0-pre-mathlib` (commit: 74e90e91beef9d5135f996f197a996b7725d1b52)

このドキュメントは、Mathlib統合で問題が発生した場合の完全復旧手順を提供します。

---

## 🚨 緊急ロールバック（簡易版）

問題が発生して即座に元の状態に戻したい場合：

```bash
# 1. Git branch切り替え（最も安全・高速）
git checkout pre-mathlib-baseline

# 2. または、git reset（現在のブランチをリセット）
git reset --hard v1.0-pre-mathlib

# 3. .lakeディレクトリクリーンアップ
rm -rf .lake

# 4. 確認
git status
lake --version
```

---

## 🔧 段階的ロールバック手順

### レベル1: Mathlib設定のみロールバック

**症状**: Mathlibのimportエラーが発生するが、基本プロジェクトは正常
**対処**: lakefile.leanをのみリセット

```bash
# 1. lakefile.leanの復元
git checkout v1.0-pre-mathlib -- lakefile.lean

# 2. lake manifestのリセット
git checkout v1.0-pre-mathlib -- lake-manifest.json

# 3. .lakeディレクトリクリーンアップ
rm -rf .lake

# 4. 基本プロジェクトビルド
lake build

# 5. 確認
lake env lean test_basic_imports.lean
```

### レベル2: 設定ファイル完全ロールバック

**症状**: 設定関連の問題でプロジェクト全体が動作不良
**対処**: 全設定ファイルを元の状態に復元

```bash
# 1. 設定ファイル群復元
git checkout v1.0-pre-mathlib -- lakefile.lean
git checkout v1.0-pre-mathlib -- lake-manifest.json  
git checkout v1.0-pre-mathlib -- lean-toolchain

# 2. バックアップから手動復元（必要に応じて）
cp lakefile.lean.backup lakefile.lean
cp lake-manifest.json.backup lake-manifest.json
cp lean-toolchain.backup lean-toolchain

# 3. 完全クリーンアップ
rm -rf .lake
lake clean

# 4. 基本環境再構築
lake build

# 5. 動作確認
lake env lean MyProject/NaturalNumbers.lean
```

### レベル3: プロジェクト完全ロールバック

**症状**: プロジェクト全体が破損、動作不能
**対処**: 完全に元の状態に復元

```bash
# 方法A: Git branch切り替え（推奨）
git checkout pre-mathlib-baseline
rm -rf .lake
lake build

# 方法B: Git reset（現在ブランチをリセット）
git reset --hard v1.0-pre-mathlib
rm -rf .lake  
lake build

# 方法C: バックアップディレクトリから復元
rm -rf ./*
cp -r ../project-backups/myproject_backup_*/\* ./
lake build
```

---

## 🗂️ バックアップからの完全復元

### アーカイブからの復元

```bash
# 1. 現在のプロジェクトを安全な場所に移動
mv myproject myproject_broken_$(date +%Y%m%d_%H%M%S)

# 2. バックアップアーカイブを展開
mkdir myproject
cd myproject
tar -xzf ../project-backups/myproject_archive_*.tar.gz

# 3. Git履歴復元（必要に応じて）
git init
git remote add origin <remote-url>
git fetch origin
git reset --hard origin/pre-mathlib-baseline

# 4. 環境再構築
lake build

# 5. 動作確認
./run_basic_tests.sh
```

### ディレクトリバックアップからの復元

```bash
# 1. 現在のディレクトリを退避
cd ..
mv myproject myproject_problematic_$(date +%Y%m%d_%H%M%S)

# 2. バックアップコピーを復元
cp -r project-backups/myproject_backup_*/ myproject
cd myproject

# 3. 環境再構築
rm -rf .lake
lake build

# 4. Git状態確認・修復
git status
git remote -v  # リモートURLが正しいか確認
```

---

## ✅ 復旧確認チェックリスト

### 基本機能確認
```bash
# 1. Lean基本動作
echo 'theorem test : True := trivial' > test_recovery.lean
lake env lean test_recovery.lean
rm test_recovery.lean

# 2. プロジェクトビルド
lake build

# 3. 実行ファイル生成
lake build myproject.exe
./myproject.exe

# 4. 既存証明ファイル
lake env lean MyProject/NaturalNumbers.lean
lake env lean test_basic_imports.lean
```

### 証明ファイル状況確認
```bash
# スタンドアロン版証明の動作確認
lake env lean sqrt2_verification_report.md  # ドキュメント確認
lake env lean square_even_standalone.lean   # 基本動作確認

# 期待結果: エラーなしでコンパイル完了
```

### システム機能確認
```bash
# 日報システム
powershell -File LeanDailyReportSimple.ps1

# エラーログシステム  
powershell -File ErrorLogger.ps1

# 期待結果: 正常実行、ログファイル生成
```

---

## 🔍 トラブルシューティング

### よくある問題と解決法

#### 問題1: `lake: command not found`
**原因**: Lean/Lake環境の破損  
**解決策**:
```bash
# elan（Leanツールチェーン管理）再インストール
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile
elan default leanprover/lean4:v4.3.0
```

#### 問題2: `git checkout` でファイルが復元されない
**原因**: ファイルがuntracked、またはgitignoreされている  
**解決策**:
```bash
# 強制的にファイル状態をクリーン
git clean -fd
git checkout pre-mathlib-baseline -- .

# またはreset使用
git reset --hard pre-mathlib-baseline
```

#### 問題3: バックアップファイルが見つからない
**原因**: バックアップ作成時の問題  
**解決策**:
```bash
# バックアップディレクトリ確認
ls -la ../project-backups/

# Git履歴から復元
git reflog  # 最近のcommit履歴確認
git checkout <commit-hash>

# タグから復元
git tag -l  # 利用可能タグ確認
git checkout v1.0-pre-mathlib
```

#### 問題4: 依存関係エラーが継続
**原因**: システムレベルの環境問題  
**解決策**:
```bash
# 完全環境リセット
rm -rf ~/.elan ~/.cache/mathlib
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# プロジェクト環境再構築
rm -rf .lake
lake clean
lake build
```

---

## 📊 復旧成功の指標

### 完全復旧確認項目

| 項目 | 確認コマンド | 期待結果 |
|------|-------------|----------|
| Lean基本動作 | `lake env lean --version` | `Lean (version 4.3.0...)` |
| プロジェクトビルド | `lake build` | `エラーなし` |
| 基本証明 | `lake env lean test_basic_imports.lean` | `True : Prop` |
| 自然数証明 | `lake env lean MyProject/NaturalNumbers.lean` | `エラーなし` |
| 日報システム | `powershell -File LeanDailyReportSimple.ps1` | `レポートファイル生成` |
| Git状態 | `git status` | `working tree clean` |

### 部分復旧で十分な場合

Mathlib関連機能のみ除外し、基本機能が動作すれば以下で十分：

- ✅ 基本Lean証明: 動作
- ✅ スタンドアロン証明: 動作  
- ✅ プロジェクトビルド: 成功
- ❌ Mathlibインポート: 無効化
- ❌ 高度戦術: 利用不可

---

## 🚀 復旧後の推奨事項

### 即座に実行すべきこと
1. **バックアップ状況確認**: 定期バックアップの設定
2. **変更箇所の特定**: 何が問題だったかの記録
3. **テスト実行**: 基本機能の包括的確認

### 段階的改善
1. **問題分析**: ロールバック原因の詳細調査
2. **代替アプローチ**: より安全なMathlib統合手法の検討
3. **予防策**: 同様問題の発生防止

---

## 📝 ロールバック実行記録テンプレート

ロールバック実行時は以下の情報を記録してください：

```
# ロールバック実行記録

## 基本情報
- 実行日時: [YYYY-MM-DD HH:MM:SS]
- 実行者: [Name]
- ロールバック理由: [詳細説明]
- 使用した復旧レベル: [1/2/3/アーカイブ復元]

## 問題状況
- 発生していたエラー: [具体的エラーメッセージ]
- 影響範囲: [ファイル、機能]
- 復旧前の最後のcommit: [hash]

## 実行した手順
1. [実際に実行したコマンド1]
2. [実際に実行したコマンド2]
...

## 復旧結果
- 成功/失敗: [STATUS]
- 確認したテスト項目: [チェックリスト結果]
- 残存問題: [あれば詳細]

## 教訓・改善点
- [今後の予防策]
- [システム改善案]
```

---

**緊急時連絡先**: この手順書で解決しない場合は、PROJECT_STATE_SNAPSHOT.mdの詳細情報も参照してください。