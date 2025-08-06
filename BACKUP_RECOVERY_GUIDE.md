# プロジェクト バックアップ・復旧 完全ガイド

## 📋 概要

**作成日**: 2025年8月6日  
**対象プロジェクト**: myproject (Lean 4 + Mathlib)  
**バックアップ基準点**: v1.0-pre-mathlib  
**テスト状況**: ✅ 全機能検証済み

このガイドは、プロジェクトの完全バックアップ・復旧システムの使用方法を説明します。

---

## 🎯 作成されたバックアップ

### 1. Git バージョン管理
```
Branch: pre-mathlib-baseline  
Tag: v1.0-pre-mathlib  
Commit: 74e90e91beef9d5135f996f197a996b7725d1b52
```

### 2. ファイルシステム バックアップ
```
ディレクトリコピー: ../project-backups/myproject_backup_20250806_201827/
圧縮アーカイブ: ../project-backups/myproject_archive_20250806_201914.tar.gz
```

### 3. 設定ファイル個別バックアップ
```
lakefile.lean.backup
lake-manifest.json.backup  
lean-toolchain.backup
```

---

## 🚀 復旧シナリオ別手順

### シナリオ1: 軽微な問題（Mathlib設定のみリセット）
**使用例**: importエラーが発生するが基本機能は正常

```bash
# Step 1: Mathlib設定をリセット
git checkout v1.0-pre-mathlib -- lakefile.lean lake-manifest.json

# Step 2: キャッシュクリア
rm -rf .lake

# Step 3: 基本ビルド
lake build

# Step 4: 確認
lake env lean test_basic_imports.lean
```

### シナリオ2: 中程度の問題（プロジェクト設定リセット）
**使用例**: 設定ファイルが破損、ビルドエラーが多発

```bash
# Step 1: 全設定ファイルリセット
git checkout v1.0-pre-mathlib -- lakefile.lean lake-manifest.json lean-toolchain

# Step 2: 完全クリーンアップ
rm -rf .lake
lake clean

# Step 3: 環境再構築  
lake build

# Step 4: 基本機能確認
bash test_backup_recovery.sh
```

### シナリオ3: 重大な問題（完全ロールバック）
**使用例**: プロジェクト全体が動作不能

```bash
# 方法A: ブランチ切り替え（推奨）
git checkout pre-mathlib-baseline
rm -rf .lake
lake build

# 方法B: ハードリセット
git reset --hard v1.0-pre-mathlib
rm -rf .lake
lake build

# 確認
bash test_backup_recovery.sh
```

### シナリオ4: 災害復旧（アーカイブから完全復元）
**使用例**: Git履歴も含めて全て破損

```bash
# Step 1: 現在のディレクトリ退避
cd ..
mv myproject myproject_damaged_$(date +%Y%m%d_%H%M%S)

# Step 2: アーカイブから復元
mkdir myproject
cd myproject  
tar -xzf ../project-backups/myproject_archive_*.tar.gz

# Step 3: Git履歴復元
git init
git remote add origin <your-remote-url>
git add .
git commit -m "Restore from archive backup"

# Step 4: 環境構築
lake build

# Step 5: 動作確認
bash test_backup_recovery.sh
```

---

## 🔍 復旧後の検証手順

### 自動検証スクリプト実行
```bash
bash test_backup_recovery.sh
```
**期待結果**: 全テストが✅PASSEDと表示される

### 手動検証項目

#### 1. 基本Lean機能
```bash
echo 'theorem test : True := trivial' > manual_test.lean
lake env lean manual_test.lean  # エラーなしで完了すること
rm manual_test.lean
```

#### 2. プロジェクト構造
```bash
lake build                      # エラーなしで完了
./myproject.exe                 # "Hello, Lean 4 Project!"と表示
```

#### 3. 証明ファイル
```bash
lake env lean MyProject/NaturalNumbers.lean    # コンパイル成功
lake env lean test_basic_imports.lean          # "True : Prop"と表示
```

#### 4. 補助システム
```bash
powershell -File LeanDailyReportSimple.ps1     # レポート生成
powershell -File ErrorLogger.ps1               # ログ作成
```

---

## 📊 復旧確認チェックリスト

| 項目 | 確認方法 | 期待結果 | 状態 |
|------|----------|----------|------|
| Git状態 | `git status` | `working tree clean` | [ ] |
| Leanバージョン | `lake env lean --version` | `Lean (version 4.3.0...)` | [ ] |
| プロジェクトビルド | `lake build` | エラーなし | [ ] |
| 基本証明 | `lake env lean test_basic_imports.lean` | `True : Prop` | [ ] |
| 自然数証明 | `lake env lean MyProject/NaturalNumbers.lean` | エラーなし | [ ] |
| 実行ファイル | `./myproject.exe` | `Hello, Lean 4 Project!` | [ ] |
| 日報システム | `powershell -File LeanDailyReportSimple.ps1` | ファイル生成 | [ ] |
| バックアップ整合性 | `bash test_backup_recovery.sh` | 全テストPASS | [ ] |

---

## 🚨 トラブルシューティング

### よくある問題と解決策

#### Q1: `git checkout pre-mathlib-baseline`でエラー
**エラー**: `error: pathspec 'pre-mathlib-baseline' did not match any file(s)`  
**解決**: 
```bash
git branch -a                    # ブランチ一覧確認
git fetch origin                 # リモートから取得
git checkout -b pre-mathlib-baseline v1.0-pre-mathlib  # タグからブランチ作成
```

#### Q2: `lake build`が失敗する
**エラー**: 各種ビルドエラー  
**解決**:
```bash
rm -rf .lake                     # キャッシュ完全削除
lake clean                       # プロジェクトクリーン
elan default leanprover/lean4:v4.3.0  # Lean バージョン確認
lake build                       # 再ビルド
```

#### Q3: バックアップアーカイブが見つからない
**エラー**: `No such file or directory`  
**解決**:
```bash
ls ../project-backups/           # バックアップ確認
find .. -name "myproject_archive_*.tar.gz"  # アーカイブ検索

# 見つからない場合はGitから復元
git checkout v1.0-pre-mathlib
```

#### Q4: 全機能が復旧しない
**症状**: 一部機能が動作しない  
**解決**:
```bash
# 段階的復旧確認
git log --oneline -5             # 最近のcommit確認  
git diff HEAD v1.0-pre-mathlib   # 差分確認
git checkout v1.0-pre-mathlib -- <specific-file>  # 個別ファイル復元
```

---

## 📈 バックアップ戦略の最適化

### 定期バックアップ設定（推奨）
```bash
# 週次バックアップスクリプト例
#!/bin/bash
DATE=$(date +%Y%m%d_%H%M%S)
git tag "backup-$DATE" -m "Automatic weekly backup"
tar -czf "../project-backups/auto_backup_$DATE.tar.gz" --exclude='.lake' --exclude='.git' .
echo "Backup created: backup-$DATE"
```

### 重要な変更前のスナップショット
```bash
# 大きな変更前に実行
git tag "pre-major-change-$(date +%Y%m%d)" -m "Snapshot before major changes"
git push origin --tags
```

---

## 📝 復旧実行ログテンプレート

復旧実行時は記録を残してください：

```
# 復旧実行ログ

## 基本情報
- 実行日時: [YYYY-MM-DD HH:MM:SS]
- 復旧シナリオ: [1/2/3/4]
- 復旧理由: [具体的問題の説明]

## 実行手順
1. [実際に実行したコマンド]
2. [実際に実行したコマンド]
...

## 検証結果
- 自動検証: [bash test_backup_recovery.sh の結果]
- 手動検証: [チェックリスト確認結果]
- 残存問題: [あれば詳細]

## 教訓
- [今後の改善点]
- [予防策]
```

---

## 🎯 成功指標

### 完全復旧成功の定義
- ✅ 全自動テストがPASS
- ✅ 基本Lean機能の動作確認
- ✅ プロジェクトビルドの成功  
- ✅ 既存証明ファイルのコンパイル成功
- ✅ 補助スクリプトの正常動作

### 部分復旧成功の定義（最小要件）
- ✅ 基本Lean環境の動作
- ✅ スタンドアロン証明ファイルのコンパイル
- ✅ プロジェクトの基本ビルド成功
- ⚠️ Mathlib機能は無効（許容範囲）

---

## 📞 サポート情報

### 参考ドキュメント
- `PROJECT_STATE_SNAPSHOT.md`: 詳細な現在状態記録
- `ROLLBACK_PROCEDURES.md`: 包括的ロールバック手順  
- `mathlib_import_system_overview.md`: システム全体概要

### 自己診断ツール
- `test_backup_recovery.sh`: 自動復旧テスト
- `mathlib-testing/scripts/SimpleImportTest.ps1`: 基本機能確認

**復旧に関する全ての情報はこのガイドに集約されています。**