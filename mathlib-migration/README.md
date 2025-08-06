# Mathlib Gradual Migration System

**並行開発型Mathlib移行システム** - 現在のプロジェクトを維持しながら段階的にMathlibに移行

## 🎯 システム概要

このシステムは、以下のワークフローで安全な並行Mathlib移行を実現します：

1. **mathlib-migrationブランチで並行開発**
2. **少しずつ証明を移行・検証**  
3. **動作確認後に成功部分をmainにマージ**
4. **失敗時の自動復旧機能付き**

## 🏗️ システム構成

### コンポーネント

| ファイル | 機能 | 用途 |
|---------|------|------|
| `MigrationOrchestrator.ps1` | **メイン制御システム** | 全工程の統合管理 |
| `MigrationTracker.ps1` | **進捗管理システム** | 移行状況の追跡・記録 |
| `ProofMigrator.ps1` | **証明移行ツール** | 個別ファイルのMathlib変換 |
| `MigrationVerifier.ps1` | **検証システム** | 移行結果の自動検証 |
| `SelectiveMerger.ps1` | **選択的マージシステム** | 検証済みファイルのmain統合 |

### ワークフロー

```
現在のmainブランチ (保護)
    ↓ ブランチ作成
mathlib-migrationブランチ (開発)
    ↓ 段階的移行
個別ファイル移行・検証
    ↓ 成功時のみ
選択的マージ → mainブランチ
```

## 🚀 基本的な使用方法

### 1. システム開始

```powershell
# インタラクティブメニューで開始（推奨）
.\mathlib-migration\MigrationOrchestrator.ps1 -Action Menu

# 現在の状況確認
.\mathlib-migration\MigrationOrchestrator.ps1 -Action Status
```

### 2. 段階的移行実行

```powershell
# 次のファイルを自動選択して移行
.\mathlib-migration\MigrationOrchestrator.ps1 -Action Migrate -Strategy Progressive -Interactive

# 特定ファイルの移行（メニューから選択）
.\mathlib-migration\MigrationOrchestrator.ps1 -Action Menu
# → "3. Migrate Specific File" を選択
```

### 3. 移行結果の検証

```powershell
# 全移行ファイルの自動検証
.\mathlib-migration\MigrationOrchestrator.ps1 -Action Verify

# 個別ファイル検証
.\mathlib-migration\MigrationVerifier.ps1 -FileToVerify "migrated\MyProof.lean"
```

### 4. 成功部分のマージ

```powershell
# インタラクティブマージ（推奨）
.\mathlib-migration\MigrationOrchestrator.ps1 -Action Merge

# または直接実行
.\mathlib-migration\SelectiveMerger.ps1 -MergeMode Interactive
```

## 📊 移行戦略

### 1. Simple Strategy (シンプル)
- **対象**: インポートのないファイル優先
- **特徴**: 最もリスクの少ない順序
- **推奨**: 初回移行時

### 2. Progressive Strategy (段階的) - **推奨**
- **対象**: インポートの少ない順に移行
- **特徴**: 複雑さに応じた段階的アプローチ
- **推奨**: 通常の移行作業

### 3. Advanced Strategy (高度)
- **対象**: 部分移行済みファイル優先
- **特徴**: 効率重視、高度な機能活用
- **推奨**: システムに慣れた後

## 🔧 移行レベル

### Basic Level
- **変更内容**: 基本的なMathlibインポートのみ追加
- **安全性**: 最高（既存コードをほぼ変更しない）
- **適用例**: `import Mathlib.Tactic.Basic`

### Standard Level - **推奨**
- **変更内容**: インポート + 型のUnicode変換
- **安全性**: 高（型表記の統一）
- **適用例**: `Int → ℤ`, `Nat → ℕ`

### Advanced Level
- **変更内容**: 完全移行 + 戦術改善
- **安全性**: 中（高度な変更含む）
- **適用例**: `exact ⟨x⟩ → use x`, `sorry → by ring`

## 📈 実行例

### 成功例: 段階的移行ワークフロー

```powershell
PS> .\mathlib-migration\MigrationOrchestrator.ps1 -Action Menu

🔄 Mathlib Gradual Migration System 🔄
=====================================

Current Branch: mathlib-migration
Migration Progress: 45.2% complete
Files: 14/31 migrated

1. 📊 Show Migration Status
2. 🎯 Migrate Next File
3. 📁 Migrate Specific File
4. 🔍 Verify Migrated Files
5. 🔀 Merge Ready Files
6. 📈 Generate Progress Report

Choice: 2

🎯 MIGRATE NEXT FILE
===================
Next migration target:
  File: square_even_proof.lean
  Status: NotStarted
  Imports: 0

Proceed with migration? (y): y
Select migration level:
  1. Basic - Add basic Mathlib imports only
  2. Standard - Add imports and convert types
  3. Advanced - Full migration with tactics
Choice: 2

Migrating file with Standard level...
✅ Migration completed

🔍 Auto-verifying migrated file...
  Testing compilation... ✅ Compilation successful
  Testing import resolution... ✅ All imports resolved
  Testing theorem validity... ✅ 3/3 theorems valid
✅ File verified and ready for merge
```

### マージ実行例

```powershell
Choice: 5

🔀 MERGE READY FILES
===================
Identifying merge-ready files...

File Status Summary:
  Ready to Merge: 8
  Needs Review: 2
  Not Ready: 1

Interactive Merge Selection
===========================

Files ready to merge:
  1. square_even_proof.lean (Pass rate: 100.0%)
  2. basic_arithmetic.lean (Pass rate: 100.0%)
  3. simple_theorems.lean (Pass rate: 100.0%)
  [...]

Select files to merge (all): all

Preparing merge branch...
Creating merge branch: mathlib-merge-20250806_214530
✅ Merge branch prepared: mathlib-merge-20250806_214530

Executing selective merge...
✅ Successfully merged to main

✅ SELECTIVE MERGE COMPLETED SUCCESSFULLY
Merged 8 files to main branch
```

## 🛡️ 安全機能

### 1. 自動バックアップ
- 全操作前にセーフティブランチ自動作成
- マイルストーンブランチによる進捗保存
- 失敗時の自動ロールバック機能

### 2. 段階的検証
- **コンパイレーション**: 基本的な構文チェック
- **インポート解決**: 依存関係の検証
- **定理妥当性**: 証明の正当性確認
- **パフォーマンス**: 実行時間・メモリ使用量チェック

### 3. 選択的マージ
- 検証に合格したファイルのみマージ
- 問題のあるファイルは安全に隔離
- mainブランチの完全性保護

## 📂 生成されるファイル

### 追跡・管理ファイル
```
mathlib-migration/
├── migration_status.json          # 移行進捗データベース
├── migrated/                      # 移行済みファイル
│   ├── square_even_proof.lean
│   └── basic_arithmetic.lean
├── verification_*.json            # 検証結果レポート
└── merge_report_*.md              # マージ結果レポート
```

### ブランチ構造
```
main (保護されたブランチ)
├── mathlib-migration (開発ブランチ)
├── mathlib-merge-* (マージ用ブランチ)
├── safety-* (セーフティバックアップ)
└── milestone-* (進捗マイルストーン)
```

## 🔍 トラブルシューティング

### よくある問題

#### 1. "Branch not found" エラー
```powershell
# 解決策: ブランチを手動作成
git checkout -b mathlib-migration
```

#### 2. "Migration verification failed" エラー
```powershell
# 詳細確認
.\mathlib-migration\MigrationVerifier.ps1 -FileToVerify "path\to\file.lean" -Verbose

# 手動修正後に再検証
.\mathlib-migration\MigrationVerifier.ps1 -FileToVerify "fixed\file.lean"
```

#### 3. "Merge conflicts" エラー
```powershell
# 競合解決後に再実行
git status
git add <resolved-files>
git commit -m "Resolve merge conflicts"
```

### 状況確認コマンド

```powershell
# 現在の移行状況
.\mathlib-migration\MigrationOrchestrator.ps1 -Action Status

# 詳細進捗レポート
.\mathlib-migration\MigrationTracker.ps1 -UpdateStatus -GenerateReport

# ブランチ状況
git branch -a
git status
```

## 🎯 推奨ワークフロー

### 日常的な移行作業

1. **朝の作業開始**
   ```powershell
   git checkout mathlib-migration
   .\mathlib-migration\MigrationOrchestrator.ps1 -Action Status
   ```

2. **1-3個のファイル移行**
   ```powershell
   .\mathlib-migration\MigrationOrchestrator.ps1 -Action Menu
   # → 2-3回繰り返し
   ```

3. **移行結果の検証**
   ```powershell
   .\mathlib-migration\MigrationOrchestrator.ps1 -Action Verify
   ```

4. **成功分のマージ（週1回）**
   ```powershell
   .\mathlib-migration\MigrationOrchestrator.ps1 -Action Merge
   ```

### 週次まとめ作業

```powershell
# 進捗レポート生成
.\mathlib-migration\MigrationOrchestrator.ps1 -Action Status
.\mathlib-migration\MigrationTracker.ps1 -GenerateReport

# 古いブランチのクリーンアップ
git branch -d mathlib-merge-*  # マージ完了済みブランチ
```

## 📋 システム要件

### 必須環境
- **PowerShell 5.1以上**
- **Git 2.20以上**
- **Lean 4.3.0以上**
- **Lake (最新版)**

### 推奨環境
- **メモリ**: 8GB以上
- **ディスク**: 2GB以上の空き容量
- **GitHub CLI** (プルリクエスト作成用)

## 🔗 関連システム

このMathlib移行システムは、以下のシステムと連携できます：

- **Auto Recovery System** (`mathlib-recovery/`) - エラー時の自動復旧
- **Import Learning System** (`import-learning/`) - インポート最適化

## 🎉 期待される効果

### 安全性向上
- ✅ mainブランチの完全保護
- ✅ 段階的移行によるリスク最小化
- ✅ 自動バックアップとロールバック

### 開発効率向上
- ✅ 並行開発による継続的作業
- ✅ 自動検証による品質保証
- ✅ 選択的マージによる柔軟な統合

### プロジェクト管理改善
- ✅ 詳細な進捗追跡
- ✅ 包括的レポート生成
- ✅ 学習データの蓄積

---

## 🎯 まとめ

**Mathlib Gradual Migration System**により：

- 🔄 **並行開発**: mainブランチを保護しながら安全に移行作業
- 📊 **進捗管理**: 詳細な追跡システムで全体の進行状況を把握
- 🔍 **品質保証**: 自動検証により高品質な移行を実現
- 🔀 **柔軟統合**: 成功した部分のみを選択的にマージ

**安全で効率的なMathlib移行を実現しましょう！**