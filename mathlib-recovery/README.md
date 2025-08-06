# Mathlib Migration Auto Recovery System

**自動復旧システム** - Mathlib移行中のエラーに対する包括的な自動復旧システム

## 🎯 システム概要

このシステムは、Mathlib移行中に発生するエラーを自動的に検出し、以下の機能を提供します：

1. **エラー検出時の自動ロールバック** - 前の安全な状態に即座に復元
2. **問題部分の特定と分離** - エラーの原因となるコンポーネントを自動分離
3. **段階的再試行機能** - インテリジェントな復旧戦略で段階的に修復を試行
4. **ブランチ管理システム** - 全ての操作を個別のブランチで管理し、安全性を確保

## 🏗️ システム構成

### コアモジュール

| モジュール | ファイル | 機能 |
|-----------|---------|------|
| **自動復旧システム** | `AutoRecoverySystem.ps1` | エラー検出・ロールバック・修正提案 |
| **問題分離フレームワーク** | `ProblemIsolation.ps1` | 問題のあるファイル・モジュールの特定と分離 |
| **段階的再試行システム** | `StagedRetrySystem.ps1` | プログレッシブな復旧戦略の実行 |
| **ブランチマネージャー** | `BranchManager.ps1` | セーフティブランチの作成と管理 |
| **復旧オーケストレーター** | `RecoveryOrchestrator.ps1` | 全システムの統合制御 |

### システムアーキテクチャ

```
RecoveryOrchestrator (Master Controller)
    ├── AutoRecoverySystem (Error Detection & Rollback)
    ├── ProblemIsolation (Component Isolation)
    ├── StagedRetrySystem (Progressive Recovery)
    └── BranchManager (Branch Safety & Management)
```

## 🚀 使用方法

### 基本的な使用

```powershell
# 基本的な自動復旧実行
.\RecoveryOrchestrator.ps1 -Operation "build" -RecoveryStrategy "Smart" -AutoMode

# 特定のエラーログを解析して復旧
.\RecoveryOrchestrator.ps1 -Operation "build" -ErrorLog "build_error.log" -RecoveryStrategy "Conservative"

# ドライランモード（実際の変更は行わない）
.\RecoveryOrchestrator.ps1 -Operation "update" -RecoveryStrategy "Smart" -DryRun -Verbose
```

### 復旧戦略の選択

#### 1. Conservative (保守的)
- **特徴**: 最も安全なアプローチ
- **適用場面**: 重要な本番環境、初回復旧試行
- **動作**: 最小限の変更、手動確認要求、低リスク

```powershell
.\RecoveryOrchestrator.ps1 -RecoveryStrategy "Conservative" -Operation "build"
```

#### 2. Smart (インテリジェント) - **推奨**
- **特徴**: バランス型アプローチ
- **適用場面**: 通常の開発環境、一般的な使用
- **動作**: 自動判断、適応的復旧、中程度のリスク

```powershell
.\RecoveryOrchestrator.ps1 -RecoveryStrategy "Smart" -Operation "build"
```

#### 3. Aggressive (積極的)
- **特徴**: 高速復旧、高リスク許容
- **適用場面**: 開発・テスト環境、緊急時復旧
- **動作**: 大胆な変更、自動実行、高リスク

```powershell
.\RecoveryOrchestrator.ps1 -RecoveryStrategy "Aggressive" -Operation "build"
```

## 🔧 復旧プロセスの詳細

### フェーズ1: エラー検出 (Detection)
```powershell
# 自動エラー検出
$errors = Detect-MathlibError "build" $errorOutput

# 検出されるエラータイプ:
# - BuildFailure: ビルドエラー
# - ImportError: インポートエラー  
# - DependencyError: 依存関係エラー
# - SyntaxError: 構文エラー
```

### フェーズ2: セーフティバックアップ (Safety Backup)
```powershell
# 安全なバックアップブランチの作成
$safetyBranch = Create-SafetyBranch "pre_recovery" "Full backup before recovery"
$milestoneBranch = Create-MilestoneBranch "recovery_start" "Stable state"
```

### フェーズ3: 問題評価 (Assessment)
```powershell
# リスク評価と復旧プラン作成
$recoveryPlan = @{
    NeedsRollback = $true
    IsolationMode = "Smart"
    RetryStrategy = "Progressive"
    MaxRetries = 3
}
```

### フェーズ4: 問題分離 (Isolation)
```powershell
# 問題のあるコンポーネントの分離
$isolationResults = Start-ProblemIsolation -IsolationMode "Smart"

# 分離戦略:
# - FileLevel: 個別ファイルの分離
# - ModuleLevel: モジュール全体の分離
# - ImportLevel: インポート文の分離
```

### フェーズ5: 復旧実行 (Recovery)
```powershell
# ロールバック実行（必要に応じて）
$rollbackResult = Rollback-ToSafeState "High severity errors" 1

# 段階的再試行
$retryResult = Start-StagedRetry -RetryStrategy "Progressive"

# 再試行ステージ:
# - Minimal: 最小限の操作
# - Basic: 基本操作
# - Standard: 標準操作
# - Full: 完全操作
# - Complete: 包括的操作
```

### フェーズ6: 検証 (Validation)
```powershell
# 復旧結果の検証
$validationResult = Execute-PostValidation @(
    "Check basic compilation"
    "Verify output files"
    "Full compilation test"
    "Import validation"
)
```

### フェーズ7: 統合 (Consolidation)
```powershell
# 成功した復旧のマージ
$mergeResult = Merge-RecoveryBranch $recoveryBranch -MergeStrategy "safe"

# ドキュメント生成
$reportPath = Generate-RecoveryDocumentation $session
```

## 📊 実行例

### 成功例: ビルドエラーの自動復旧

```powershell
PS> .\RecoveryOrchestrator.ps1 -Operation "build" -RecoveryStrategy "Smart" -AutoMode

🚨 RECOVERY ORCHESTRATION INITIATED
Operation: build | Strategy: Smart
============================================================
✅ Recovery session initialized: a1b2c3d4
✅ Session branch created: safety_orchestration_session_a1b2c3d4_20250806_213045

🔍 [Detection] Starting error detection phase...
⚠️ [Detection] Detected 3 errors (Severity: High)

🛡️ [SafetyBackup] Creating safety backups...
✅ [SafetyBackup] Safety backups created successfully

📋 [Assessment] Assessing recovery requirements...
✅ [Assessment] Recovery plan created: Rollback -> Isolation -> Retry -> Validation
ℹ️ [Assessment] Risk level: Medium | Estimated duration: 45 minutes

🔬 [Isolation] Starting problem isolation...
✅ [Isolation] Successfully isolated 2 components

🔄 [Recovery] Starting recovery operations...
⚠️ [Recovery] Executing rollback...
✅ [Recovery] Rollback completed successfully
ℹ️ [Recovery] Starting staged retry process...
ℹ️ [Recovery] Recovery attempt 1 of 3
🎉 [Recovery] Recovery attempt 1 succeeded!

🔬 [Validation] Validating recovery results...
✅ [Validation] Validation successful: 4/4 health checks passed

📋 [Consolidation] Consolidating recovery session...
✅ [Consolidation] Session consolidated - Duration: 12.3 minutes
ℹ️ [Consolidation] Documentation: mathlib-recovery\recovery_session_a1b2c3d4.md

✅ RECOVERY ORCHESTRATION COMPLETED SUCCESSFULLY
✅ All systems recovered and validated
============================================================
Session ID: a1b2c3d4 | Status: Success
Duration: 12.3 minutes
```

### 失敗例: 手動介入が必要なケース

```powershell
PS> .\RecoveryOrchestrator.ps1 -Operation "update" -RecoveryStrategy "Conservative"

🚨 RECOVERY ORCHESTRATION INITIATED
Operation: update | Strategy: Conservative
============================================================

🔍 [Detection] Starting error detection phase...
⚠️ [Detection] Detected 8 errors (Severity: High)

🛡️ [SafetyBackup] Creating safety backups...
✅ [SafetyBackup] Safety backups created successfully

📋 [Assessment] Assessing recovery requirements...
✅ [Assessment] Recovery plan created: Rollback -> Isolation -> Retry -> Validation
ℹ️ [Assessment] Risk level: High | Estimated duration: 90 minutes

🔬 [Isolation] Starting problem isolation...
✅ [Isolation] Successfully isolated 5 components

🔄 [Recovery] Starting recovery operations...
⚠️ [Recovery] Executing rollback...
✅ [Recovery] Rollback completed successfully
ℹ️ [Recovery] Recovery attempt 1 of 2
❌ [Recovery] Recovery attempt 1 failed
ℹ️ [Recovery] Recovery attempt 2 of 2
❌ [Recovery] Recovery attempt 2 failed
❌ [Recovery] Recovery phase failed: All recovery attempts exhausted

🔬 [Validation] Validating recovery results...
❌ [Validation] Validation failed: 1/4 health checks passed

🚨 RECOVERY ORCHESTRATION FAILED
⚠️ Manual intervention may be required
============================================================
Session ID: x7y8z9w0 | Status: Failed
Duration: 45.7 minutes
```

## 📂 生成されるファイルとブランチ

### ブランチ構造

```
main (元のブランチ)
├── safety_pre_recovery_20250806_213045 (セーフティバックアップ)
├── milestone_recovery_start_20250806_213100 (マイルストーン)
├── isolation_Smart_components_20250806_213200 (分離ブランチ)  
├── recovery_build_attempt1_20250806_213300 (復旧試行1)
├── recovery_build_attempt2_20250806_213400 (復旧試行2)
└── milestone_recovery_complete_a1b2c3d4_20250806_214500 (完了マイルストーン)
```

### 生成ファイル

```
mathlib-recovery/
├── recovery_log.json (復旧履歴データベース)
├── isolation_report.md (分離レポート)
├── recovery_session_a1b2c3d4.md (セッション詳細レポート)
├── isolated_files/ (分離されたファイル)
│   ├── 20250806_213245_problematic_file.lean
│   └── 20250806_213246_another_file.lean
└── temp_validation_*.lean (一時検証ファイル)
```

## ⚙️ 設定とカスタマイズ

### 復旧設定の調整

```powershell
# 最大再試行回数の変更
.\RecoveryOrchestrator.ps1 -MaxRecoveryAttempts 5

# タイムアウト設定の調整
$retryConfig.BaseDelaySeconds = 60  # デフォルト: 30秒
$retryConfig.MaxDelaySeconds = 600  # デフォルト: 300秒
```

### エラー検出パターンのカスタマイズ

```powershell
# AutoRecoverySystem.ps1 内のエラーパターンを編集
$errorPatterns["CustomError"] = @{
    Patterns = @("custom error pattern", "another pattern")
    Severity = "Medium"
    RecoveryStrategy = "Isolate"
}
```

### ブランチ管理設定

```powershell
# BranchManager.ps1 内の設定を調整
$branchConfig.BranchTypes["custom"] = @{
    Prefix = "custom"
    Description = "Custom branch type"
    Retention = 10  # days
    AutoCleanup = $true
}
```

## 🔍 トラブルシューティング

### よくある問題と解決策

#### 1. "Not a git repository" エラー
```powershell
# 解決策: Git リポジトリを初期化
git init
git add .
git commit -m "Initial commit"
```

#### 2. "Failed to create safety branch" エラー
```powershell
# 解決策: 作業ツリーをクリーンにする
git add .
git commit -m "WIP: preparing for recovery"
```

#### 3. "Recovery attempts exhausted" エラー
```powershell
# 解決策: より保守的な戦略を使用
.\RecoveryOrchestrator.ps1 -RecoveryStrategy "Conservative" -MaxRecoveryAttempts 1

# または手動でロールバック
git reset --hard HEAD~1
```

#### 4. "Branch merge conflicts" エラー
```powershell
# 解決策: 手動でコンフリクトを解決
git status
git add <resolved-files>
git commit -m "Resolve merge conflicts"
```

### ログファイルの確認

```powershell
# 復旧ログの確認
Get-Content mathlib-recovery\recovery_log.json | ConvertFrom-Json | Format-Table

# セッション詳細レポートの確認
Get-Content mathlib-recovery\recovery_session_*.md

# 分離レポートの確認
Get-Content mathlib-recovery\isolation_report.md
```

## 🎯 推奨ワークフロー

### 1. 日常的な使用
```powershell
# 通常のビルド作業
lake build

# エラーが発生した場合
.\RecoveryOrchestrator.ps1 -Operation "build" -RecoveryStrategy "Smart" -AutoMode
```

### 2. 重要な変更前
```powershell
# 事前にマイルストーンを作成
.\BranchManager.ps1 -Function "Create-MilestoneBranch" -MilestoneName "before_major_change"

# 変更作業
# ... 作業実行 ...

# 問題が発生した場合の復旧
.\RecoveryOrchestrator.ps1 -RecoveryStrategy "Conservative"
```

### 3. 定期メンテナンス
```powershell
# 古いブランチのクリーンアップ
.\BranchManager.ps1 -CleanupOldBranches

# ブランチ状況の確認
.\BranchManager.ps1 -Function "Get-BranchSummary" -Verbose
```

## 📈 パフォーマンス最適化

### 復旧時間の短縮

1. **キャッシュの利用**
   ```powershell
   # 事前にキャッシュをダウンロード
   lake exe cache get
   ```

2. **並列処理の活用**
   ```powershell
   # Aggressive戦略で高速復旧
   .\RecoveryOrchestrator.ps1 -RecoveryStrategy "Aggressive"
   ```

3. **分離範囲の最適化**
   ```powershell
   # より細かい分離設定
   .\ProblemIsolation.ps1 -IsolationMode "Conservative"
   ```

## 🛡️ セキュリティ考慮事項

### 1. バックアップブランチの保護
- セーフティブランチは自動削除されません
- 重要なマイルストーンは明示的に保護されます

### 2. ロールバック操作の安全性
- すべてのロールバック前に自動バックアップが作成されます
- 複数の復元ポイントが利用可能です

### 3. 分離ファイルの管理
- 分離されたファイルは専用ディレクトリに保存されます
- 元の位置情報が保持され、復元が可能です

## 📋 システム要件

### 必須要件
- **PowerShell 5.1以上** (Windows PowerShell または PowerShell Core)
- **Git 2.20以上** (ブランチ管理機能)
- **Lake** (Leanプロジェクト管理)
- **Lean 4** (証明システム)

### 推奨環境
- **メモリ**: 8GB以上
- **ディスク容量**: 2GB以上の空き容量
- **ネットワーク**: Mathlib キャッシュダウンロード用

## 🔗 関連リソース

- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Lake Package Manager](https://github.com/leanprover/lake)

---

## 🎉 まとめ

この自動復旧システムにより、Mathlib移行中のエラーに対して：

✅ **自動的なエラー検出とロールバック**
✅ **インテリジェントな問題分離**  
✅ **段階的な復旧戦略**
✅ **完全なブランチ管理**
✅ **包括的なドキュメント生成**

が実現され、安全で効率的なMathlib移行作業が可能になります。

**推奨使用方法**: まず `Smart` 戦略で試行し、必要に応じて `Conservative` または `Aggressive` 戦略を選択してください。