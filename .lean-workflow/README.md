# Lean証明プロジェクト完全Gitワークフローシステム

## 📋 概要

このシステムは、Lean4を使用した数学的証明プロジェクト用の包括的なワークフロー管理システムです。証明の完成、エラー修正、進捗管理、品質保証を自動化し、研究効率を大幅に向上させます。

### 🎯 主要機能

- **🔄 自動コミット**: 証明完成時の自動Git操作
- **🐛 エラー追跡**: 詳細なエラー分析・修正履歴・パターン学習
- **📊 進捗レポート**: 日次・週次・月次の自動レポート生成
- **🚀 GitHub統合**: 自動プッシュ・バックアップ・同期
- **🏷️ 難易度タグ**: AI駆動の証明複雑性分析・分類
- **⚙️ 統合管理**: ワンストップでの全システム制御

---

## 🚀 クイックスタート

### 1. システム初期化
```powershell
# ワークフローシステムをセットアップ
.\.lean-workflow\scripts\workflow-manager.ps1 -Action init

# インタラクティブ設定（推奨）
.\.lean-workflow\scripts\workflow-manager.ps1 -Action init -Interactive
```

### 2. システム状況確認
```powershell
# 全体的なシステム状況を確認
.\.lean-workflow\scripts\workflow-manager.ps1 -Action status
```

### 3. 設定検証
```powershell
# 設定に問題がないか確認
.\.lean-workflow\scripts\workflow-manager.ps1 -Action validate
```

---

## 📚 詳細使用方法

### 🔄 証明完成時の自動コミット

```powershell
# 証明ファイル完成時
.\.lean-workflow\core\lean-proof-workflow.ps1 -Action auto-commit -ProofFile "square_even.lean"

# カスタムメッセージ付き
.\.lean-workflow\core\lean-proof-workflow.ps1 -Action auto-commit -ProofFile "sqrt2_indep.lean" -Message "Complete √2 independence proof with advanced tactics"
```

### 🐛 エラー修正の記録

```powershell
# エラー修正を記録
.\.lean-workflow\error-tracking\error-fix-recorder.ps1 -Action record -ProofFile "theorem.lean" -ErrorType "syntax" -ErrorMessage "missing 'by'" -Solution "Added 'by' keyword" -Category "syntax" -TimeSpent "15"

# エラーパターン分析
.\.lean-workflow\error-tracking\error-fix-recorder.ps1 -Action analyze -Days 7

# リカバリ推奨取得
.\.lean-workflow\error-tracking\error-fix-recorder.ps1 -Action recovery -ErrorMessage "type mismatch" -ErrorType "type"
```

### 📊 進捗レポート生成

```powershell
# 日次レポート生成
.\.lean-workflow\reporting\progress-reporter.ps1 -ReportType daily

# 週次レポート生成
.\.lean-workflow\reporting\progress-reporter.ps1 -ReportType weekly

# 月次レポート生成  
.\.lean-workflow\reporting\progress-reporter.ps1 -ReportType monthly

# 自動コミット付きレポート生成
.\.lean-workflow\reporting\progress-reporter.ps1 -ReportType daily -AutoCommit
```

### 🚀 GitHub自動プッシュ

```powershell
# GitHubプッシュシステム初期化
.\.lean-workflow\github\auto-push-manager.ps1 -Action setup

# リモートリポジトリ設定
.\.lean-workflow\github\auto-push-manager.ps1 -Action configure-remote -RemoteName origin

# プッシュ実行（タグ付き）
.\.lean-workflow\github\auto-push-manager.ps1 -Action push -IncludeTags

# ドライラン実行
.\.lean-workflow\github\auto-push-manager.ps1 -Action push -DryRun

# Git同期
.\.lean-workflow\github\auto-push-manager.ps1 -Action sync
```

### 🏷️ 証明難易度タグ付け

```powershell
# 証明ファイルを分析
.\.lean-workflow\tagging\difficulty-tagger.ps1 -Action analyze -ProofFile "fermat_last.lean"

# 自動難易度判定でタグ付け
.\.lean-workflow\tagging\difficulty-tagger.ps1 -Action tag -ProofFile "group_theory.lean" -Difficulty auto

# 手動でタグ付け
.\.lean-workflow\tagging\difficulty-tagger.ps1 -Action tag -ProofFile "topology_basic.lean" -Difficulty advanced -Category topology -Description "基本的な位相幾何学の証明"

# バッチタグ付け
.\.lean-workflow\tagging\difficulty-tagger.ps1 -Action batch-tag -BatchPath "MyProject/NumberTheory/"

# 難易度レポート生成
.\.lean-workflow\tagging\difficulty-tagger.ps1 -Action report
```

---

## 📁 システム構成

```
.lean-workflow/
├── 📁 core/                    # コア機能
│   └── lean-proof-workflow.ps1 # メイン証明ワークフロー
├── 📁 automation/              # 自動化機能  
│   └── auto-commit-hooks.ps1   # 自動コミットフック
├── 📁 error-tracking/          # エラー追跡
│   └── error-fix-recorder.ps1  # エラー記録・分析
├── 📁 reporting/               # レポート生成
│   └── progress-reporter.ps1   # 進捗レポート生成
├── 📁 github/                  # GitHub統合
│   └── auto-push-manager.ps1   # 自動プッシュ管理
├── 📁 tagging/                 # タグ管理
│   └── difficulty-tagger.ps1   # 難易度タグ付け
├── 📁 config/                  # 設定ファイル
│   ├── master-config.json      # マスタ設定
│   ├── workflow-config.json    # ワークフロー設定
│   ├── github-config.json      # GitHub設定
│   └── error-config.json       # エラー追跡設定
├── 📁 scripts/                 # 管理スクリプト
│   └── workflow-manager.ps1    # 統合管理システム
├── 📁 logs/                    # ログファイル
├── 📁 reports/                 # 生成レポート
├── 📁 metadata/               # メタデータ
└── 📄 README.md               # このファイル
```

---

## ⚙️ 設定システム

### 📄 マスタ設定ファイル (master-config.json)

システム全体の動作を制御する中央設定ファイル：

```json
{
  "git": {
    "autoCommit": {
      "enabled": true,
      "verifyProofFirst": true,
      "includeDifficultyTag": true
    },
    "autoPush": {
      "enabled": false,
      "strategy": "on-success",
      "includeTags": true
    }
  },
  "errorTracking": {
    "enabled": true,
    "patternLearning": true,
    "recoveryRecommendations": true
  },
  "difficulty": {
    "autoClassification": true,
    "useAdvancedAnalysis": true
  }
}
```

### 🔧 インタラクティブ設定

```powershell
# 対話型設定ウィザード
.\.lean-workflow\scripts\workflow-manager.ps1 -Action configure -Interactive
```

---

## 🎯 使用シナリオ例

### シナリオ1: 新しい証明を完成させる

1. **証明ファイル作成**: `new_theorem.lean` を作成・編集
2. **自動コミット実行**: 
   ```powershell
   .\.lean-workflow\core\lean-proof-workflow.ps1 -Action auto-commit -ProofFile "new_theorem.lean"
   ```
3. **自動で実行される処理**:
   - 証明検証 (lake check)
   - 難易度分析・タグ作成
   - Git コミット（メタデータ付き）
   - 統計データ更新

### シナリオ2: エラー修正プロセス

1. **エラー発生**: 証明中にtype errorが発生
2. **エラー記録**: 
   ```powershell
   .\.lean-workflow\error-tracking\error-fix-recorder.ps1 -Action record -ProofFile "problem.lean" -ErrorType "type" -ErrorMessage "expected Nat, got Int"
   ```
3. **パターンマッチング**:
   ```powershell
   .\.lean-workflow\error-tracking\error-fix-recorder.ps1 -Action pattern-match -ErrorMessage "expected Nat, got Int"
   ```
4. **修正・検証・記録**完了

### シナリオ3: 定期レポート生成

```powershell
# 毎日実行（cron/Task Scheduler）
.\.lean-workflow\reporting\progress-reporter.ps1 -ReportType daily -AutoCommit

# 毎週実行
.\.lean-workflow\reporting\progress-reporter.ps1 -ReportType weekly -AutoCommit
```

### シナリオ4: プロジェクト全体の難易度分析

```powershell
# 全ファイルを一括分析・タグ付け
.\.lean-workflow\tagging\difficulty-tagger.ps1 -Action batch-tag

# 分析レポート生成
.\.lean-workflow\tagging\difficulty-tagger.ps1 -Action report
```

---

## 📊 生成されるレポート例

### 日次進捗レポート
- Git活動統計（コミット数、変更ファイル数）
- 証明統計（完成率、難易度分布）
- エラー分析（発生頻度、解決時間）
- 推奨事項（次のアクション提案）

### エラー分析レポート
- エラーカテゴリ別分布
- 頻出エラーパターンTOP5
- 平均解決時間
- 改善推奨事項

### 難易度タグレポート
- 証明ファイル難易度分布
- 複雑性統計（平均スコア、最高・最低）
- カテゴリ別分析
- 学習パス推奨

---

## 🔒 セキュリティ機能

### ファイル検証
- 悪意のあるコードパターンの検出
- ファイルサイズ制限
- 許可された拡張子のみ処理

### Git安全性
- コミット署名オプション
- 保護ブランチ設定
- 強制プッシュ禁止

### データ保護
- 秘密情報の自動検出・除外
- ログローテーション
- 設定ファイル暗号化（将来実装）

---

## 🚨 トラブルシューティング

### よくある問題と解決策

#### 1. "lake check" が失敗する
```powershell
# Leanプロジェクトの依存関係を更新
lake update
lake build
```

#### 2. Git操作でエラーが発生する
```powershell
# Git状態を確認
git status
git log --oneline -5

# 必要に応じてリセット
git reset --hard HEAD
```

#### 3. 設定ファイルが破損した
```powershell
# 設定をリセットして再初期化
.\.lean-workflow\scripts\workflow-manager.ps1 -Action reset -Force
.\.lean-workflow\scripts\workflow-manager.ps1 -Action init
```

#### 4. パフォーマンスが低下している
```powershell
# システムベンチマークを実行
.\.lean-workflow\scripts\workflow-manager.ps1 -Action benchmark
```

### ログファイルの確認

```powershell
# 本日のワークフローログを確認
Get-Content .\.lean-workflow\logs\workflow-$(Get-Date -Format 'yyyy-MM-dd').log -Tail 20

# エラー追跡ログを確認
Get-Content .\.lean-workflow\logs\error-tracker-$(Get-Date -Format 'yyyy-MM-dd').log -Tail 20
```

---

## 📈 拡張機能・カスタマイズ

### カスタムスクリプトの追加

1. **スクリプト配置**: `.lean-workflow/scripts/custom/` に配置
2. **設定登録**: `master-config.json` の `advanced.customization` セクションで設定
3. **フック設定**: 特定のイベント時に自動実行

### 通知システムの拡張

```json
{
  "notifications": {
    "channels": {
      "slack": {
        "enabled": true,
        "webhook": "YOUR_SLACK_WEBHOOK_URL"
      },
      "email": {
        "enabled": true,
        "smtp": {
          "server": "smtp.gmail.com",
          "port": 587
        }
      }
    }
  }
}
```

### AI分析機能の追加（将来実装）

- 証明パターンの自動認識
- 最適化提案の自動生成
- 類似定理の検索・推奨

---

## 🤝 貢献・サポート

### 貢献方法

1. **Issue報告**: バグや改善要望を報告
2. **Pull Request**: 新機能や修正の提案
3. **ドキュメント改善**: 使用方法やFAQの充実
4. **テスト**: 様々な環境での動作確認

### サポートチャンネル

- **GitHub Issues**: バグ報告・機能要望
- **ドキュメント**: 詳細な使用方法
- **コミュニティ**: ベストプラクティスの共有

---

## 📝 更新履歴

### v1.0.0 (2025-08-06)
- ✨ 初回リリース
- 🔄 自動コミット機能実装
- 🐛 エラー追跡システム実装
- 📊 進捗レポート生成実装
- 🚀 GitHub自動プッシュ実装
- 🏷️ 難易度タグ付けシステム実装
- ⚙️ 統合管理システム実装

### 今後の予定
- 🤖 AI駆動証明最適化
- ☁️ クラウド同期機能
- 👥 チーム協業機能
- 📱 モバイル通知対応

---

## 📄 ライセンス

MIT License - 自由に使用・改変・再配布可能

---

## 🙏 謝辞

このシステムは以下のオープンソースプロジェクトに基づいています：
- **Lean 4**: Microsoft Research による定理証明支援システム
- **Mathlib**: Lean 4用数学ライブラリ
- **PowerShell**: クロスプラットフォーム自動化フレームワーク
- **Git**: 分散バージョン管理システム

---

**🎯 Lean証明プロジェクトの効率化と品質向上を支援します！**