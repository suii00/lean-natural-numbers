# Mathlib使用前後のコード自動比較システム

Mathlib移行前後のLeanコードを包括的に分析・比較する統合システム

## 🎯 システム概要

このシステムは、Mathlib移行によるコードへの影響を4つの主要観点から分析します：

- **証明の複雑さ比較** - 証明の長さ、戦術の洗練度、論理的深度の変化を測定
- **戦術使用の変化** - 利用可能な戦術と使用パターンの比較
- **パフォーマンス比較** - コンパイル時間、メモリ使用量、実行速度の変化
- **学習コストの評価** - Mathlib移行に必要な教育投資の評価

## 🏗️ システム構成

### コンポーネント一覧

```
mathlib-comparison/
├── ComprehensiveComparator.ps1    # 統合比較システム（メイン）
├── ProofComplexityAnalyzer.ps1    # 証明複雑度分析器
├── TacticComparator.ps1           # 戦術使用比較器
├── PerformanceBenchmarker.ps1     # パフォーマンス測定器
├── LearningCostEvaluator.ps1      # 学習コスト評価器
└── README.md                      # このドキュメント
```

### 1. 証明複雑度分析器 (`ProofComplexityAnalyzer.ps1`)

**機能**: 証明の複雑さを5つの指標で定量化し、Mathlib移行前後を比較

**分析指標**:
- 証明の長さ (30% 重み)
- 戦術の複雑さ (25% 重み) 
- 論理的深度 (20% 重み)
- 定理依存関係 (15% 重み)
- 構文複雑さ (10% 重み)

**使用例**:
```powershell
.\ProofComplexityAnalyzer.ps1 -OriginalFile "original.lean" -MathlibFile "migrated.lean"
```

### 2. 戦術使用比較器 (`TacticComparator.ps1`)

**機能**: 使用戦術の変化を分析し、新しく利用可能になった戦術を評価

**分析内容**:
- 追加・削除された戦術の特定
- 戦術カテゴリ別使用量の変化
- 新しい自動化戦術の恩恵評価
- 戦術の複雑度とlearning costの算出

**使用例**:
```powershell
.\TacticComparator.ps1 -OriginalFile "original.lean" -MathlibFile "migrated.lean" -IncludeExamples
```

### 3. パフォーマンス測定器 (`PerformanceBenchmarker.ps1`)

**機能**: コンパイル性能への影響を定量的に測定

**測定項目**:
- コンパイル時間の変化
- インポート解決時間
- 型チェック時間
- メモリ使用量（オプション）

**使用例**:
```powershell
.\PerformanceBenchmarker.ps1 -OriginalFile "original.lean" -MathlibFile "migrated.lean" -BenchmarkRuns 5 -IncludeMemoryProfiling
```

### 4. 学習コスト評価器 (`LearningCostEvaluator.ps1`)

**機能**: Mathlib移行に必要な学習時間と教育投資を評価

**評価内容**:
- ユーザーレベル別学習時間の算出
- 新しい概念とトピック領域の特定
- 前提知識要件の分析
- 段階的学習パスの提案

**使用例**:
```powershell
.\LearningCostEvaluator.ps1 -OriginalFile "original.lean" -MathlibFile "migrated.lean" -UserLevel Beginner -IncludeTrainingPlan
```

### 5. 統合比較システム (`ComprehensiveComparator.ps1`) - **メインツール**

**機能**: 全てのコンポーネントを統合した包括的分析

**出力内容**:
- エグゼクティブサマリー
- 移行推奨度の評価
- ROI（投資対効果）の評価  
- 優先度付きアクション提案
- ビジネスケースの構築

## 🚀 クイックスタート

### 基本的な使用方法

1. **包括的比較の実行**:
```powershell
.\ComprehensiveComparator.ps1 -OriginalFile "original.lean" -MathlibFile "migrated.lean" -SaveReport
```

2. **初心者向け詳細分析**:
```powershell
.\ComprehensiveComparator.ps1 -OriginalFile "proof.lean" -MathlibFile "proof_mathlib.lean" -UserLevel Beginner -IncludePerformance -IncludeTrainingPlan
```

3. **サマリーレポート**:
```powershell
.\ComprehensiveComparator.ps1 -OriginalFile "theorem.lean" -MathlibFile "theorem_mathlib.lean" -OutputFormat Summary
```

### 出力例

```
Mathlib Migration Analysis Summary
=================================

Recommendation: Recommended
Overall Impact: Positive 
ROI: High

Key Numbers:
- Complexity: -8.5 points
- New Tactics: 7
- Learning: 15.5 hours
- Performance: -12.3%

Priority Actions:
- Focus on algebraic automation tactics - significant productivity gains available
- Invest in 'simp' tactic training - high-value skill for Mathlib usage
```

## 📊 分析レポート

### 生成されるレポート

1. **包括的分析レポート** (`comprehensive_analysis_*.txt`)
   - 全コンポーネントの詳細分析結果
   - エグゼクティブサマリー
   - 優先度付き推奨事項

2. **JSON データ** (`comprehensive_analysis_*.json`)
   - プログラマティックアクセス用の構造化データ
   - 追加分析やダッシュボード構築に使用可能

3. **個別コンポーネントレポート**
   - 各分析器の専門的な詳細レポート

### レポート解釈ガイド

**移行推奨度**:
- `Recommended`: 移行による恩恵が明確
- `Conditional`: 条件付きで移行を検討
- `Not Recommended`: 移行コストが恩恵を上回る

**ROI評価**:
- `High`: 学習投資に対する生産性向上が大きい
- `Moderate`: バランスの取れた投資対効果
- `Low`: 投資に見合う恩恵が少ない

## 🎛️ 高度な使用方法

### カスタム設定

各コンポーネントは個別に設定可能な複雑度重み付けと評価基準を持ちます:

```powershell
# 証明複雑度の重み付けをカスタマイズ
$complexityConfig.ComplexityMetrics["ProofLength"].Weight = 0.4
$complexityConfig.ComplexityMetrics["TacticComplexity"].Weight = 0.3
```

### バッチ処理

複数ファイルの一括比較:

```powershell
Get-ChildItem -Path "originals\" -Filter "*.lean" | ForEach-Object {
    $original = $_.FullName
    $mathlib = $_.FullName -replace "originals", "mathlib"
    if (Test-Path $mathlib) {
        .\ComprehensiveComparator.ps1 -OriginalFile $original -MathlibFile $mathlib -OutputFormat Summary
    }
}
```

## 📈 実用的応用例

### 1. チーム研修計画の策定

```powershell
# チーム全体の学習計画を策定
.\LearningCostEvaluator.ps1 -OriginalFile "team_project.lean" -MathlibFile "team_project_mathlib.lean" -UserLevel Intermediate -IncludeTrainingPlan
```

### 2. 移行戦略の最適化

```powershell
# 段階的移行のためのファイル優先順位決定
Get-ChildItem "*.lean" | ForEach-Object {
    .\ProofComplexityAnalyzer.ps1 -OriginalFile $_.FullName -MathlibFile "$($_.BaseName)_mathlib.lean" -OutputFormat JSON
} | Sort-Object ComplexityIncrease
```

### 3. パフォーマンス影響の評価

```powershell
# 大規模プロジェクトでのパフォーマンス影響測定
.\PerformanceBenchmarker.ps1 -OriginalFile "large_proof.lean" -MathlibFile "large_proof_mathlib.lean" -BenchmarkRuns 10 -IncludeMemoryProfiling
```

## 🔧 要件

### システム要件

- **PowerShell 5.1+** または **PowerShell Core 7.0+**
- **Lean 4** (4.3.0以降推奨)
- **Lake** (Leanビルドシステム)

### オプション要件

- **Git** (バージョン管理機能用)
- **Mathlib 4** (比較対象Mathlibプロジェクト)

### 推奨環境

- **Visual Studio Code** + Lean 4 Extension
- **メモリ**: 8GB以上（大規模プロジェクトの場合）
- **ストレージ**: 2GB以上の空き容量（Mathlibキャッシュ用）

## 🤝 統合システムとの連携

このシステムは既存のMathlib移行システムと完全に統合されています:

### 移行オーケストレーションとの連携

```powershell
# 移行後の自動評価
.\mathlib-migration\MigrationOrchestrator.ps1 -Action Migrate -Strategy Progressive
.\mathlib-comparison\ComprehensiveComparator.ps1 -OriginalFile "original.lean" -MathlibFile "migrated\file_mathlib.lean" -SaveReport
```

### 回復システムとの連携

移行失敗時の判断材料として比較分析を活用:

```powershell
# 移行結果が期待を下回る場合の分析
if ($migrationResult.Success -eq $false) {
    .\ComprehensiveComparator.ps1 -OriginalFile $originalFile -MathlibFile $failedFile -OutputFormat Summary
}
```

## 📋 トラブルシューティング

### よくある問題

1. **パフォーマンス測定の失敗**
   - Lakeビルドが正常に動作することを確認
   - `lake exe cache get`でMathlibキャッシュを取得

2. **戦術認識の問題**
   - 戦術データベースは定期的に更新が必要
   - カスタム戦術は手動で追加設定

3. **メモリ不足エラー**
   - 大規模ファイルの場合はベンチマーク回数を削減
   - `-BenchmarkRuns 1`オプションを使用

### サポート

問題が発生した場合は、以下の情報と共にレポートしてください:

1. PowerShellのバージョン
2. Lean 4のバージョン  
3. 分析対象ファイルのサイズと複雑さ
4. エラーメッセージの全文

## 🎉 まとめ

この比較システムにより、Mathlib移行の影響を：

- **定量的に測定** - 客観的データに基づく意思決定
- **包括的に分析** - 複雑さ、性能、学習コスト、戦術変化を総合評価
- **戦略的に計画** - ROI評価と優先度付きアクション提案
- **継続的に改善** - 移行結果のフィードバックによる最適化

**安全で効率的なMathlib移行の成功を保証します！** 🚀