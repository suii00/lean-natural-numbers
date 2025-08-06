# Mathlib Import段階的テストシステム

## 🎯 概要

このシステムは、Mathlibのimportを段階的に追加し、各段階でのコンパイルエラーを自動記録・解決するためのツールセットです。

## 📁 システム構造

```
mathlib-testing/
├── scripts/                     # 実行スクリプト
│   ├── MathLibImportTester.ps1  # 段階的importテスト
│   ├── ErrorAnalyzer.ps1        # エラー解析・自動修復
│   └── RunMathLibTests.ps1      # 統合実行スクリプト
├── tests/                       # 生成されるテストファイル
│   ├── Level0_Basic.lean
│   ├── Level1_Tactic_Basic.lean
│   └── ...
├── logs/                        # ログとレポート
│   ├── import_test_*.json       # テスト結果JSON
│   ├── import_report_*.md       # テストレポート
│   └── error_analysis_*.md      # エラー解析レポート
└── database/                    # 成功パターン・解決策DB
    ├── success_patterns.json   # 成功したimportパターン
    └── error_solutions.json    # エラー解決パターン
```

## 🚀 使用方法

### 基本実行
```powershell
# 統合テスト実行（推奨）
.\mathlib-testing\scripts\RunMathLibTests.ps1

# 詳細ログ付き実行
.\mathlib-testing\scripts\RunMathLibTests.ps1 -Verbose

# 自動修復付き実行
.\mathlib-testing\scripts\RunMathLibTests.ps1 -AutoFix -Verbose
```

### 個別スクリプト実行

#### 1. 段階的Importテスト
```powershell
.\mathlib-testing\scripts\MathLibImportTester.ps1 [-Verbose]
```

#### 2. エラー解析
```powershell
.\mathlib-testing\scripts\ErrorAnalyzer.ps1 -ErrorLogFile "logs\import_test_*.json" [-AutoFix]
```

## 📊 テストレベル

### Level 0: 基本
- **Import**: なし
- **テスト**: 基本的なLean構文
- **目的**: 環境の基本動作確認

### Level 1: 基本戦術
- **Import**: `Mathlib.Tactic.Basic`
- **テスト**: `trivial`, `rfl`戦術
- **目的**: 最小限のMathlib戦術確認

### Level 2: 拡張戦術
- **Import**: `Mathlib.Tactic.Basic`, `Mathlib.Tactic.Ring`
- **テスト**: `ring`戦術
- **目的**: 代数的計算戦術の確認

### Level 3: 自然数基本
- **Import**: `Mathlib.Tactic.Basic`, `Mathlib.Data.Nat.Basic`
- **テスト**: 自然数の基本定理
- **目的**: 数値データ型の基本機能確認

### Level 4: 自然数拡張
- **Import**: 上記 + `Mathlib.Data.Nat.Parity`
- **テスト**: 偶数・奇数判定
- **目的**: 数論の基本機能確認

### Level 5: フル戦術
- **Import**: `Mathlib.Tactic`
- **テスト**: `omega`, `norm_num`, `use`戦術
- **目的**: 完全なMathlib戦術セット確認

## 🔍 エラータイプと解決策

### MissingDependency
**症状**: `object file ... does not exist`
**解決策**: 
- `lake exe cache get` でキャッシュ取得
- `lake build` で依存関係ビルド

### TacticNotAvailable  
**症状**: `unknown tactic`
**解決策**:
- 適切なimportを追加
- Mathlib.Tacticの完全ビルド

### IdentifierNotFound
**症状**: `unknown identifier` 
**解決策**:
- 必要なimportを追加
- 名前空間を確認

### SyntaxError
**症状**: `unexpected token`
**解決策**:
- Lean 4構文の確認
- 型注釈の追加

## 📈 成功パターンデータベース

システムは成功したimportパターンを自動記録し、以下の情報を保存します：

- **成功したImport組み合わせ**
- **実行時間**
- **テスト日時**
- **環境情報**

## 🛠️ 自動修復機能

以下のエラーに対して自動修復を提供：

1. **依存関係不足** → `lake exe cache get`自動実行
2. **ビルドファイル不足** → `lake build`自動実行

## 📋 出力ファイル

### JSONログ
```json
{
  "TestSession": {
    "Timestamp": "2025-08-06_14-30-00",
    "TotalTests": 6,
    "SuccessCount": 4,
    "SuccessRate": 0.67
  },
  "Results": [...]
}
```

### Markdownレポート
- テストレベル別結果
- エラー詳細と解決策
- 推奨事項
- 成功パターン分析

## 🎯 実用例

### 新しいLeanプロジェクトでの確認
```powershell
# 基本確認
.\mathlib-testing\scripts\RunMathLibTests.ps1

# 問題があれば自動修復
.\mathlib-testing\scripts\RunMathLibTests.ps1 -AutoFix
```

### 既存プロジェクトのMathlib対応確認
```powershell
# 詳細ログで段階的確認
.\mathlib-testing\scripts\RunMathLibTests.ps1 -Verbose

# 特定レベルまでの動作を確認してから本格運用
```

## 🔧 カスタマイズ

### テストレベルの追加
`MathLibImportTester.ps1`の`$testLevels`配列に新しいレベルを追加：

```powershell
@{
    Name = "Level6_Custom"
    Description = "カスタムテスト"
    Imports = @("Your.Custom.Import")
    TestCode = @"
-- カスタムテストコード
import Your.Custom.Import
theorem custom_test : CustomProp := by custom_tactic
"@
}
```

### エラーパターンの追加
`ErrorAnalyzer.ps1`の`$errorPatterns`に新しいパターンを追加。

## 📞 サポート

問題が発生した場合：
1. 生成されたレポートファイルを確認
2. `-Verbose`オプションで詳細ログを確認
3. `database/`ディレクトリの成功パターンを参照

---

*Mathlib Import段階的テストシステム - 効率的なMathlib導入をサポート*