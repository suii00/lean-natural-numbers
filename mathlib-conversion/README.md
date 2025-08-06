# Mathlib自動変換システム

## 📋 概要

このシステムは、既存のLean証明コードを自動的にMathlib対応形式に変換します。

## 🛠️ 変換システム構成

### 1. SimpleMathLibConverter.ps1
**用途**: 基本的な単一ファイル変換
**機能**: 
- Import文の自動追加
- 型名の変換 (Int → ℤ, Nat → ℕ)
- 定理名の変換 (Nat.add_zero → add_zero)
- 戦術の変換

```powershell
# 基本使用法
.\SimpleMathLibConverter.ps1 -InputFile "file.lean"

# プレビューモード
.\SimpleMathLibConverter.ps1 -InputFile "file.lean" -DryRun -Verbose

# カスタム出力
.\SimpleMathLibConverter.ps1 -InputFile "file.lean" -OutputFile "converted.lean"
```

### 2. BatchMathLibConverter.ps1
**用途**: プロジェクト全体の一括変換
**機能**: 
- 複数ファイルの自動検出
- 証明ファイルの分析・分類
- 一括変換処理
- 詳細レポート生成

```powershell
# プロジェクト全体変換
.\BatchMathLibConverter.ps1 -ProjectPath "." -OutputDir "converted"

# プレビューモード
.\BatchMathLibConverter.ps1 -DryRun -Verbose
```

### 3. InteractiveErrorFixer.ps1
**用途**: エラーの対話的修正
**機能**: 
- コンパイルエラーの自動解析
- 修正候補の提示
- 段階的エラー修正
- 修正履歴の記録

```powershell
# 対話的修正
.\InteractiveErrorFixer.ps1 -InputFile "file.lean"

# 自動修正モード
.\InteractiveErrorFixer.ps1 -InputFile "file.lean" -AutoFix
```

## 🎯 変換ルール

### Import文変換
| 元のコード | 変換後 |
|-----------|--------|
| (なし) | `import Mathlib.Tactic.Basic` |
| `import Std` | `import Mathlib.Init.Logic` |

### 型変換
| 元の型 | 変換後 |
|--------|--------|
| `Int` | `ℤ` |
| `Nat` | `ℕ` |
| `Real` | `ℝ` |

### 定理名変換
| 元の定理名 | 変換後 |
|-----------|--------|
| `Nat.add_zero` | `add_zero` |
| `Nat.zero_add` | `zero_add` |
| `Nat.add_comm` | `add_comm` |

### 戦術変換
| 元の戦術 | 変換後 |
|----------|--------|
| `exact ⟨x⟩` | `use x` |
| (特殊な構文) | (Mathlib標準構文) |

## 📊 実行例

### 変換前 (square_even_standalone.lean)
```lean
-- 平方が偶数なら元の数も偶数であることの証明
def MyEven (n : Int) : Prop := ∃ k : Int, n = 2 * k

theorem even_square_main (n : Int) : MyEven (n * n) → MyEven n := by
  sorry
```

### 変換後 (square_even_standalone_mathlib.lean)
```lean
import Mathlib.Tactic.Basic

-- 平方が偶数なら元の数も偶数であることの証明  
def MyEven (n : ℤ) : Prop := ∃ k : ℤ, n = 2 * k

theorem even_square_main (n : ℤ) : MyEven (n * n) → MyEven n := by
  sorry
```

## 🔍 エラーパターンと解決策

### よくあるエラーと自動修正

#### 1. Missing Import エラー
**エラー**: `object file ... does not exist`
**自動修正**: 
- 必要なimport文を追加
- `import Mathlib.Data.Nat.Basic`
- `import Mathlib.Tactic.Basic`

#### 2. Unknown Tactic エラー  
**エラー**: `unknown tactic 'use'`
**自動修正**:
- `import Mathlib.Tactic.Use` 追加
- または代替戦術 `exact ⟨⟩` に置換

#### 3. Type Mismatch エラー
**エラー**: `expected ℕ got Nat`
**自動修正**:
- 全体的な型名置換
- Unicode記号への統一

## 🚀 使用手順

### ステップ1: 単一ファイル変換テスト
```powershell
# まずプレビューで確認
.\SimpleMathLibConverter.ps1 -InputFile "your_file.lean" -DryRun -Verbose

# 問題なければ実際の変換
.\SimpleMathLibConverter.ps1 -InputFile "your_file.lean"
```

### ステップ2: エラー修正
```powershell
# 変換結果にエラーがある場合
.\InteractiveErrorFixer.ps1 -InputFile "your_file_mathlib.lean" -AutoFix
```

### ステップ3: プロジェクト全体変換
```powershell
# 全ファイル一括変換
.\BatchMathLibConverter.ps1 -ProjectPath "." -OutputDir "mathlib-converted"
```

### ステップ4: 結果確認
```powershell
# 生成されたレポート確認
Get-Content "mathlib-conversion\batch_report_*.md"
```

## 📈 変換成功事例

### 実際の変換結果
```
Converting Lean file to Mathlib format: square_even_standalone.lean
Converted: 'def MyEven (n : Int)' -> 'def MyEven (n : ℤ)'
Converted: 'theorem even_square_main (n : Int)' -> 'theorem even_square_main (n : ℤ)'
Added Mathlib.Tactic.Basic import
Conversion completed!
Changes applied: 11
```

### 検出される変換ポイント
- **Type conversions**: 10個の Int → ℤ 変換
- **Import additions**: 1個の基本import追加  
- **総変更点**: 11箇所

## 🔧 カスタマイズ

### 変換ルールの追加
`SimpleMathLibConverter.ps1` 内の変換ルールを編集:

```powershell
# 新しい定理名変換を追加
$convertedLine = $convertedLine -replace "MyTheorem", "StandardTheorem"

# 新しい戦術変換を追加  
$convertedLine = $convertedLine -replace "my_tactic", "standard_tactic"
```

### エラーパターンの拡張
`InteractiveErrorFixer.ps1` 内のパターンを追加:

```powershell
"new error pattern" = @{
    Type = "NewErrorType"
    Solutions = @(
        @{Action = "AddImport"; Import = "Mathlib.New.Module"}
    )
}
```

## 📝 制限事項と注意点

### 現在の制限
- **Unicode問題**: 一部Unicode文字の表示問題
- **複雑な構文**: 高度な証明構造の変換は制限的
- **依存関係**: Mathlibビルド完了が前提

### 推奨ワークフロー
1. **バックアップ作成**: 変換前に必ずバックアップ
2. **段階的変換**: 一つずつファイル変換して確認
3. **テスト実行**: 変換後は必ずコンパイルテスト
4. **手動調整**: 自動変換で対応できない部分は手動修正

## 🎯 期待される改善

### 変換システム導入効果
- **作業効率**: 手動変換作業の大幅短縮
- **エラー削減**: 一般的な変換ミスの自動回避
- **一貫性**: プロジェクト全体での統一的な変換

### 今後の拡張予定
- より高度なエラー修正パターン
- 証明構造の自動最適化
- インタラクティブな変換提案

---

**変換システムで効率的なMathlib移行を実現しましょう！**