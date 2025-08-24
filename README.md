# Lean 4 数学証明プロジェクト

## プロジェクト概要
Lean 4を使用した数学定理の形式的証明プロジェクトです。基本的な数学定理から始め、より高度な証明へと段階的に発展させています。

## 完了した成果

### Mathlib移行完了 (2025年8月)
- Mathlibの完全統合に成功
- エラー解析とドキュメント化の完了

### 実装済み証明

#### 基礎数学証明
- **√2の無理数性** (`src/MyProjects/Sqrt2Indep/`)
  - 完全な独立証明の実装
  - Mathlibタクティクを使用した最適化版
  
- **偶数の平方は偶数** (`src/MyProjects/SquareEven/`)
  - 基本版から完全版まで段階的実装
  - Mathlib版での実装完了

#### 高度な数学証明
- **線形期待値の定理** (`LinearityOfExpectation.lean`)
  - 確率論の基本定理の形式化
  - 複数バージョンでの実装

- **階数・零化定理** (`Rank_Nullity.lean`, `Rank_Nullity_Bourbaki.lean`)
  - 線形代数の基本定理
  - ブルバキスタイルの証明も実装

- **カントールの定理** (`src/MyProjects/cantor_theorem/`)
  - 集合論の基礎定理
  - ZFC公理系での実装

- **中国剰余定理** (`src/MyProjects/CRT/`)
  - 数論の重要定理
  - 多段階実装とBourbakiスタイル

- **楕円曲線理論** (`src/MyProjects/EllipticCurve/`)
  - 代数幾何の基礎
  - 高度な理論への拡張

- **ヘンゼルの補題** (`src/MyProjects/Hensel/`)
  - p進数論の基礎
  - 完全な形式化実装

- **ペル方程式** (`src/MyProjects/Pell/`)
  - ディオファントス方程式
  - 数論的アプローチ

- **ディリクレの定理** (`src/MyProjects/Dirichlet/`)
  - 解析的数論
  - L関数の実装

- **対称行列の固有値** (`src/MyProjects/symmetric_matrix_proof/`)
  - 線形代数の重要定理
  - スペクトル理論への応用

- **群論の基本定理** (`src/MyProjects/group_theory_proofs/`)
  - 抽象代数の基礎
  - 複数の定理を実装

## 次期開発計画

### 1. より高度な数学証明への挑戦
- **解析学分野**
  - εδ論法による連続性の証明
  - 微分可能性と連続性の関係
  - テイラー級数の収束性
  
- **代数学分野**
  - 群論の基本定理（ラグランジュの定理など）
  - 環と体の構造定理
  - ガロア理論の基礎
  
- **数論分野**
  - フェルマーの小定理
  - オイラーの定理
  - 素数定理への準備

### 2. 他の数学分野への拡張
- **位相空間論**
  - コンパクト性と連続写像
  - ハウスドルフ空間の性質
  - チコノフの定理への道
  
- **圏論**
  - 関手と自然変換
  - 米田の補題
  - 随伴関手
  
- **確率論**
  - 測度論的確率論の基礎
  - 大数の法則
  - 中心極限定理

### 3. インフラストラクチャの強化
- **自動証明支援システム**
  - タクティク推薦システム
  - 証明パターン学習機能
  - 並列証明検証
  
- **ドキュメント生成**
  - 証明の自動可視化
  - インタラクティブな証明探索
  - 教育用資料の自動生成

## プロジェクト構造

```
myproject/
├── src/MyProjects/           # メイン証明ディレクトリ
│   ├── Sqrt2Indep/        # √2の無理数性
│   ├── SquareEven/        # 偶数の平方定理
│   ├── CRT/               # 中国剰余定理
│   ├── EllipticCurve/     # 楕円曲線理論
│   ├── Hensel/            # ヘンゼルの補題
│   ├── Pell/              # ペル方程式
│   ├── Dirichlet/         # ディリクレの定理
│   ├── cantor_theorem/    # カントールの定理
│   ├── group_theory_proofs/ # 群論の証明
│   ├── symmetric_matrix_proof/ # 対称行列の証明
│   ├── AlgebraNotes/      # 代数学ノート
│   ├── TopologyBasics/    # 位相空間論の基礎
│   ├── MeasureNotes/      # 測度論ノート
│   ├── OrderNotes/        # 順序論ノート
│   └── RealAnalysisNotes/ # 実解析ノート
├── 03_library/            # ライブラリドキュメント
│   ├── Error/             # エラードキュメント
│   └── imports/           # Mathlib4インポートパターン
└── *.lean                 # トップレベル証明ファイル
```


## 技術スタック
- **Lean 4**: 証明支援システム (v4.22.0)
- **Mathlib4**: 数学ライブラリ (v4.22.0)
- **Lake**: ビルドシステム (v5.0.0)
- **Git**: バージョン管理

## セットアップ

```bash
# リポジトリのクローン
git clone https://github.com/suii00/lean-natural-numbers.git
cd myproject

# Lean環境のセットアップ
lake update
lake build

# 特定の証明をビルド
lake build MyProjects
```

## 使用方法

### 証明の実行
```bash
# 個別の証明ファイルをチェック
lean --run src/MyProjects/Sqrt2Indep/Complete.lean

# すべての証明をビルド
lake build
```


## 貢献方法
1. このリポジトリをフォーク
2. 新しいブランチを作成 (`git checkout -b feature/new-proof`)
3. 変更をコミット (`git commit -m 'Add new proof'`)
4. ブランチにプッシュ (`git push origin feature/new-proof`)
5. プルリクエストを作成

## ライセンス
MIT License

## 連絡先
プロジェクトに関する質問や提案は、Issueセクションでお願いします。