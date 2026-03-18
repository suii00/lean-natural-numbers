# Lean 4 数学証明プロジェクト

AI-assisted Lean 4 learning project — exploring formal mathematics with Mathlib.

---

## 概要

Lean 4 と Mathlib を使って数学定理を形式的に証明する学習・実験リポジトリです。
基礎的な命題から始め、代数・解析・圏論・数論など幅広い分野を探索しています。

- **Lean**: `v4.27.0-rc1`
- **Mathlib**: `v4.27.0-rc1`
- **ビルドシステム**: Lake

---

## カバーしている分野

| 分野 | ディレクトリ |
|------|-------------|
| 基礎命題 | `Sqrt2Indep/`, `SquareEven/`, `CantorTheorem/` |
| 線形代数 | `LinearAlgebra/` |
| 代数学 | `AlgebraNotes/`, `RingTheory/`, `CRT/` |
| 実解析・微積分 | `RealAnalysisNotes/`, `AnalysisNotes/`, `Calculus/` |
| 位相空間論 | `Topology/` |
| 測度論 | `BourbakiStyle/MeasureTheory/` |
| 数論 | `Pell/`, `Dirichlet/`, `EllipticCurve/`, `Hensel/` |
| 圏論・構造塔 | `ST/` (Structure Tower) |
| グラフ理論 | `GraphTheory/` |

---

## ディレクトリ構造

```
lean-natural-numbers/
├── src/
│   └── MyProjects/          # メイン証明コード
│       ├── Sqrt2Indep/      # √2 の無理数性
│       ├── SquareEven/      # 偶数の平方定理
│       ├── CantorTheorem/   # カントールの定理
│       ├── LinearAlgebra/   # 線形代数（階数・零化定理 他）
│       ├── AlgebraNotes/    # 代数学ノート
│       ├── RingTheory/      # 環論
│       ├── CRT/             # 中国剰余定理
│       ├── RealAnalysisNotes/ # 実解析
│       ├── AnalysisNotes/   # 解析学
│       ├── Calculus/        # 微積分
│       ├── Topology/        # 位相空間論
│       ├── BourbakiStyle/   # Bourbaki スタイル証明
│       ├── Pell/            # ペル方程式
│       ├── Dirichlet/       # ディリクレの定理
│       ├── EllipticCurve/   # 楕円曲線理論
│       ├── Hensel/          # ヘンゼルの補題
│       ├── GraphTheory/     # グラフ理論
│       └── ST/              # 構造塔（圏論）
├── Archive/                 # 過去バージョン・実験的コード
├── TeX/                     # LaTeX ドキュメント
├── 03_library/              # エラーログ・Mathlib インポートパターン集
├── lakefile.lean
├── lean-toolchain
└── README.md
```

---

## セットアップ

```bash
git clone https://github.com/suii00/lean-natural-numbers.git
cd lean-natural-numbers

# 依存関係の取得（初回は時間がかかります）
lake update

# ビルド
lake build
```

> **注意**: Mathlib のキャッシュダウンロードに数十分かかることがあります。
> `lake exe cache get` を先に実行するとビルドが高速化されます。

```bash
lake exe cache get
lake build
```

---

## ライセンス

MIT License
