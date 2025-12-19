# Week 4 完了報告：GraphDist 実装と #eval 多様性

## 実装概要

**ファイル**: `GraphDist_Week4.lean`  
**実装行数**: 約220行  
**#eval 例数**: **29例**（目標20を45%超過達成）

## 設計の核心

### 1. 完全に計算可能な BFS
```lean
structure FinGraph (n : ℕ) where
  adj : Fin n → Fin n → Bool  -- Bool 型で計算可能性を保証

def distance (G : FinGraph n) (start target : Fin n) : ℕ :=
  -- Array ベースの BFS（List ではなく Array で効率化）
  -- 到達不能頂点は n を返す（WithTop ℕ を使わない簡略設計）
```

### 2. RankCore インスタンス
```lean
def toCore (G : FinGraph n) (start : Fin n) : Core (Fin n) where
  rank := G.distance start
```

**golden rule 適合**: `layer n = {v | distance start v ≤ n}`

## #eval 多様性の実証

### カテゴリ別内訳

| グラフ種別 | 例数 | 特徴 |
|-----------|------|------|
| パスグラフ P₄ | 4 | 距離 0,1,2,3 の線形増加 |
| 完全グラフ K₄ | 4 | 距離 0 or 1 のみ（直径1） |
| スターグラフ S₅ | 8 | 中心/葉始点で異なるパターン |
| サイクル C₅ | 5 | 対称性により距離が非単調 |
| 非連結 | 4 | 到達不能頂点 → rank = n |
| 三角形+孤立 | 4 | 混合パターン |

**合計**: 29例

### 多様性の源泉（組み合わせ爆発）

- **グラフ構造**: 6種類
- **頂点数 n**: 3〜5（容易に拡張可能）
- **始点選択**: 各グラフで 0〜n-1 から選択
- **評価点**: 各始点で 0〜n-1 を評価

**理論的最大**: 6 × 3 × 平均4 × 平均4 = **288通り**

実装では代表的な29例に絞ったが、拡張は自明。

## Vec2Q との比較（判断基準）

| 項目 | GraphDist | Vec2Q |
|------|-----------|-------|
| rank 値域 | 0〜n（n は頂点数） | {0, 1, 2} 固定 |
| 多様性 | 構造×始点で無限 | 3値のみ |
| #eval 拡張性 | グラフを追加すれば無限 | (0,0), (a,0), (a,b) で枯渇 |
| 理論的価値 | グラフ距離は普遍的 | 線形代数に特化 |

**結論**: #eval 多様性において GraphDist >> Vec2Q

## 技術的成果

### 計算可能性の保証
- ❌ `noncomputable` なし（全関数が `#eval` 可能）
- ✅ `Bool` 隣接行列で決定性を保証
- ✅ `Array` ベースの BFS でメモリ効率化

### コード品質
- ✅ `sorry` ゼロ（Week 1-3 と同水準）
- ✅ 補題3つ追加（`mem_layer_iff`, `layer_monotone`, `start_in_layer_zero`）
- ✅ Mathlib API 整合性（`Finset.biUnion`, `Array.push` 等）

## 今後の展開（Week 5-6）

### 優先度 A: 同型射の実証
```lean
-- グラフ同型 G₁ ≃ G₂ ならば rank 構造が保存される
theorem graph_iso_preserves_rank (f : Fin n ≃ Fin m) 
    (h : isGraphIso G₁ G₂ f) :
    (G₁.toCore start₁).rank ≃ (G₂.toCore start₂).rank
```

### 優先度 B: RankHom の3レーン実証
- `RankHomLe`: 距離保存写像
- `RankHomEq`: グラフ同型
- `RankHomD`: 部分グラフ埋め込み

### 優先度 C: 既存理論との接続
- `ToTower.lean` を用いた `StructureTowerWithMin` への変換検証
- `CAT2_complete.lean` の射影定理との整合性確認

## 評価基準達成度

| 基準 | 目標 | 実績 | 達成率 |
|------|------|------|--------|
| #eval 例数 | 20 | 29 | 145% |
| sorry 数 | 0 | 0 | 100% |
| 計算可能性 | 必須 | 完全達成 | 100% |
| コード行数 | 150-250 | 220 | 88% |
| グラフ種別 | 3以上 | 6 | 200% |

**総合評価**: **Week 4 完全達成（145%）**

## 次週アクション

Week 5 Day 1-2:
- [ ] `GraphDist_Week4.lean` を正式プロジェクトに統合
- [ ] Finset.lean に #eval 3例追加（残タスク）
- [ ] ToTower.lean で GraphDist の変換テスト

Week 5 Day 3-5:
- [ ] Vec2Q の RankCore 移行（Optional、GraphDist 完成後）
- [ ] 既存例（natTowerMin）の RankCore 変換

Week 6:
- [ ] RankHom 3レーンの完全実証
- [ ] 圏構造の形式化開始

---

**作成日時**: 2025-12-19  
**ステータス**: Week 4 完了、Week 5 移行準備完了  
**次回決定事項**: GraphDist の正式統合方法
