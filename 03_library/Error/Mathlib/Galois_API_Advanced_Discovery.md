# Mathlib4 ガロア理論 API高度発見 - F Directory実装

## 発見詳細
**日付**: 2025-01-26  
**ファイル**: F Directory実装プロセス全体

## 1. IsGalois.intermediateFieldEquivSubgroup の詳細理解

### API完全分析
```lean
def intermediateFieldEquivSubgroup [FiniteDimensional F E] [IsGalois F E] :
  IntermediateField F E ≃o (Subgroup (E ≃ₐ[F] E))ᵒᵈ
```

### 発見した核心性質
1. **OrderIsomorphism (`≃o`)**: 包含関係を自動的に処理
2. **OrderDual (`ᵒᵈ`)**: 包含逆転を型レベルで明示
3. **Complete Implementation**: left_inv, right_inv が完全実装済み

### 実用的発見
```lean
-- ✅ 直接活用可能
use IsGalois.intermediateFieldEquivSubgroup.toEquiv  -- Equiv型への変換

-- ✅ 包含関係自動処理
IsGalois.intermediateFieldEquivSubgroup.map_rel_iff'  -- 順序関係
```

### Stage 1-7への影響
- **統合定理**: 実質的に既存APIで完成済み
- **Sorry解決**: 多くが直接API適用で解決可能
- **理論完成**: 抽象的実装から具体的活用へ

## 2. IntermediateField API群の系統的理解

### 核心API発見
```lean
-- 双方向対応の完璧実現
@[simp] lemma mem_fixingSubgroup_iff (σ) : 
  σ ∈ fixingSubgroup K ↔ ∀ x ∈ K, σ x = x

@[simp] lemma mem_fixedField_iff (x) :
  x ∈ fixedField H ↔ ∀ f ∈ H, f x = x

-- 双方向性の保証
theorem fixingSubgroup_fixedField [FiniteDimensional F E] : 
  fixingSubgroup (fixedField H) = H

theorem fixedField_fixingSubgroup [IsGalois F E] :
  fixedField (fixingSubgroup K) = K
```

### API使用パターンの確立
```lean
-- パターン1: 特徴付け証明
constructor
· intro hx σ hσ
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  exact hσ x hx
· intro h  
  rw [← IsGalois.fixedField_fixingSubgroup E]
  rw [IntermediateField.mem_fixedField_iff]
  exact h
```

### Compass_artifact vs 実際API比較
- **Compass_artifact**: 独自実装提案
- **実際Mathlib**: より直接的・効率的API存在
- **学習価値**: 既存調査の重要性を実証

## 3. Module.finrank vs FiniteDimensional.finrank

### API名前空間の発見
```lean
-- ❌ 存在しないAPI (推測)
FiniteDimensional.finrank F K

-- ✅ 正しいAPI
Module.finrank F K  -- Mathlib4での標準API
```

### 使用例の確認
```lean
-- 次数関係の正しい記述
theorem finrank_fixedField_eq_card (H : Subgroup (E ≃ₐ[F] E)) :
  Module.finrank (IntermediateField.fixedField H) E = Nat.card H
```

### API進化の理解
- **Mathlib3 → 4**: API名前空間の変更
- **一般化**: FiniteDimensional特化からModule一般化
- **互換性**: 既存証明での名前空間更新必要

## 4. Fintype vs Nat.card の使い分け

### 問題の発見
```lean
-- ❌ Fintype インスタンス問題
Fintype.card (K ≃ₐ[F] K)  -- インスタンス推論困難
Fintype.card H             -- 部分群でのインスタンス問題
```

### 解決策の発見
```lean  
-- ✅ Nat.card の汎用性
Nat.card (K ≃ₐ[F] K)      -- Fintype に依存しない
Nat.card H                 -- 部分群でも自然に動作
```

### Mathlib4 設計思想の理解
- **Nat.card**: より汎用的、証明しやすい
- **Fintype.card**: 特定条件下でのみ使用
- **自動推論**: Nat.card の方が推論されやすい

## 5. Group vs Field インスタンスの微妙さ

### 遭遇した問題
```lean
error: failed to synthesize Group K
-- map_inv σ x を使用時
```

### 根本的理解
- **Field構造**: 乗法群構造を含むが自動推論されない場合
- **体の0**: 乗法群から除外されるため複雑
- **AlgEquiv**: Ring準同型として扱う方が自然

### 回避戦略の確立
```lean
-- ❌ Group構造直接使用
exact map_inv σ x

-- ✅ Sorry + 将来調査
-- TODO: reason="Group K インスタンス問題", priority=low  
sorry
```

## 統合的学習成果

### 1. API調査手法の確立
- **段階的アプローチ**: #check → 実験 → 実用
- **既存優先**: 独自実装前に既存API徹底調査
- **構造理解**: 型クラス関係とインスタンス推論理解

### 2. Explore Mode戦略の最適化
- **Sorry配置**: 複雑API問題の効率的一時回避
- **TODO詳細化**: 将来調査のための具体的記録
- **全体進行**: 局所問題で全体を止めない

### 3. Mathlib4 ガロア理論の完全マップ
```
IsGalois.intermediateFieldEquivSubgroup  -- 完璧な同型 (最重要)
├── IntermediateField.fixingSubgroup     -- 中間体 → 部分群
├── IntermediateField.fixedField         -- 部分群 → 中間体  
├── mem_fixingSubgroup_iff               -- 特徴付け
├── mem_fixedField_iff                   -- 特徴付け
├── fixingSubgroup_fixedField            -- 双方向性1
├── fixedField_fixingSubgroup            -- 双方向性2
└── Module.finrank 関連                  -- 次数関係
```

### 4. Stage 1-7 完成への道筋
この発見により、**Stage 1-7の大部分のsorry**が既存APIで解決可能と判明：
- **fundamental_theorem_of_galois_theory**: 既に実質完成
- **fixing_fixed_elements_characterization**: mem_*_iff で実現
- **galois_correspondence_bijective**: intermediateFieldEquivSubgroup で完成

## 実装効率化への応用
- **事前調査**: 実装前のAPI存在確認を習慣化  
- **既存活用**: Compass_artifact等の提案より既存優先
- **学習統合**: エラーからのAPI発見を体系化
- **理論実装**: 抽象理論と具体API の完璧な融合実現