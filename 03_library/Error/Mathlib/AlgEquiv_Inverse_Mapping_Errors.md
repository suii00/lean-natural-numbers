# AlgEquiv逆元写像エラー - Stage 4 Implementation

## エラー詳細
**日付**: 2025-01-25  
**ファイル**: `GaloisCorrespondenceStage4.lean`

## 1. AlgEquiv逆元写像API不明エラー

### エラーメッセージ
```
error: unknown constant 'AlgEquiv.map_inv'
```

### 問題のあったコード
```lean
lemma fixed_inv_mem (H : Subgroup (GaloisGroup F K)) {x : K}
  (hx : x ∈ fixedBySubgroup H) :
  x⁻¹ ∈ fixedBySubgroup H := by
  intro σ hσ
  rw [AlgEquiv.map_inv, hx σ hσ]  -- AlgEquiv.map_inv が存在しない
```

### 原因
- 期待したAPI: `AlgEquiv.map_inv`
- 実際の状況: 体の自己同型での逆元写像APIが不明確
- `map_inv`は他の構造（Group homomorphismなど）では存在

### 解決方法（Explore Mode）
```lean
lemma fixed_inv_mem (H : Subgroup (GaloisGroup F K)) {x : K}
  (hx : x ∈ fixedBySubgroup H) :
  x⁻¹ ∈ fixedBySubgroup H := by
  -- TODO: reason="AlgEquiv逆元写像の正しいAPI", 
  --       missing_lemma="map_inv_for_AlgEquiv", priority=med
  sorry
```

### API調査が必要な項目
- `K ≃ₐ[F] K`型での逆元保存性質
- 体の自己同型の逆元に関する補題
- Mathlibでの正しいAPI名

## 教訓

### AlgEquiv API理解の深化必要性
1. **準同型性質**: `map_mul`, `map_add`は存在
2. **逆元性質**: 体特有のAPIが必要
3. **文書調査**: 具体的API名の確認が重要

### Explore Mode戦略の有効性
- 不明なAPIは即座にsorryで記録
- TODO形式で将来調査を明確化
- 全体実装を止めずに進行継続

### 次回への提言
- `#check`での事前API確認
- Mathlib4 Docsでの体自己同型API調査
- `K ≃ₐ[F] K`の完全なAPI理解