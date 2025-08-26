# IntermediateField構築パターン - Stage 4 Implementation

## 成功パターンの記録
**日付**: 2025-01-25  
**ファイル**: `GaloisCorrespondenceStage4.lean`

## IntermediateField構築の成功事例

### パターン1: toSubalgebra継承による構築
```lean
def subgroup_to_intermediate (H : Subgroup (GaloisGroup F K)) : IntermediateField F K where
  -- Subalgebra部分を継承
  toSubalgebra := {
    carrier := fixedBySubgroup H
    mul_mem' := fixed_mul_mem H
    one_mem' := (fixed_contains_zero_one H).2
    add_mem' := fixed_add_mem H  
    zero_mem' := (fixed_contains_zero_one H).1
    algebraMap_mem' := fixed_contains_base H
  }
  -- IntermediateFieldに必要な逆元閉性のみ追加
  inv_mem' := fun {x} hx => fixed_inv_mem H hx
```

### 発見した設計パターン
1. **継承の活用**: `extends Subalgebra`の威力
2. **最小追加**: `inv_mem'`のみでIntermediateField完成
3. **補助関数**: 各閉性を別関数で証明

## 補助関数の効果的分割

### 基本性質の分離
```lean
-- 基本要素を含む性質
lemma fixed_contains_zero_one : (0 : K) ∈ fixedBySubgroup H ∧ (1 : K) ∈ fixedBySubgroup H
lemma fixed_contains_base : ∀ a : F, algebraMap F K a ∈ fixedBySubgroup H

-- 演算に対する閉性
lemma fixed_mul_mem : x ∈ fixedBySubgroup H → y ∈ fixedBySubgroup H → x * y ∈ fixedBySubgroup H  
lemma fixed_add_mem : x ∈ fixedBySubgroup H → y ∈ fixedBySubgroup H → x + y ∈ fixedBySubgroup H
lemma fixed_inv_mem : x ∈ fixedBySubgroup H → x⁻¹ ∈ fixedBySubgroup H  -- sorry
```

### 利点
1. **可読性**: 各性質が明確に分離
2. **再利用性**: 他の構築でも活用可能
3. **デバッグ容易性**: 個別にテスト可能

## 成功した証明手法

### 準同型性質の活用
```lean
lemma fixed_mul_mem {x y : K} (hx : x ∈ fixedBySubgroup H) (hy : y ∈ fixedBySubgroup H) :
  x * y ∈ fixedBySubgroup H := by
  intro σ hσ
  rw [map_mul, hx σ hσ, hy σ hσ]  -- map_mulが決定的
```

### F-線形性の威力
```lean  
lemma fixed_contains_base (a : F) : algebraMap F K a ∈ fixedBySubgroup H := by
  intro σ hσ
  exact σ.commutes a  -- AlgEquiv.commutesが決定的
```

## 困難な部分とその対処

### 逆元写像の問題
```lean
-- 困難: AlgEquiv.map_invが存在しない
lemma fixed_inv_mem : x⁻¹ ∈ fixedBySubgroup H := by
  -- TODO with priority記録でExplore Mode継続
  sorry
```

### 複雑な同値証明の問題  
```lean
-- 困難: 全ガロア群→基体の対応
lemma subgroup_to_intermediate_top : subgroup_to_intermediate ⊤ = ⊥ := by
  -- TODO with priority記録でExplore Mode継続  
  sorry
```

## 設計原則の確立

### 1. 段階的構築
- 基本性質 → 演算閉性 → 構造構築
- 各段階で独立したlemma

### 2. API最大活用
- `map_mul`, `map_add`: 準同型性質
- `AlgEquiv.commutes`: F-線形性
- 既存の型クラスインスタンス

### 3. Explore Mode戦略
- 困難な部分は即座にsorry + TODO
- 成功パターンの蓄積優先
- 全体進行の継続

## 次段階への応用

### Stage 3-4の統合パターン
- 双方向対応の実装完了
- 同様のパターンで Stage 5-6（単射性・全射性）実装可能
- 確立した設計原則の活用

### 再利用可能なコンポーネント
- `fixedBySubgroup` / `fixingSubgroup`概念
- 閉性証明のパターン
- IntermediateField構築手法