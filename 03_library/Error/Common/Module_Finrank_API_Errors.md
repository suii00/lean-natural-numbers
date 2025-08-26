# Module.finrank API発見エラー - Stage 7 Implementation

## エラー詳細
**日付**: 2025-01-26  
**ファイル**: `GaloisCorrespondenceStage7.lean`

## 1. FiniteDimensional.finrank API不存在エラー

### エラーメッセージ
```
error: unknown constant 'FiniteDimensional.finrank'
```

### 問題のあったコード
```lean
theorem fundamental_theorem_degree_relation [FiniteDimensional F K] [IsGalois F K]
  (H : Subgroup (GaloisGroup F K)) :
  H.index = FiniteDimensional.finrank F (subgroup_to_intermediate H) ∧
  Nat.card H = FiniteDimensional.finrank (subgroup_to_intermediate H) K
```

### 根本原因
- **Mathlib4 APIの変更**: `FiniteDimensional.finrank`は存在しない
- **名前空間の混同**: Mathlib3からMathlib4への移行での名前変更
- **事前調査不足**: API存在確認せずに推測で使用

### API発見プロセス

#### 段階1: エラーからの手がかり収集
```lean
-- 期待していたAPI（不存在）
FiniteDimensional.finrank : ∀ (R : Type*) (M : Type*) [Ring R] [AddCommGroup M] [Module R M] [FiniteDimensional R M], ℕ
```

#### 段階2: 類似APIの探索
```bash
# Mathlib内での検索戦略
rg "finrank" --type lean  # ripgrepでの検索
rg "FiniteDimensional" --type lean  # 関連名前空間確認
```

#### 段階3: 正しいAPIの発見
```lean
-- 実際に存在するAPI
Module.finrank : ∀ (R : Type*) (M : Type*) [Ring R] [AddCommGroup M] [Module R M], ℕ
```

### API修正の過程

#### 修正前（エラー）
```lean
H.index = FiniteDimensional.finrank F (subgroup_to_intermediate H) ∧
Nat.card H = FiniteDimensional.finrank (subgroup_to_intermediate H) K
```

#### 修正後（成功）
```lean
H.index = Module.finrank F (subgroup_to_intermediate H) ∧
Nat.card H = Module.finrank (subgroup_to_intermediate H) K
```

### 学習成果

#### 1. Mathlib4の次数API体系
```lean
-- 基本的な次数API
Module.finrank (R : Type*) (M : Type*) [Ring R] [AddCommGroup M] [Module R M] : ℕ

-- 体拡大での特殊化
Module.finrank (F : Type*) (K : Type*) [Field F] [Field K] [Algebra F K] : ℕ

-- 使用例
#check Module.finrank ℚ ℝ  -- ℝ の ℚ 上の次元（無限）
#check Module.finrank F K   -- K の F 上の拡大次数
```

#### 2. FiniteDimensionalとの関係
```lean
-- FiniteDimensionalは条件、finrankは値
variable [FiniteDimensional F K]  -- K/F が有限拡大
#check Module.finrank F K         -- その次数を取得

-- 条件付き等式
theorem finrank_eq_card_basis [FiniteDimensional F K] : 
  Module.finrank F K = Fintype.card (Basis.ofVectorSpaceIndex F K)
```

#### 3. ガロア理論での応用
```lean
-- ガロア群の位数と拡大次数の関係
theorem galois_degree_formula [FiniteDimensional F K] [IsGalois F K] :
  Fintype.card (K ≃ₐ[F] K) = Module.finrank F K

-- 中間体による次数分解
theorem tower_law [FiniteDimensional F K] (L : IntermediateField F K) :
  Module.finrank F K = Module.finrank F L * Module.finrank L K
```

## 2. API調査手法の確立

### 有効な調査戦略

#### 1. エラーメッセージからのAPI推測
```lean
-- エラー: unknown constant 'X.Y'
-- → 名前空間Xでの関数Y探索
-- → 類似名前空間での同名関数探索
-- → 機能的に同等な代替API探索
```

#### 2. #check による段階的確認
```lean
#check FiniteDimensional  -- 名前空間存在確認
#check Module             -- 代替名前空間確認  
#check Module.finrank     -- 具体的API確認
#check @Module.finrank    -- 完全型シグネチャ確認
```

#### 3. 文書・コード検索の併用
- **Mathlib4 docs**: 公式API文書
- **GitHub検索**: 実際の使用例
- **ripgrep**: ローカルMathlib検索

### 回避すべき間違ったアプローチ

#### ❌ 推測による実装
```lean
-- 存在しないAPIを推測で使用
FiniteDimensional.finrank F K  -- エラー必至
```

#### ❌ 即座のsorryによる回避
```lean
-- TODO: reason="API不明", missing_lemma="finrank_API", priority=low
sorry  -- 学習機会を逃す
```

#### ❌ エラーメッセージの無視
```
error: unknown constant 'FiniteDimensional.finrank'
-- → 「後で調べよう」として放置
```

### ✅ 推奨される学習アプローチ

#### 1. エラー即座調査
```lean
-- エラー発生 → 即座に調査開始
#check FiniteDimensional.finrank  -- 存在確認
#check Module.finrank             -- 代替確認
```

#### 2. 段階的API理解
```lean
-- 基本理解
#check Module.finrank

-- 型制約理解  
#check @Module.finrank

-- 関連定理理解
#check Module.finrank_eq_card_basis
```

#### 3. 実用例での検証
```lean
-- 簡単な例で動作確認
example [FiniteDimensional ℚ ℝ] : Module.finrank ℚ ℝ = 0 := sorry  -- 無限次元
example : Module.finrank ℚ (ℚ⟨√2⟩) = 2 := sorry                    -- 2次拡大
```

## 教訓

### API発見の体系的手法
1. **エラーファースト**: エラーメッセージから必要APIを特定
2. **段階的調査**: 名前空間 → 関数 → 型 → 使用例の順
3. **検証重視**: 簡単な例での動作確認必須

### 将来への応用
- 新しいMathlib APIに遭遇した際の調査フロー確立
- エラーメッセージから学習機会を最大化する習慣
- 推測より調査を優先する開発マインドセット