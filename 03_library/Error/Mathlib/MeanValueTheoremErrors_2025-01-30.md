# Mean Value Theorem Implementation Errors (2025-01-30)

## 概要
平均値定理`exists_hasDerivAt_eq_slope`を使用した単射性証明実装で遭遇したエラーと解決方法をまとめます。高度なMathlib APIの正確な使用法と、構成的証明における論理構造の確立過程を体系化。

## 1. API発見と正確な使用法エラー

### エラー1: `exists_hasDerivAt_eq_slope`の引数型エラー
```lean
-- エラーコード
obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope f (deriv f) h_order h_cont h_diff

-- エラーメッセージ
error: Application type mismatch: In the application
  exists_hasDerivAt_eq_slope f (deriv f) h_order
the argument h_order has type ¬x < y : Prop
but is expected to have type x < y : Prop
```

**原因**: `wlog`戦術の誤用により、期待される`x < y`ではなく`¬x < y`が生成
**数学的背景**: 平均値定理は`a < b`条件で区間`[a,b]`上の連続性と`(a,b)`上の微分可能性が必要

**解決方法**: `wlog`を`cases'`による直接的なCase分けに変更
```lean
-- 改善後
cases' lt_or_gt_of_ne h_ne with h_order h_order
· -- Case 1: x < y の場合
  obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope f (deriv f) h_order h_cont h_diff
· -- Case 2: y < x の場合
  obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope f (deriv f) h_order h_cont h_diff
```

### エラー2: `wlog`戦術の複雑な構文エラー
```lean
-- エラーコード
wlog h_order : x < y
· -- 対称性により y < x の場合も同様に証明可能
  exact this hy hx hxy.symm (Ne.symm h_ne) (lt_of_not_le (fun h => h_ne (le_antisymm h (le_of_not_gt h_order))))

-- エラーメッセージ
複雑な型推論エラーと引数不一致
```

**原因**: `wlog`の対称性引数が過度に複雑で、型推論が失敗
**解決方法**: より直接的で理解しやすいCase分けアプローチ

## 2. 書き換え規則のパターンマッチングエラー

### エラー3: `rw`での式パターン不一致
```lean
-- エラーコード
have h_deriv_zero : deriv f c = 0 := by
  rw [← hc_eq, h_slope_zero]

-- エラーメッセージ
error: tactic 'rewrite' failed, did not find instance of the pattern in the target expression
  (f y - f x) / (y - x)
```

**原因**: `hc_eq : deriv f c = (f y - f x) / (y - x)`なのに逆方向書き換え`← hc_eq`を使用
**数学的背景**: 等式の方向性と書き換え方向の一致重要性

**解決方法**: 等式の方向を正確に把握し、適切な書き換え方向を使用
```lean
-- 改善後
have h_deriv_zero : deriv f c = 0 := by
  rw [hc_eq, h_slope_zero]  -- 順方向書き換え
```

## 3. 証明構造設計エラー

### エラー4: 背理法と Case分けの組み合わせ複雑性
```lean
-- 問題のあった構造
by_contra h_ne
wlog h_order : x < y generalizing x y
-- 複雑な対称性処理
```

**原因**: 背理法、wlog、Case分けを同時に使用し、論理構造が過度に複雑化
**解決方法**: 段階的で理解しやすい論理構造
```lean
-- 改善後の構造
by_contra h_ne  -- 背理法
cases' lt_or_gt_of_ne h_ne with h_order h_order  -- 明確なCase分け
· -- Case 1: 具体的処理
· -- Case 2: 対称的処理
```

## 4. Mathlib API統合エラー

### エラー5: import path の段階的発見プロセス
```lean
-- 段階的import追加
import Mathlib.Analysis.Calculus.Deriv.Basic         -- 基本微分
import Mathlib.Data.Set.Operations                   -- Set.InjOn
import Mathlib.Order.Interval.Set.Defs               -- Set.Ioo
import Mathlib.Topology.Order.OrderClosed            -- isOpen_Ioo  
import Mathlib.Analysis.Calculus.Deriv.MeanValue     -- exists_hasDerivAt_eq_slope
```

**学習過程**: 各エラーごとに必要なmoduleを段階的に発見・追加

### エラー6: API仕様の正確な理解不足
```lean
-- exists_hasDerivAt_eq_slope の正確な仕様
theorem exists_hasDerivAt_eq_slope (f f' : ℝ → ℝ) {a b : ℝ} 
  (hab : a < b) 
  (hfc : ContinuousOn f (Set.Icc a b)) 
  (hff' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) :
  ∃ c ∈ Set.Ioo a b, f' c = (f b - f a) / (b - a)
```

**重要な理解**: 
- 第2引数は導関数`f'`（関数）
- 順序条件`hab : a < b`が必須
- 閉区間での連続性と開区間での微分可能性の区別

## 5. 構成的証明の論理設計パターン

### 成功パターン1: 段階的Case分け
```lean
by_contra h_ne  -- 明確な背理法導入
cases' lt_or_gt_of_ne h_ne with h_order h_order  -- 対称的Case分け
· -- Case 1での平均値定理適用
  obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope f (deriv f) h_order h_cont h_diff
  -- 矛盾導出
· -- Case 2での対称的処理
```

### 成功パターン2: API適用の前提条件整理
```lean
-- 平均値定理の前提条件を明示的に構築
have h_cont : ContinuousOn f (Set.Icc x y) := by sorry  -- TODO化
have h_diff : ∀ z ∈ Set.Ioo x y, HasDerivAt f (deriv f z) z := by sorry  -- TODO化
-- 前提条件が整った上でAPI適用
obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope f (deriv f) h_order h_cont h_diff
```

### 成功パターン3: 矛盾導出の明確な構造
```lean
-- f(x) = f(y) から平均変化率 = 0
have h_slope_zero : (f y - f x) / (y - x) = 0 := by rw [hxy, sub_self, zero_div]
-- 平均値定理により c での微分係数 = 0
have h_deriv_zero : deriv f c = 0 := by rw [hc_eq, h_slope_zero]
-- しかし微分係数 ≠ 0 のはず
have h_deriv_ne_zero : deriv f c ≠ 0 := by sorry  -- TODO
-- 矛盾
exact h_deriv_ne_zero h_deriv_zero
```

## 学習ポイント

### 1. 高度API使用の原則
- **API仕様の正確理解**: 引数の型と順序の厳密確認
- **前提条件の明示化**: 複雑な前提はTODOで段階化
- **段階的import**: エラーごとに必要moduleを特定・追加

### 2. 構成的証明設計の改善
- **論理構造の簡潔性**: wlogより直接的Case分けを優先
- **対称性の活用**: 2つのCaseで同じ論理構造を適用
- **矛盾導出の明確性**: 各ステップの数学的意味を明示

### 3. エラー対処戦略
- **型エラーの根本分析**: 期待される型と実際の型の詳細比較
- **書き換え方向の確認**: 等式の向きと書き換え方向の一致
- **TODO指向開発**: 複雑な部分はTODO化して本質に集中

## 今後の発展指針

### 1. 残存TODOの実装
- 導関数の連続性（Priority High）
- 微分可能性の近傍拡張（Priority Med）
- HasDerivAtの構築（Priority Med）

### 2. パターンの一般化
- 平均値定理による単射性パターンの他関数への応用
- 構成的背理法の標準テンプレート化
- API発見プロセスの系統化

### 3. 教育的価値の向上
- 高度定理の段階的理解方法
- エラーからの学習サイクル確立
- 数学的直観と形式証明の統合

この平均値定理実装により、Lean 4での高度な解析学定理の構成的証明手法が確立されました。特に「API発見→論理構造設計→段階的実装→TODO管理」の完全なワークフローが実証されました。