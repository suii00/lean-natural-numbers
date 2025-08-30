# Constructive Proof Conversion Errors (2025-01-30)

## 概要
媒介変数と陰関数の微分実装における`sorry`を構成的証明に変換する際に遭遇したエラーと解決方法をまとめます。厳密な構成的証明への変換で発生した典型的なエラーパターンを体系化。

## 1. 分数の符号処理エラー

### エラー1: `rfl` failed - 分数の負号位置不一致
```lean
-- エラーコード
theorem circle_parametric_basic (t : ℝ) (ht : Real.sin t ≠ 0) :
  dy_dt / dx_dt = -Real.cos t / Real.sin t := by
  rw [div_neg]
  rfl  -- エラー発生

-- エラーメッセージ
error: tactic 'rfl' failed, the left-hand side
  -(cos t / sin t)
is not definitionally equal to the right-hand side
  -cos t / sin t
```

**原因**: `div_neg`により`-(cos t / sin t)`となったが、目標は`-cos t / sin t`
**数学的背景**: `a/(-b) = -(a/b)` と `-(a/b) = -a/b` の違い

**解決方法**:
```lean
-- 正しいアプローチ
rw [div_neg]          -- cos t / (-sin t) → -(cos t / sin t)
rw [neg_div]          -- -(cos t / sin t) → -cos t / sin t
```

### エラー2: `rewrite` failed - パターンマッチング失敗
```lean
-- エラーコード
theorem ellipse_param_specific :
  dy_dt / dx_dt = -(b * Real.cos t) / (a * Real.sin t) := by
  rw [div_neg]  -- エラー発生

-- エラーメッセージ
error: tactic 'rewrite' failed, did not find instance of the pattern in the target expression
  ?a / -?m.9560
```

**原因**: 複合的な分数`(b * cos t) / (-a * sin t)`で`div_neg`パターンが認識されない
**解決方法**: `field_simp`による直接的な分数操作
```lean
-- 改善後
simp only [show dx_dt = -a * Real.sin t from rfl, show dy_dt = b * Real.cos t from rfl]
field_simp [ht]  -- 分数計算を直接実行、前提条件htを活用
```

## 2. 三角関数恒等式エラー

### エラー3: `mul_comm` の型不一致エラー
```lean
-- エラーコード
theorem circle_tangent_orthogonal (t : ℝ) :
  tangent_x * x + tangent_y * y = 0 := by
  rw [mul_comm Real.cos t Real.sin t]  -- エラー発生

-- エラーメッセージ
error: Application type mismatch: In the application
  mul_comm cos t
the argument
  t
has type
  ℝ : Type
but is expected to have type
  ℝ → ℝ : Type
```

**原因**: `mul_comm`の引数として`Real.cos t`（値）ではなく`Real.cos`（関数）を渡すべき
**数学的背景**: 関数の合成と値の混同

**解決方法**:
```lean
-- 正しいアプローチ - ringで直接解決
simp only [各letの展開]
-- 内積を展開: (-sin t)(cos t) + (cos t)(sin t) = 0
-- ringで直接計算 - 乗法の可換性と分配法則により相殺される
ring
```

## 3. 自動戦術の過度な実行エラー

### エラー4: `no goals to be solved` - 証明完了後の追加操作
```lean
-- エラーコード
theorem ellipse_param_specific :
  dy_dt / dx_dt = -(b * Real.cos t) / (a * Real.sin t) := by
  field_simp
  ring  -- エラー発生（証明が既に完了）

-- エラーメッセージ
error: no goals to be solved
```

**原因**: `field_simp`で証明が完了したが、追加で`ring`を実行
**解決方法**: 証明の進行状況を確認し、必要な戦術のみ使用
```lean
-- 改善後
simp only [各letの展開]
field_simp [ht]  -- これで証明完了
```

## 4. 構成的証明の設計パターン

### 成功パターン1: 段階的な代数操作
```lean
theorem circle_parametric_basic :
  dy_dt / dx_dt = -Real.cos t / Real.sin t := by
  -- 1. 定義を展開
  simp only [show dx_dt = -Real.sin t from rfl, show dy_dt = Real.cos t from rfl]
  -- 2. 分数の符号処理
  rw [div_neg]
  -- 3. 符号の位置調整
  rw [neg_div]
```

### 成功パターン2: 直接的な分数計算
```lean
theorem ellipse_param_specific :
  dy_dt / dx_dt = -(b * Real.cos t) / (a * Real.sin t) := by
  -- 1. 定義展開
  simp only [各let定義]
  -- 2. 分数計算（前提条件付き）
  field_simp [ht]
```

### 成功パターン3: 代数的恒等式の活用
```lean
theorem circle_tangent_orthogonal :
  tangent_x * x + tangent_y * y = 0 := by
  -- 1. 定義展開
  simp only [各let定義]
  -- 2. 代数計算（理由付きring使用）
  ring  -- 乗法可換性と分配法則により相殺される
```

## 5. 平方根の性質証明

### 成功パターン4: 非負性の証明
```lean
theorem arc_length_element :
  ∃ (ds_dt : ℝ), ds_dt^2 = dx_dt^2 + dy_dt^2 := by
  use Real.sqrt (dx_dt^2 + dy_dt^2)
  -- 平方根の定義により、sqrt(a)² = a (a ≥ 0の場合)
  rw [Real.sq_sqrt]
  -- dx_dt^2 + dy_dt^2 ≥ 0 であることを示す
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)
```

## 学習ポイント

### 1. 構成的証明の原則
- **明示的な構成**: `use`で具体的なwitnessを提供
- **段階的展開**: `simp only [show ... from rfl]`で定義を明確化
- **理由付き自動戦術**: `ring`使用時は数学的根拠を明示

### 2. エラー回避戦略
- **分数の符号**: `div_neg` + `neg_div`の組み合わせパターン
- **複合分数**: `field_simp`による直接処理
- **三角恒等式**: 個別操作より`ring`による統一処理
- **証明完了判定**: 各戦術後のgoal状態確認

### 3. 数学的理解の深化
- **符号の代数**: `-(a/b)`と`-a/b`の厳密な区別
- **分数の性質**: 分母の符号処理の順序重要性
- **恒等式の活用**: 直接計算による証明の簡潔性

## 今後の指針

### 1. 証明設計の改善
- 定義展開 → 代数操作 → 恒等式適用の順序
- 各ステップでの明確な数学的説明
- 自動戦術の理由付き使用

### 2. エラー予防
- 型の一致確認（関数vs値）
- 証明進行状況の逐次確認
- パターンマッチングの事前検証

### 3. 教育的価値
- 構成的証明による数学的理解の深化
- エラーからの学習パターンの確立
- 厳密性と実用性のバランス

この構成的証明変換により、`sorry`なしの完全証明を達成し、Lean 4での厳密な数学証明の実践的スキルを獲得できました。