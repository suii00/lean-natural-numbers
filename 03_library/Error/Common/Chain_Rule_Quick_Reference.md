# Chain Rule エラー対処クイックリファレンス

## 🚨 よくあるエラーと即座の解決法

### 型推論エラー
```
❌ failed to synthesize AddCommGroup ℕ
❌ failed to synthesize NontriviallyNormedField ℕ
```
**即座の修正**:
```lean
-- Before
2 * x
-- After  
(2 : ℝ) * x
```

### 関数等価性エラー
```
❌ HasDerivAt ((fun x => x) + fun x => 1) (1 + 0) x
```
**即座の修正**:
```lean
-- Before
HasDerivAt.add (hasDerivAt_id' x) (hasDerivAt_const x 1)
-- After
convert HasDerivAt.add (hasDerivAt_id' x) (hasDerivAt_const x 1) using 1
ring
```

### パターンマッチングエラー
```
❌ tactic 'rewrite' failed, did not find instance
```
**即座の修正**: `deriv_comp` → `HasDerivAt.comp`

## ⚡ 成功パターン（コピペ可能）

### 基本的な連鎖律
```lean
theorem your_chain_rule :
  ∀ x : ℝ, deriv (fun x => outer_func (inner_func x)) x = expected_result := by
  intro x
  have h : HasDerivAt (fun x => outer_func (inner_func x)) expected_result x := by
    -- 内側関数
    have inner : HasDerivAt inner_func inner_derivative x := your_proof_here
    -- 外側関数  
    have outer : HasDerivAt outer_func outer_derivative (inner_func x) := your_proof_here
    -- 連鎖律
    convert HasDerivAt.comp x outer inner using 1
    ring  -- または field_simp
  exact HasDerivAt.deriv h
```

### よく使う内側関数
```lean
-- 恒等関数 (x)
hasDerivAt_id' x

-- 定数倍 (c*x)
(hasDerivAt_id' x).const_mul (c : ℝ)

-- 加法 (x + c)
convert HasDerivAt.add (hasDerivAt_id' x) (hasDerivAt_const x c) using 1
ring
```

### よく使う外側関数
```lean
-- 指数関数 e^u
Real.hasDerivAt_exp u

-- べき乗 u^n
hasDerivAt_pow n u

-- 平方根 √u
Real.hasDerivAt_sqrt (ne_of_gt positive_condition)
```

## 🔧 デバッグ手順

1. **型注釈チェック**
   ```lean
   #check your_expression  -- 型を確認
   ```

2. **段階的テスト**
   ```lean
   have test : HasDerivAt inner_func ... := sorry
   have test2 : HasDerivAt outer_func ... := sorry
   ```

3. **convertデバッグ**
   ```lean
   convert target_expression using 1
   sorry  -- 残ったゴールを確認
   ```

## 📝 チェックリスト

### 実装前
- [ ] 内側・外側関数を明確に特定
- [ ] 各関数の微分値を計算
- [ ] 必要なimportを確認

### エラー遭遇時
- [ ] 数値に型注釈 `(n : ℝ)` があるか？
- [ ] 関数引数に型注釈 `fun x : ℝ =>` があるか？
- [ ] `convert ... using 1` を試したか？
- [ ] `ring`/`field_simp` を試したか？

### 完成前
- [ ] `lake build` が成功するか？
- [ ] 警告メッセージがないか？
- [ ] `sorry` が残っていないか？