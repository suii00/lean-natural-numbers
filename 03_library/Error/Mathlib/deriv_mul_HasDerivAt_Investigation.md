# deriv_mul と HasDerivAt API 調査結果 (2025-01-29)

## 1. deriv_mul の正確な仕様

### シグネチャ
```lean
theorem deriv_mul 
  {𝕜 : Type u} [NontriviallyNormedField 𝕜] 
  {x : 𝕜} 
  {𝔸 : Type u_3} [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸] 
  {c d : 𝕜 → 𝔸} 
  (hc : DifferentiableAt 𝕜 c x) 
  (hd : DifferentiableAt 𝕜 d x) :
  deriv (c * d) x = deriv c x * d x + c x * deriv d x
```

### 重要な点
- `c * d` は**関数の積**（Pointwise multiplication）
- `(c * d) x = c x * d x` という意味
- 引数は `DifferentiableAt` の証明が必要

## 2. なぜ deriv_mul が失敗するか

### 問題の本質
```lean
-- これは失敗する
theorem x_exp_fail : ∀ x : ℝ, 
  deriv (fun x => x * Real.exp x) x = (x + 1) * Real.exp x := by
  intro x
  rw [deriv_mul differentiableAt_id Real.differentiableAt_exp]
  -- エラー: パターンマッチング失敗
```

**原因**: Lean が `(fun x => x * Real.exp x)` を `id * Real.exp` の形として認識できない

### パターンマッチングの問題
- `deriv_mul` は `deriv (f * g) x` の形を期待
- しかし `(fun x => x * Real.exp x)` は単一のラムダ式
- 関数の積 `(fun x => x) * Real.exp` として分解する必要がある

## 3. 解決策

### 方法1: 関数を明示的に分解
```lean
theorem x_exp_deriv_correct : ∀ x : ℝ,
  deriv (fun x => x * Real.exp x) x = (x + 1) * Real.exp x := by
  intro x
  -- 関数を2つの関数の積として定義
  let f := fun y : ℝ => y
  let g := Real.exp
  have h_eq : (fun x => x * Real.exp x) = f * g := by
    ext y; rfl
  rw [h_eq]
  -- ここで deriv_mul が適用可能
  rw [deriv_mul (differentiableAt_id) (Real.differentiableAt_exp)]
  simp [f, g, deriv_id'', Real.deriv_exp]
  ring
```

### 方法2: HasDerivAt を使用（推奨）
```lean
theorem x_exp_deriv_hasDerivAt : ∀ x : ℝ,
  deriv (fun x => x * Real.exp x) x = (x + 1) * Real.exp x := by
  intro x
  have h1 : HasDerivAt (fun x => x) 1 x := hasDerivAt_id' x  -- 注: x を明示的に適用
  have h2 : HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp x
  have h_prod : HasDerivAt (fun x => x * Real.exp x) 
                          (1 * Real.exp x + x * Real.exp x) x := 
    HasDerivAt.mul h1 h2
  convert HasDerivAt.deriv h_prod using 1
  ring
```

## 4. HasDerivAt の利点

### 定義
```lean
def HasDerivAt {𝕜 F} (f : 𝕜 → F) (f' : F) (x : 𝕜) : Prop
```

### 特徴
1. **点ごとの微分**: 特定の点 `x` での微分を表現
2. **値の明示**: 微分値 `f'` を明示的に指定
3. **柔軟な証明**: 複雑な関数でも段階的に構築可能

### deriv との関係
- `HasDerivAt f f' x` ⟹ `deriv f x = f'`
- `HasDerivAt.deriv` で変換可能

## 5. API 使用上の注意点

### hasDerivAt_id' の罠
```lean
-- 誤り
have h : HasDerivAt (fun x => x) 1 x := hasDerivAt_id'
-- エラー: 型の不一致

-- 正しい
have h : HasDerivAt (fun x => x) 1 x := hasDerivAt_id' x
-- または
have h : HasDerivAt (fun x => x) 1 x := hasDerivAt_id'
```

### differentiableAt_const の使用
```lean
-- 定数関数の微分可能性
have : DifferentiableAt ℝ (fun _ => (3 : ℝ)) x := differentiableAt_const
```

## 6. 推奨アプローチ

### 単純な場合
- 基本的な関数: `rw [定理名]` で直接適用
- 例: `rw [Real.deriv_exp]`, `rw [deriv_id'']`

### 複雑な場合
1. **HasDerivAt を優先**: より確実で柔軟
2. **段階的構築**: 各部分の微分を個別に証明
3. **最後に deriv に変換**: `HasDerivAt.deriv` を使用

### deriv_mul を使いたい場合
1. 関数を明示的に `f * g` の形に分解
2. `ext` タクティックで等価性を証明
3. その後 `deriv_mul` を適用

## 7. まとめ

**deriv_mul の難しさ**:
- パターンマッチングが厳密
- 関数の積の形を明示的に認識させる必要がある
- ラムダ式の直接適用は困難

**HasDerivAt の優位性**:
- より柔軟で確実
- 段階的な証明構築が可能
- 複雑な関数でも対応しやすい

**実用的な推奨**:
- 簡単な場合: 直接 `rw` を使用
- 積・合成関数: `HasDerivAt` レベルで作業
- 最終的に `deriv` に変換