# Chain Rule deriv_comp Investigation Errors - 2025-08-26

## Session Overview
**Task**: Investigate using provided `deriv_comp` theorems for Stable Mode chain rule implementations
**Date**: 2025-08-26
**Mode**: stable (連鎖律マスター)
**File**: `TrigonometricChainRuleFixed.lean`

## Error Categories

### 1. Function.comp_apply Pattern Matching Errors

**Error**:
```
error: tactic 'rewrite' failed, did not find instance of the pattern in the target expression
  Real.sin (2 * ?m.1198)
x : ℝ
⊢ deriv (fun x => Real.sin (2 * x)) x = 2 * Real.cos (2 * x)
```

**Context**: Attempting to replace `deriv.scomp` with direct `deriv_comp` application
**Root Cause**: `Function.comp_apply` rewrite pattern doesn't match lambda expressions
**Files Affected**: 
- `TrigonometricChainRuleFixed.lean:32`
- `TrigonometricChainRuleFixed.lean:41`  
- `TrigonometricChainRuleFixed.lean:50`

### 2. Unknown Constant Errors

**Error**:
```
error: unknown constant 'differentiableAt_const.mul'
```

**Context**: Trying to use outdated mathlib API patterns
**Root Cause**: API evolution - `differentiableAt_const.mul` doesn't exist in current mathlib
**Files Affected**: 
- `TrigonometricChainRuleFixed.lean:80`
- `TrigonometricSimplified.lean:21, 32, 53`
- `TrigonometricDirect.lean:17`

### 3. Deprecated API Warnings

**Warning**:
```
warning: `differentiableAt_id'` has been deprecated: use `differentiableAt_fun_id` instead
```

**Context**: Using outdated function identity differentiability
**Impact**: Code works but generates warnings
**Files Affected**: `TrigonometricChainRuleFixed.lean:97`

### 4. Type Synthesis Failures

**Error**:
```
error: failed to synthesize NontriviallyNormedField 𝕜'
```

**Context**: Attempting to define generic `deriv_comp` theorem without proper type constraints
**Root Cause**: Missing field type specifications in custom theorem definition
**Files Affected**: `TrigonometricDirect.lean:13`

### 5. Simp No Progress Errors

**Error**:
```
error: simp made no progress
```

**Context**: Using `simp only [Function.comp_apply]` as suggested fix
**Root Cause**: Pattern doesn't apply to the current goal structure
**Files Affected**: 
- `TrigonometricDirect.lean:32, 41, 79, 97`

## Attempted Solutions and Results

### ❌ Failed Approach 1: Direct deriv_comp Replacement
```lean
-- FAILED: 直接置換
rw [deriv_comp Real.differentiableAt_sin (differentiableAt_const.mul differentiableAt_id')]
-- Error: unknown constant 'differentiableAt_const.mul'
```

### ❌ Failed Approach 2: Function.comp_apply Pattern
```lean
-- FAILED: パターンマッチング
rw [← Function.comp_apply (f := Real.sin) (g := fun x => 2 * x)]
rw [deriv_comp ...]
-- Error: tactic 'rewrite' failed, did not find instance of the pattern
```

### ❌ Failed Approach 3: simp only Workaround
```lean
-- FAILED: simp回避策
simp only [Function.comp_apply]
rw [deriv.comp ...]
-- Error: simp made no progress
```

### ✅ Working Solution: Existing deriv.scomp Pattern
```lean
-- SUCCESS: 既存パターン
rw [← Function.comp_apply (f := Real.sin) (g := fun x => 2 * x)]
rw [deriv.scomp]
-- Works perfectly in TrigonometricChainRule.lean
```

## Key Findings

### API Compatibility Issues
1. **`deriv_comp` vs `deriv.scomp`**: 提供された定理の型シグニチャが現環境と不一致
2. **differentiableAt API**: 
   - ❌ `differentiableAt_const.mul` が存在しない（dot notation error）
   - ✅ **正解1**: `differentiableAt_const` は存在（引数 `c : F` 必要）
   - ✅ **正解2**: `DifferentiableAt.const_mul` も存在  
   - 🔧 **修正**: dot記法の混同が問題の原因
3. **Deprecated Functions**: `differentiableAt_id'` → `differentiableAt_fun_id`

### Pattern Matching Limitations
1. **Lambda vs Composition**: `fun x => f(g(x))`から`f ∘ g`への変換が困難
2. **Rewrite Failures**: Function composition パターンマッチングの制限
3. **Type Inference**: 自動型推論がFunction.comp表記で失敗

## Recommendations

### 🎯 For Stable Mode Implementation
**Keep using existing `deriv.scomp` pattern**:
```lean
rw [← Function.comp_apply (f := Real.sin) (g := fun x => 2 * x)]
rw [deriv.scomp]
```

### 🛠️ For Future API Migration
1. Monitor mathlib updates for `deriv_comp` integration improvements
2. Track `differentiableAt_const.mul` equivalent API
3. Update to `differentiableAt_fun_id` from `differentiableAt_id'`

### 📚 Educational Value
- **Theoretical Understanding**: 提供された定理は連鎖律の数学的理解に有用
- **Practical Implementation**: 現実的には既存パターンが最適
- **Error Prevention**: API進化追跡の重要性を実証

## CRITICAL DISCOVERY: Correct API Pattern Found

### ✅ 正しいAPI使用法
```lean
-- ❌ 間違い: differentiableAt_const.mul
-- ✅ 正解: DifferentiableAt.const_mul
exact DifferentiableAt.const_mul differentiableAt_fun_id a
exact differentiableAt_const b
```

**確認済み動作例**: `StableModeTest.lean:29-30`

### 🔄 修正版deriv_comp実装試行結果

**発見された事実**:
- ✅ `differentiableAt_const (c : F)` は存在（**公式docs完全確認済み**）
- ✅ **正式型シグニチャ**: `@[simp] theorem differentiableAt_const {𝕜} [NontriviallyNormedField 𝕜] {E F} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {x : E} (c : F) : DifferentiableAt 𝕜 (fun (x : E) => c) x`
- ✅ `DifferentiableAt.const_mul` は存在
- ❌ **しかし**: `deriv_comp`のパターンマッチングが依然として失敗

**残存エラー**:
```
error: tactic 'rewrite' failed, did not find instance of the pattern in the target expression
  deriv (?m.545 ∘ ?m.544) ?m.540
```

**根本原因判明**: `deriv_comp`は`h₂ ∘ h`の形式を要求するが、
`Real.sin ∘ (fun y => 2 * y)`がパターンマッチしない

**最終結論**: APIは正しいが、**パターンマッチング制約**により`deriv.scomp`が実用的

## Error Prevention Guidelines

1. **Check existing working implementations for API patterns**
2. **Verify exact API names - dot notation matters** (`DifferentiableAt.const_mul` not `differentiableAt_const.mul`)
3. **Test incremental changes rather than wholesale replacements**
4. **Document both successful and failed approaches for future reference**
5. **🆕 Always grep for successful usage patterns in codebase before assuming API doesn't exist**

---
**Generated**: 2025-08-26  
**Session**: Chain Rule deriv_comp Investigation  
**Status**: 既存deriv.scopパターン継続推奨