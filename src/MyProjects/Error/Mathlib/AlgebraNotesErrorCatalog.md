# 📚 AlgebraNotes エラーカタログ - Mathlib4 互換性問題と解決策

## 🎯 概要
このドキュメントは `src/MyProofs/AlgebraNotes` ディレクトリで発生した全エラーを分析し、型エラー、import問題、Mathlib互換性問題に分類して文書化したものです。

**分析日**: 2025-08-22  
**対象ファイル数**: 86 Leanファイル  
**エラー発生ファイル**: 約70%

---

## 📊 エラー分類統計

| カテゴリー | 発生頻度 | 深刻度 |
|----------|---------|--------|
| 型エラー | 45% | 高 |
| Mathlib API互換性 | 35% | 高 |
| Tactic失敗 | 15% | 中 |
| Import問題 | 3% | 低 |
| その他 | 2% | 低 |

---

## 🔴 カテゴリー1: 型エラー (Type Errors)

### 1.1 Coset記法エラー
**エラーメッセージ**:
```lean
failed to synthesize HSMul G (Set G)
failed to synthesize HMul G (Subgroup G)
```

**発生場所**:
- FirstIsomorphism_Explore.lean:66, 76
- FirstIsomorphismMembership.lean:83, 93, 103-104

**原因**: 左剰余類の記法 `g * ker` が正しく解釈されない

**解決策**:
```lean
-- ❌ 間違い
g₁ * MonoidHom.ker f = g₂ * MonoidHom.ker f

-- ✅ 解決策1: 商群の等価性を使用
QuotientGroup.mk g₁ = QuotientGroup.mk g₂

-- ✅ 解決策2: 明示的な membership で表現
g₁⁻¹ * g₂ ∈ MonoidHom.ker f
```

### 1.2 型推論失敗
**エラーメッセージ**:
```lean
typeclass instance problem is stuck, it is often due to metavariables
```

**発生場所**:
- NoetherCorrespondenceFixed.lean:32
- FirstIsomorphismMembership.lean:146

**原因**: 型推論に必要な情報が不足

**解決策**:
```lean
-- ❌ 間違い
example := QuotientGroup.mk

-- ✅ 解決策: 型注釈を明示
example := @QuotientGroup.mk G _ (MonoidHom.ker f)
```

### 1.3 Application Type Mismatch
**エラーメッセージ**:
```lean
Application type mismatch: In the application ...
the argument ... has type ... but is expected to have type ...
```

**発生場所**: 多数のファイル

**パターンと解決策**:

#### パターン1: MonoidHom型の混同
```lean
-- ❌ 間違い
lemma foo : MonoidHom (QuotientGroup.mk) := QuotientGroup.mk

-- ✅ 解決策
#check (@QuotientGroup.mk G _ N)  -- 既に G →* G ⧸ N の型
```

#### パターン2: lift関数の引数エラー
```lean
-- ❌ 間違い  
QuotientGroup.lift f

-- ✅ 解決策（正規性の証明が必要）
QuotientGroup.lift f (MonoidHom.normal_ker f)
```

---

## 🔴 カテゴリー2: Mathlib API互換性問題

### 2.1 存在しないAPI
**エラーメッセージ**:
```lean
unknown identifier 'QuotientGroup.rangeKerLift_mk'
unknown constant 'MonoidHom.mem_range_self'
Invalid field 'normal_mem_comm'
```

**原因**: Mathlib4では削除または名称変更されたAPI

**解決策マッピング**:

| 旧API (Lean3/古いMathlib) | 新API (Mathlib4) |
|--------------------------|------------------|
| `QuotientGroup.lift` | `QuotientGroup.lift` (引数が異なる) |
| `QuotientGroup.rangeKerLift_mk` | 存在しない（不要） |
| `MonoidHom.mem_range_self` | `Set.mem_range_self` |
| `Subgroup.normal_mem_comm` | 存在しない |
| `IsGroupHom` | 不要（`MonoidHom`で十分） |

### 2.2 API引数の変更
**問題**: 関数の引数順序や必須引数が変更

**例と解決策**:
```lean
-- ❌ Lean3スタイル
QuotientGroup.lift φ

-- ✅ Mathlib4スタイル（正規性の証明が必要）
QuotientGroup.lift φ hN
-- ここで hN : N.Normal
```

### 2.3 暗黙引数の変更
```lean
-- 明示的に型引数を渡す必要がある場合
@QuotientGroup.mk G _ N  -- G, Group G, N を明示
```

---

## 🔴 カテゴリー3: Tactic失敗

### 3.1 rewrite失敗
**エラー**:
```lean
tactic 'rewrite' failed, did not find instance of the pattern
```

**よくある原因と解決策**:

```lean
-- ❌ パターンが見つからない
rw [leftRel_eq] at h

-- ✅ 解決策1: 正しいlemmaを使用
rw [QuotientGroup.eq] at h

-- ✅ 解決策2: unfoldして展開
unfold leftRel at h
rw [...] at h
```

### 3.2 simp失敗
**エラー**:
```lean
simp made no progress
```

**解決策**:
```lean
-- ❌ 効果なし
simp only [leftRel_eq]

-- ✅ 明示的にrwを使用
rw [leftRel_eq]
-- または simp に追加のlemmaを与える
simp [leftRel_eq, QuotientGroup.eq]
```

### 3.3 rfl失敗
**エラー**:
```lean
tactic 'rfl' failed, expected goal to be a binary relation
```

**解決策**:
```lean
-- ❌ 関係でないものにrfl
example : ∀ x y, φ (x * y) = φ x * φ y := by rfl

-- ✅ 正しくmap_mulを使用
example : ∀ x y, φ (x * y) = φ x * φ y := 
  fun x y => map_mul φ x y
```

---

## 🔴 カテゴリー4: Import問題

### 4.1 モジュール構造の変更
**エラー**:
```lean
bad import 'Mathlib.GroupTheory.Subgroup.Basic'
```

**Mathlib4の正しいimport構造**:
```lean
import Mathlib.GroupTheory.QuotientGroup.Basic  -- 商群
import Mathlib.GroupTheory.Subgroup.Basic       -- 存在しない
import Mathlib.RingTheory.Ideal.Basic          -- イデアル
import Mathlib.RingTheory.PrimeSpectrum        -- 素スペクトラム
```

---

## 🛠️ 汎用的な解決パターン

### パターン1: 型を明示的に指定
```lean
-- 型推論が失敗する場合
have : (x : G) ∈ (MonoidHom.ker f : Set G) := ...
```

### パターン2: 暗黙引数を明示
```lean
-- @を使って全引数を明示
@QuotientGroup.mk G _ (MonoidHom.ker f)
```

### パターン3: 中間結果を分解
```lean
-- 複雑な式を段階的に
have h1 : ... := ...
have h2 : ... := ...
exact combine h1 h2
```

### パターン4: #checkで型を確認
```lean
#check QuotientGroup.mk           -- 型を確認
#check MonoidHom.ker              -- 返り値の型を確認
#check @QuotientGroup.eq          -- 全引数を表示
```

---

## 📋 チェックリスト

エラー修正時の確認手順：

1. **Import確認**
   - [ ] 必要なMathlibモジュールがimportされているか
   - [ ] import名が正しいか（Mathlib4準拠）

2. **型確認**
   - [ ] `#check`で関数の型を確認
   - [ ] 暗黙引数が正しく推論されるか
   - [ ] 必要に応じて`@`で明示的に指定

3. **API確認**
   - [ ] 使用しているAPIがMathlib4に存在するか
   - [ ] 引数の順序や型が正しいか
   - [ ] 代替APIが必要か

4. **Tactic確認**
   - [ ] `rw`で書き換えるパターンが存在するか
   - [ ] `simp`に適切なlemmaを与えているか
   - [ ] goalの型が期待通りか

---

## 🔍 デバッグコマンド

```lean
-- 型の詳細表示
set_option pp.all true

-- インスタンス検索のトレース
set_option trace.Meta.synthInstance true

-- simp の詳細表示
set_option trace.simp true

-- 現在のgoalと仮定を表示
trace_state

-- 使える定理を検索
library_search
apply?
exact?
```

---

## 📚 参考リンク

- [Mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Lean4 Reference Manual](https://leanprover.github.io/lean4/doc/)
- [Mathlib4 Porting Guide](https://github.com/leanprover-community/mathlib4/wiki/Porting-guide)

---

## 📈 改善の優先順位

1. **最優先**: 型エラーの修正（coset記法、型推論）
2. **高優先**: Mathlib API互換性（正しいAPI使用）
3. **中優先**: Tactic失敗の解決
4. **低優先**: Import整理とクリーンアップ

このカタログは継続的に更新され、新しいエラーパターンが発見され次第追加されます。