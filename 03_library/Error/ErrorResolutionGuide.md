# 🔧 エラー解決ガイド

## 📋 クイックリファレンス

### 🚨 よくあるエラーと即座の対処法

| エラーメッセージ | 原因 | 解決法 |
|-----------------|------|--------|
| `failed to synthesize Mul (R ⧸ ...)` | Ring vs CommRing | `[CommRing R]` に変更 |
| `bad import 'Mathlib.RingTheory.Ideal.Quotient'` | 古いインポート | 細分化されたモジュール使用 |
| `unknown constant 'RingHom.quotientKerEquivRange_apply_mk'` | 存在しないAPI | mathlibドキュメント確認 |
| `type mismatch ...→+*...` | 関数合成エラー | `.comp` を使用 |
| `typeclass instance problem is stuck` | メタ変数問題 | 明示的型注釈 |

---

## 🎯 段階的エラー解決手順

### Step 1: エラーの分類
1. **コンパイルエラー** vs **型エラー** vs **証明エラー**
2. **Import問題** vs **定義問題** vs **使用問題**

### Step 2: 基本チェックリスト
- [ ] 正しいインポートを使用しているか？
- [ ] `CommRing` vs `Ring` の選択は適切か？
- [ ] mathlibの最新APIを使用しているか？
- [ ] 型注釈は十分か？

### Step 3: デバッグテクニック
```lean
-- 型の確認
#check RingHom.quotientKerEquivRange
#check Ideal.Quotient.mk

-- インスタンスの確認
example : Ring (R ⧸ I) := by infer_instance

-- 型情報の表示
set_option diagnostics true
```

---

## 📚 エラー別解決事例

### 1. Import/Module エラー

#### 問題
```lean
import Mathlib.RingTheory.Ideal.Quotient
-- エラー: bad import
```

#### 解決
```lean
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
```

#### 理由
Mathlib 4では理想の商環関連のモジュールが細分化された。

---

### 2. 型合成エラー

#### 問題
```lean
variable {R S : Type*} [Ring R] [Ring S]
def quotient_type := R ⧸ RingHom.ker f  -- エラー: Mul (R ⧸ ...)
```

#### 解決
```lean
variable {R S : Type*} [CommRing R] [CommRing S]
def quotient_type := R ⧸ RingHom.ker f  -- 成功
```

#### 理由
多くのmathlib APIは可換環を前提としている。

---

### 3. API互換性エラー

#### 問題
```lean
simp [RingHom.quotientKerEquivRange_apply_mk]
-- エラー: unknown constant
```

#### 解決
```lean
-- 直接的な定義の使用
simp [RingHom.quotientKerEquivRange]
-- または
rfl  -- 多くの場合、定義により成り立つ
```

#### 理由
APIの詳細な補題は公開されていない場合がある。

---

### 4. 型不一致エラー

#### 問題
```lean
def bad_comp : R →+* S := 
  f₃ ∘ f₂ ∘ f₁  -- エラー: type mismatch
```

#### 解決
```lean
def good_comp : R →+* S := 
  f₃.comp (f₂.comp f₁)  -- 成功
```

#### 理由
環準同型の合成には専用の `.comp` を使用する必要がある。

---

### 5. 証明タクティックエラー

#### 問題
```lean
theorem bad_proof : φ₁ = φ₂ := by
  rfl  -- エラー: not definitionally equal
```

#### 解決
```lean
theorem good_proof : φ₁ = φ₂ := by
  ext x
  simp [φ₁, φ₂]
  rfl
```

#### 理由
定義の展開と適切な拡張性補題が必要。

---

## 🛠️ 予防策

### 開発時のベストプラクティス

1. **段階的実装**
   ```lean
   -- まず簡単なケースから
   theorem simple_case : Nonempty (...) := ⟨...⟩
   -- 次に詳細な性質
   theorem detailed_properties : ... := by ...
   ```

2. **型の明示**
   ```lean
   -- 型を明示的に記述
   def iso : R ⧸ RingHom.ker f ≃+* f.range := RingHom.quotientKerEquivRange f
   ```

3. **定期的なビルドチェック**
   ```bash
   lake build  # 全体チェック
   lake build Module.Name  # 特定モジュール
   ```

### コードレビューチェックポイント

- [ ] すべてのインポートが正しいか
- [ ] `CommRing` vs `Ring` の選択が適切か
- [ ] カスタム定義が本当に必要か（mathlibに存在しないか）
- [ ] エラーメッセージが理解しやすいか
- [ ] 証明が過度に複雑でないか

---

## 🔍 リソース

### 有用なmathlib検索コマンド
```lean
#check RingHom.quotientKerEquivRange
#check Ideal.Quotient.mk
#check RingHom.ker
```

### mathlibドキュメント
- [Ring Theory Documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory.html)
- [Ideal Quotient Documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Quotient.html)

### デバッグオプション
```lean
set_option diagnostics true  -- 詳細な診断情報
set_option trace.Meta.synthInstance true  -- インスタンス解決の詳細
```

---

*このガイドは実際のエラー経験に基づいて作成され、継続的に更新されます*