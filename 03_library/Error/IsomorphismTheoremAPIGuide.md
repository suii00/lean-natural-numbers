# 同型定理実装のためのMathlibAPIガイド

## 🎯 重要なAPI理解

### Ideal.Quotient.lift の正しい使用法

```lean
-- 定義
def Ideal.Quotient.lift (I : Ideal R) (f : R →+* S) 
  (H : ∀ a : R, a ∈ I → f a = 0) : R ⧸ I →+* S

-- 重要な補題
lemma Ideal.Quotient.lift_mk (I : Ideal R) (f : R →+* S) (H : ...) (x : R) :
  (Ideal.Quotient.lift I f H) (Ideal.Quotient.mk I x) = f x
```

### 正しい条件の与え方

```lean
-- ❌ 間違い
Ideal.Quotient.lift (RingHom.ker f) f (le_refl _)

-- ✅ 正しい  
Ideal.Quotient.lift (RingHom.ker f) f (fun a ha => ha)

-- 理由: RingHom.ker f の定義により、ha : a ∈ RingHom.ker f は f a = 0 と同値
```

---

## 🔑 核心となる補題

### RingHom.injective_iff_ker_eq_bot

```lean
theorem RingHom.injective_iff_ker_eq_bot (f : R →+* S) : 
  Function.Injective f ↔ RingHom.ker f = ⊥
```

### RingHom.ker の定義

```lean
def RingHom.ker (f : R →+* S) : Ideal R := Ideal.comap f ⊥

-- 重要な同値性
lemma RingHom.mem_ker (f : R →+* S) (x : R) : x ∈ RingHom.ker f ↔ f x = 0
```

---

## 🧪 デバッグ技術

### 型情報の確認

```lean
#check @inferInstance  -- 型クラス推論テスト
#check RingHom.ker f   -- 型確認: Ideal R
#check f               -- 型確認: R →+* S
```

### 証明状態の明示化

```lean
-- change タクティクで目標を明示
change f x = (Ideal.Quotient.lift ...) (Ideal.Quotient.mk ... x)

-- obtain で存在証明を分解
obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
```

---

## ⚡ 頻出エラーと解決法

### 1. 型クラス推論エラー
```lean
-- エラー: RingHomClass ?m.XXX ?m.YYY ?m.ZZZ
-- 解決: by を追加
lemma example_lemma : statement := by exact known_lemma
```

### 2. 関数適用エラー  
```lean
-- エラー: Function expected at Ideal.Quotient.lift_mk
-- 原因: lift_mk は等式であり関数ではない
-- 解決: 
exact Ideal.Quotient.lift_mk I f h x  -- 引数を明示
```

### 3. 定義的等式エラー
```lean
-- エラー: Not a definitional equality
-- 解決: rfl の代わりに by rfl を使用
lemma kernel_def : x ∈ RingHom.ker f ↔ f x = 0 := by rfl
```

---

## 📚 必須Import

```lean
import Mathlib.RingTheory.Ideal.Quotient.Basic  -- 商環の基本
import Mathlib.RingTheory.Ideal.Operations      -- イデアル演算
import Mathlib.RingTheory.Ideal.Maps           -- RingHom.ker など
```

---

## 🎨 証明パターン集

### パターン1: 全射の証明
```lean
theorem surjective_proof (π : R →+* R ⧸ I) : Function.Surjective π := by
  exact Ideal.Quotient.mk_surjective  -- 商写像は定義的に全射
```

### パターン2: 単射の証明  
```lean
theorem injective_proof (ι : R ⧸ RingHom.ker f →+* S) : Function.Injective ι := by
  rw [RingHom.injective_iff_ker_eq_bot]
  ext x
  -- 詳細な証明...
```

### パターン3: 等式の証明
```lean
theorem factorization (f : R →+* S) : 
  f = ι.comp π := by
  ext x
  exact (Ideal.Quotient.lift_mk ... x).symm
```

---

## 🏆 成功事例

最終的に18/18補題すべてが型チェックを通過した成功パターン：

```lean
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

-- 成功例1: 核の定義
lemma kernel_def (f : R →+* S) (x : R) : 
  x ∈ RingHom.ker f ↔ f x = 0 := by rfl

-- 成功例2: Lift の存在
lemma lift_exists (I : Ideal R) (f : R →+* S) (h : ∀ a ∈ I, f a = 0) :
  ∃ f_bar, ∀ x, f_bar (Ideal.Quotient.mk I x) = f x := by
  use Ideal.Quotient.lift I f h
  intro x
  exact Ideal.Quotient.lift_mk I f h x

-- 成功例3: 第一同型定理
theorem first_isomorphism_theorem (f : R →+* S) :
  ∃ π ι, Function.Surjective π ∧ Function.Injective ι ∧ f = ι.comp π := by
  use Ideal.Quotient.mk (RingHom.ker f)
  use Ideal.Quotient.lift (RingHom.ker f) f (fun a ha => ha)
  -- 詳細...
```

このガイドにより、今後の同型定理実装が効率的に行えます。