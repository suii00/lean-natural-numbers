# 🔧 Mathlib4 エラー解決パターン集

## 即効性のある解決パターン（コピペ用）

### 🎯 パターン1: 商群の基本操作

#### エラー: `failed to synthesize HSMul G (Set G)`
```lean
-- ❌ エラーが出るコード
lemma bad_coset (g₁ g₂ : G) (f : G →* H) :
  g₁ * MonoidHom.ker f = g₂ * MonoidHom.ker f → ... := sorry

-- ✅ 修正版1: QuotientGroup.mkを使用
lemma good_quotient (g₁ g₂ : G) (f : G →* H) :
  QuotientGroup.mk g₁ = QuotientGroup.mk g₂ → ... := by
  intro h_eq
  rw [QuotientGroup.eq] at h_eq
  -- h_eq : g₁⁻¹ * g₂ ∈ MonoidHom.ker f
  sorry

-- ✅ 修正版2: 直接membershipで表現
lemma good_membership (g₁ g₂ : G) (f : G →* H) :
  g₁⁻¹ * g₂ ∈ MonoidHom.ker f → f g₁ = f g₂ := by
  intro h_mem
  rw [MonoidHom.mem_ker] at h_mem
  rw [map_mul, map_inv] at h_mem
  exact inv_mul_eq_one.mp h_mem
```

---

### 🎯 パターン2: QuotientGroup API の正しい使用

#### エラー: `unknown identifier 'QuotientGroup.lift'`
```lean
-- ❌ エラーが出るコード（引数不足）
def bad_lift {G H : Type*} [Group G] [Group H] (f : G →* H) :=
  QuotientGroup.lift f

-- ✅ 修正版: 正規性の証明を追加
def good_lift {G H : Type*} [Group G] [Group H] (f : G →* H) :
    G ⧸ MonoidHom.ker f →* H :=
  QuotientGroup.lift f (MonoidHom.normal_ker f)

-- ✅ より簡潔: rangeKerLiftを直接使用
def best_lift {G H : Type*} [Group G] [Group H] (f : G →* H) :
    G ⧸ MonoidHom.ker f →* f.range :=
  QuotientGroup.rangeKerLift f
```

---

### 🎯 パターン3: 型推論の補助

#### エラー: `typeclass instance problem is stuck`
```lean
-- ❌ エラーが出るコード（型推論失敗）
example {G : Type*} [Group G] (N : Subgroup G) [N.Normal] :=
  QuotientGroup.mk

-- ✅ 修正版: 型を明示
example {G : Type*} [Group G] (N : Subgroup G) [N.Normal] :
    G →* G ⧸ N :=
  @QuotientGroup.mk G _ N

-- ✅ さらに明確に
example {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (g : G) :
    G ⧸ N :=
  (QuotientGroup.mk : G → G ⧸ N) g
```

---

### 🎯 パターン4: MonoidHom の取り扱い

#### エラー: `Application type mismatch with MonoidHom`
```lean
-- ❌ エラーが出るコード
lemma bad_hom_usage (f : G →* H) :
  MonoidHom (QuotientGroup.mk) := QuotientGroup.mk

-- ✅ 修正版: MonoidHomは型、値ではない
lemma good_hom_usage {G H : Type*} [Group G] [Group H] (f : G →* H) :
  ∀ x y : G, QuotientGroup.mk (x * y) = 
            QuotientGroup.mk x * QuotientGroup.mk y :=
  fun x y => map_mul QuotientGroup.mk x y

-- MonoidHomであることの確認は型で表現済み
#check (QuotientGroup.mk : G →* G ⧸ N)  -- →* がMonoidHom
```

---

### 🎯 パターン5: 第一同型定理の完全実装

```lean
import Mathlib.GroupTheory.QuotientGroup.Basic

-- ✅ 動作確認済みの完全実装
namespace FirstIsomorphism

variable {G H : Type*} [Group G] [Group H]

-- 核の正規性
lemma ker_normal (f : G →* H) : (MonoidHom.ker f).Normal :=
  MonoidHom.normal_ker f

-- 誘導写像の定義
def induced_map (f : G →* H) : G ⧸ MonoidHom.ker f →* f.range :=
  QuotientGroup.rangeKerLift f

-- 単射性
lemma induced_injective (f : G →* H) : 
  Function.Injective (induced_map f) :=
  QuotientGroup.rangeKerLift_injective f

-- 全射性
lemma induced_surjective (f : G →* H) :
  Function.Surjective (induced_map f) :=
  QuotientGroup.rangeKerLift_surjective f

-- 第一同型定理
theorem first_isomorphism (f : G →* H) :
  Nonempty (G ⧸ MonoidHom.ker f ≃* f.range) :=
  ⟨QuotientGroup.quotientKerEquivRange f⟩

end FirstIsomorphism
```

---

### 🎯 パターン6: Range/Image の扱い

#### エラー: `unknown constant 'MonoidHom.mem_range_self'`
```lean
-- ❌ エラーが出るコード
lemma bad_range (f : G →* H) (g : G) :
  f g ∈ f.range := MonoidHom.mem_range_self g

-- ✅ 修正版: Set.mem_range_selfまたは明示的証明
lemma good_range (f : G →* H) (g : G) :
  f g ∈ f.range := by
  rw [MonoidHom.mem_range]
  exact ⟨g, rfl⟩

-- ✅ Subtype構成
example (f : G →* H) (g : G) : f.range :=
  ⟨f g, by simp [MonoidHom.mem_range]⟩
```

---

### 🎯 パターン7: Tactic失敗の回避

#### エラー: `simp made no progress`
```lean
-- ❌ エラーが出るコード
example : ... := by
  simp only [leftRel_eq]

-- ✅ 修正版1: rwを使用
example : ... := by
  rw [leftRel_eq]

-- ✅ 修正版2: simpに追加情報
example : ... := by
  simp [leftRel_eq, QuotientGroup.eq]
```

#### エラー: `rfl failed`
```lean
-- ❌ エラーが出るコード
lemma bad_rfl : φ (x * y) = φ x * φ y := by rfl

-- ✅ 修正版: map_mulを使用
lemma good_map : φ (x * y) = φ x * φ y :=
  map_mul φ x y
```

---

## 🚀 クイックフィックス・チートシート

### Import修正
```lean
-- 基本的なimport（ほぼ必須）
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.GroupAction.Basic  -- 群作用が必要な場合
import Mathlib.RingTheory.Ideal.Basic         -- イデアル
import Mathlib.RingTheory.PrimeSpectrum       -- 素スペクトラム
```

### 型確認コマンド
```lean
-- デバッグ時に有用
#check QuotientGroup.mk
#check MonoidHom.ker
#check @QuotientGroup.eq
#check QuotientGroup.rangeKerLift

-- 型を詳細表示
set_option pp.all true in
#check QuotientGroup.mk
```

### よく使うMathlib定理
```lean
-- 商群関連
QuotientGroup.eq              -- 商群での等価条件
QuotientGroup.mk              -- 自然な射影
QuotientGroup.rangeKerLift   -- 第一同型定理の核心
QuotientGroup.quotientKerEquivRange  -- 群同型

-- MonoidHom関連
MonoidHom.normal_ker          -- 核の正規性
MonoidHom.mem_ker            -- 核のmembership条件
map_mul                      -- 準同型の乗法保存
map_inv                      -- 準同型の逆元保存
```

---

## 📝 トラブルシューティング・フローチャート

```
エラー発生
    ↓
1. Import確認 → 不足なら追加
    ↓
2. #check で型確認 → 型が違うなら型注釈追加
    ↓
3. API存在確認 → 存在しないなら代替API使用
    ↓
4. 引数確認 → 不足なら追加（特に正規性の証明）
    ↓
5. Tactic変更 → simp → rw → unfold → 手動証明
```

---

## 🎓 学習リソース

1. **Mathlib4 Docs**: 最新APIリファレンス
2. **#check**: 型確認の基本ツール
3. **library_search**: 使える定理の検索
4. **apply?/exact?**: 候補の提示

---

## ⚡ 最重要: これだけ覚えれば80%解決

1. **商群は`QuotientGroup.mk`を使う**（剰余類記法は避ける）
2. **`QuotientGroup.rangeKerLift`が第一同型定理の核心**
3. **型推論失敗なら`@`で明示的に指定**
4. **`simp`が効かなければ`rw`を使う**
5. **MonoidHom.ker は Subgroup を返す**（Set ではない）

このパターン集を手元に置いて、エラーが出たら該当パターンを探してコピペ修正することで、多くの問題を素早く解決できます。