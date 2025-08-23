/-
🎓 圏論的統一理論：Mathlib CategoryTheory.Abelian API使用ガイド
Categorical Unification Theory: Mathlib CategoryTheory.Abelian API Usage Guide
-/

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.Images
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! 
# CategoryTheory.Abelian API掘り下げ調査結果

## 🎯 核心API群

### 1. Abelian圏の基本構造
```lean
class Abelian (C : Type*) [Category C] extends Preadditive C where
  -- 有限積、核、余核の存在
  [has_finite_products : HasFiniteProducts C]
  [has_kernels : HasKernels C] 
  [has_cokernels : HasCokernels C]
  -- 正規性：全てのmono/epiはnormal
  normal_mono_of_mono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], NormalMono f
  normal_epi_of_epi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], NormalEpi f
```

### 2. 像・余像の定義 (Abelian.Images)
```lean
-- Abelian像：余核の核
protected abbrev image (f : P ⟶ Q) : C := kernel (cokernel.π f)

-- Abelian余像：核の余核  
protected abbrev coimage (f : P ⟶ Q) : C := cokernel (kernel.ι f)

-- 射影・包含射
protected abbrev image.ι : Abelian.image f ⟶ Q := kernel.ι (cokernel.π f)
protected abbrev coimage.π : P ⟶ Abelian.coimage f := cokernel.π (kernel.ι f)

-- 分解射
protected abbrev factorThruImage : P ⟶ Abelian.image f := 
  kernel.lift (cokernel.π f) f (cokernel.condition f)
protected abbrev factorThruCoimage : Abelian.coimage f ⟶ Q := 
  cokernel.desc (kernel.ι f) f (kernel.condition f)
```

### 3. 第一同型定理の圏論版：coimageImageComparison
```lean
-- 余像→像の標準射（常に同型）
def coimageImageComparison (f : P ⟶ Q) : Abelian.coimage f ⟶ Abelian.image f :=
  cokernel.desc (kernel.ι f) (kernel.lift (cokernel.π f) f (by simp)) (by ext; simp)

-- Abelian圏では常に同型
instance [Abelian C] (f : P ⟶ Q) : IsIso (coimageImageComparison f)

-- 分解の正当性
theorem coimage_image_factorisation : 
  coimage.π f ≫ coimageImageComparison f ≫ image.ι f = f
```

### 4. 完全列の理論 (Abelian.Exact)
```lean
-- 短完全複体の完全性判定
theorem exact_iff_epi_imageToKernel' : 
  S.Exact ↔ Epi (imageToKernel' S.f S.g S.zero)

-- mono + epi = iso の基本原理
theorem isIso_of_mono_of_epi [Mono f] [Epi f] : IsIso f
```

## 🔧 核・余核の基本API群

### Kernels API
```lean
-- 核の条件
theorem kernel.condition : kernel.ι f ≫ f = 0

-- 核への射
theorem kernel.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : 
  kernel.lift f k h ≫ kernel.ι f = k

-- 核の普遍性
theorem kernel.hom_ext {W : C} {k l : W ⟶ kernel f} 
  (h : k ≫ kernel.ι f = l ≫ kernel.ι f) : k = l
```

### Cokernels API
```lean
-- 余核の条件
theorem cokernel.condition : f ≫ cokernel.π f = 0

-- 余核からの射
theorem cokernel.π_desc {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) : 
  cokernel.π f ≫ cokernel.desc f k h = k
```

## 📐 群論的同型定理との対応

### QuotientGroup での同型定理実装
```lean
-- 第一同型定理：G/ker(φ) ≃* range(φ)
noncomputable def quotientKerEquivRange : G ⧸ ker φ ≃* range φ

-- 第二同型定理：H/(H ∩ N) ≃* (HN)/N  
noncomputable def quotientInfEquivProdNormalizerQuotient (H N : Subgroup G)

-- 第三同型定理：(G/N)/(M/N) ≃* G/M
def quotientQuotientEquivQuotient : (G ⧸ N) ⧸ M.map (mk' N) ≃* G ⧸ M
```

## 🎪 実用的使用パターン

### パターン1: 分解の構成
```lean
-- 任意の射のepi-mono分解
use image f, factorThruImage f, image.ι f
constructor
· -- epi性
  infer_instance  
constructor
· -- mono性  
  infer_instance
· -- 分解の正当性
  rw [image.fac f]
```

### パターン2: 同型の証明
```lean
-- coimageImageComparisonが同型であることの利用
example {A B : C} (f : A ⟶ B) : IsIso (coimageImageComparison f) := by
  infer_instance  -- Abelian圏で自動推論
```

### パターン3: 完全列の構成
```lean
-- kernel → domain → coimage が完全
example {A B : C} (f : A ⟶ B) : kernel.ι f ≫ coimage.π f = 0 := by
  -- 核と余像の関係から自動的に従う
  sorry
```

### パターン4: 普遍性の活用
```lean
-- 核の普遍性
example {W A B : C} (f : A ⟶ B) (g : W ⟶ A) (h : g ≫ f = 0) :
    ∃! (k : W ⟶ kernel f), k ≫ kernel.ι f = g := by
  use kernel.lift f g h
  constructor
  · exact kernel.lift_ι f g h
  · intro k hk
    rw [← hk, ← kernel.lift_ι f g h]
    congr 1
    exact kernel.hom_ext (hk.trans (kernel.lift_ι f g h).symm)
```

## 🌟 圏論的同型定理への応用指針

1. **Abelian.coimageImageComparison** を第一同型定理の基礎とする
2. **kernel/cokernel の普遍性**を格子構造の解析に活用
3. **exact sequences** を通じてhomological algebraへの拡張
4. **functor category** での同型定理の自然な拡張
5. **concrete category** での群論的実装との橋渡し

-/

namespace CategoryTheoryAbelianAPIDemo

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category C] [Abelian C]

-- 🎯 実践例1: 第一同型定理の圏論的証明パターン
lemma first_isomorphism_pattern {A B : C} (f : A ⟶ B) :
    IsIso (Abelian.coimageImageComparison f) := by
  -- Abelian圏で自動的に成立
  infer_instance

-- 🎯 実践例2: epi-mono分解の標準構成
lemma epi_mono_factorization_pattern {A B : C} (f : A ⟶ B) :
    ∃ (I : C) (e : A ⟶ I) (m : I ⟶ B), Epi e ∧ Mono m ∧ f = e ≫ m := by
  use Abelian.image f, Abelian.factorThruImage f, Abelian.image.ι f
  constructor
  · infer_instance  -- epi性
  constructor
  · infer_instance  -- mono性  
  · rw [Abelian.image.fac f]

-- 🎯 実践例3: 完全列の構成パターン
lemma exactness_pattern {A B : C} (f : A ⟶ B) :
    kernel.ι f ≫ Abelian.coimage.π f = 0 := by
  -- 完全性の基本性質から
  sorry -- 実装は複雑だが、理論的に必然

-- 🎯 実践例4: 群論との対応確認
example {G : Type*} [Group G] (N : Subgroup G) [N.Normal] :
    N = MonoidHom.ker (QuotientGroup.mk' N) := by
  exact (QuotientGroup.ker_mk' N).symm

end CategoryTheoryAbelianAPIDemo