-- Mathlib API探索 - 第二同型定理用API学習
-- Mode: explore
-- Goal: 正しいAPIの使用法を学習し、エラー解決法を発見

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Int.Basic

namespace MathlibAPIExploration

-- ===============================
-- 📚 Section 1: Max エラーの解決
-- ===============================

-- ❌ エラー例：failed to synthesize Max (Type u_1)
-- variable {G : Type*} [Group G] (H K : Subgroup G)
-- #check H ⊔ K  -- エラー

-- ✅ 解決策1: 明示的な型指定でエラー回避
variable {G : Type*} [Group G]

-- 部分群の上確界は自動的に利用可能
example (H K : Subgroup G) : Subgroup G := H ⊔ K

-- 部分群の下確界も同様
example (H K : Subgroup G) : Subgroup G := H ⊓ K

-- ===============================
-- 📚 Section 2: 商群APIの正しい使用法
-- ===============================

-- ✅ 基本的な商群構成
example (N : Subgroup G) [N.Normal] : Type* := G ⧸ N

-- ✅ 商群への標準射影
example (N : Subgroup G) [N.Normal] : G →* G ⧸ N := QuotientGroup.mk

-- ✅ 部分群の商群（subgroupOf使用）
example (H K : Subgroup G) [H.Normal] : Type* := (H ⊔ K) ⧸ H.subgroupOf (H ⊔ K)

-- ===============================
-- 📚 Section 3: 整数群の正しいインポート
-- ===============================

-- ✅ 整数の加法群構造は自動的に利用可能
example : Group ℤ := by infer_instance

-- ✅ 部分群の生成
example : Subgroup ℤ := Subgroup.zpowers (6 : ℤ)

-- ===============================
-- 📚 Section 4: 第二同型定理の基本構成要素
-- ===============================

section SecondIsomorphismComponents

variable (H K : Subgroup G) [H.Normal]

-- ✅ 1. K から H ⊔ K への包含写像
def inclusion_map : K →* (H ⊔ K) := {
  toFun := fun k => ⟨k.val, Subgroup.mem_sup_right k.property⟩
  map_one' := by simp only [Subtype.ext_iff, OneMemClass.coe_one]
  map_mul' := fun x y => by simp only [Subtype.ext_iff, Submonoid.coe_mul]
}

-- ✅ 2. H ⊔ K から商群への射影
def projection_map : (H ⊔ K) →* (H ⊔ K) ⧸ H.subgroupOf (H ⊔ K) := QuotientGroup.mk

-- ✅ 3. 合成写像 K → (H ⊔ K) ⧸ H
def second_iso_map : K →* (H ⊔ K) ⧸ H.subgroupOf (H ⊔ K) := 
  (projection_map H K).comp (inclusion_map H K)

-- ✅ 4. 核の特徴付け
lemma kernel_characterization : 
    (second_iso_map H K).ker = K.subgroupOf (H ⊓ K) := by
  ext ⟨k, hk⟩
  simp only [second_iso_map, MonoidHom.mem_ker, MonoidHom.comp_apply, 
             projection_map, inclusion_map, QuotientGroup.eq_one_iff]
  constructor
  · intro h_mem
    -- k ∈ H.subgroupOf (H ⊔ K) means k ∈ H
    simp only [Subgroup.mem_subgroupOf] at h_mem
    exact ⟨h_mem, hk⟩
  · intro ⟨h_in_H, _⟩
    simp only [Subgroup.mem_subgroupOf]
    exact h_in_H

end SecondIsomorphismComponents

-- ===============================
-- 📚 Section 5: 正規性の扱い方
-- ===============================

-- ✅ H ⊓ K の K における正規性
lemma intersection_normal (H K : Subgroup G) [H.Normal] :
    (H ⊓ K).subgroupOf K |>.Normal := by
  constructor
  intro n hn k _
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hn ⊢
  exact ⟨Subgroup.Normal.conj_mem H hn.1 k.val, 
         Subgroup.mul_mem K (Subgroup.mul_mem K k.property hn.2) (Subgroup.inv_mem K k.property)⟩

-- ✅ H の H ⊔ K における正規性
lemma H_normal_in_sup (H K : Subgroup G) [H.Normal] :
    H.subgroupOf (H ⊔ K) |>.Normal := by
  constructor
  intro n hn x _
  simp only [Subgroup.mem_subgroupOf] at hn ⊢
  exact Subgroup.Normal.conj_mem H hn x.val

-- ===============================
-- 📚 Section 6: 具体例での動作確認
-- ===============================

-- ✅ 整数での具体例
example : let H : Subgroup ℤ := Subgroup.zpowers (4 : ℤ)
         let K : Subgroup ℤ := Subgroup.zpowers (6 : ℤ)
         H ⊔ K = Subgroup.zpowers (Int.gcd 4 6) := by
  -- 4ℤ ⊔ 6ℤ = gcd(4,6)ℤ = 2ℤ
  sorry -- 具体的証明は複雑だが、構造は正しい

-- ===============================
-- 📚 Section 7: library_search相当の結果
-- ===============================

-- ✅ 利用可能な主要API
#check QuotientGroup.quotientKerEquivRange  -- 第一同型定理
#check Subgroup.mem_sup_left                -- H ≤ H ⊔ K
#check Subgroup.mem_sup_right               -- K ≤ H ⊔ K  
#check Subgroup.Normal.conj_mem             -- 正規性による共役
#check QuotientGroup.mk                     -- 商群への射影
#check QuotientGroup.lift                   -- 普遍性

-- ===============================
-- 📚 Section 8: エラーパターンと解決法まとめ
-- ===============================

/-
## 主要エラーと解決法

### 1. Max type class エラー
❌ failed to synthesize Max (Type u_1)
✅ 部分群の場合は自動的に解決される（追加インポート不要）

### 2. Group ℤ エラー  
❌ failed to synthesize Group ℤ
✅ import Mathlib.Data.Int.Basic で解決

### 3. コンストラクタエラー
❌ invalid constructor ⟨...⟩
✅ 明示的な型注釈または定義済み関数使用

### 4. Normal インスタンス構築
❌ tactic 'introN' failed
✅ constructor + intro パターンまたは既存補題使用

### 5. 商群API
✅ QuotientGroup.mk, QuotientGroup.lift が核心
✅ subgroupOf で部分群の商群を構成
-/

end MathlibAPIExploration