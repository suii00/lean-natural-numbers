import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# テンソル積の構造化（Bourbaki の精神）

本ファイルでは、Bourbaki の「構造＝台集合と構造の順序対＋射影の普遍性」
という見方に沿って、線型テンソル積の基本的な普遍性・結合自然性・
直和に関する分配・Hom–Tensor 対応を、射（線型写像）で記述します。
- 台集合と構造の順序対: `(V, W)` に付随する構造として `V ⊗[R] W`。
- 射影（普遍性）: 双線型写像 `V →ₗ[R] W →ₗ[R] X` は一意に
  線型写像 `V ⊗[R] W →ₗ[R] X` に延長する。
- 構造の自然性: 結合同型・直和分配・Hom–Tensor 対応。
-/

noncomputable section

open scoped TensorProduct DirectSum
open LinearMap

namespace MyProjects.LinearAlgebra.X

namespace TensorProductTask

variable {R V W X : Type*}
variable [CommSemiring R]
variable [AddCommMonoid V] [AddCommMonoid W] [AddCommMonoid X]
variable [Module R V] [Module R W] [Module R X]

/-! ## 普遍性：双線型からテンソルへの一意的延長 -/

theorem bilinear_to_tensor_linear_exists_unique
  (B : V →ₗ[R] W →ₗ[R] X) :
  ∃! f : V ⊗[R] W →ₗ[R] X, ∀ v w, f (v ⊗ₜ[R] w) = B v w := by
  refine ⟨TensorProduct.lift B, ?_ , ?_⟩
  · intro v w
    simpa using (TensorProduct.lift.tmul B v w)
  · intro f hf
    ext v w
    -- `lift.tmul` は `lift B (v ⊗ₜ w) = B v w` を与える
    -- ので，対称形で比較して一意性を得る
    simpa [hf v w] using (TensorProduct.lift.tmul B v w).symm

/-! ## 結合の自然性（同型の純テンソルでの振る舞い） -/

@[simp] theorem tensor_assoc_natural
  (v : V) (w : W) (x : X) :
  (TensorProduct.assoc R V W X) (((v ⊗ₜ[R] w) ⊗ₜ[R] x)) = v ⊗ₜ[R] (w ⊗ₜ[R] x) := rfl

/-! ## 直和に関する分配（有限添字の場合） -/

variable {ι : Type*}

noncomputable def tensor_distribute_sum
  [DecidableEq ι] [Fintype ι]
  (V' : ι → Type*)
  [∀ i, AddCommMonoid (V' i)] [∀ i, Module R (V' i)] :
  (⨁ i, V' i) ⊗[R] W ≃ₗ[R] ⨁ i, (V' i ⊗[R] W) :=
  TensorProduct.directSumLeft R (fun i => V' i) W

@[simp] lemma tensor_distribute_sum_tmul_lof
  [DecidableEq ι] [Fintype ι]
  (V' : ι → Type*)
  [∀ i, AddCommMonoid (V' i)] [∀ i, Module R (V' i)]
  (i : ι) (v : V' i) (w : W) :
  tensor_distribute_sum (R:=R) (V':=V')
      ((DirectSum.lof R ι (fun i => V' i) i v) ⊗ₜ[R] w)
    = DirectSum.lof R ι (fun i => V' i ⊗[R] W) i (v ⊗ₜ[R] w) := by
  -- avoid fragile named-argument matching; rely on type inference
  simpa [tensor_distribute_sum] using
    (TensorProduct.directSumLeft_tmul_lof (R:=R) (i:=i) (x:=v) (y:=w)
      (M:=fun i => V' i) (M':=W))

/-! ## Hom–Tensor 対応（普遍性の同型として） -/

noncomputable def hom_tensor_adjunction :
  (V ⊗[R] W →ₗ[R] X) ≃ₗ[R] (V →ₗ[R] W →ₗ[R] X) :=
  (TensorProduct.lift.equiv R V W X).symm

@[simp] lemma hom_tensor_adjunction_apply
  (f : V ⊗[R] W →ₗ[R] X) (v : V) (w : W) :
  (hom_tensor_adjunction (R:=R) (V:=V) (W:=W) (X:=X) f) v w = f (v ⊗ₜ[R] w) := rfl

@[simp] lemma hom_tensor_adjunction_symm_apply
  (B : V →ₗ[R] W →ₗ[R] X) (v : V) (w : W) :
  (hom_tensor_adjunction (R:=R) (V:=V) (W:=W) (X:=X)).symm B (v ⊗ₜ[R] w) = B v w := by
  -- this is `lift.equiv_apply` rewritten through `symm`
  simpa [hom_tensor_adjunction] using
    (TensorProduct.lift.equiv_apply (R:=R) (M:=V) (N:=W) (P:=X) B v w)

/-! ### examples -/
section Examples
  example (B : V →ₗ[R] W →ₗ[R] X) :
      ∀ v w, (TensorProduct.lift B) (v ⊗ₜ[R] w) = B v w := by
    intro v w; simpa using (TensorProduct.lift.tmul B v w)

  example (v : V) (w : W) (x : X) :
      (TensorProduct.assoc R V W X) (((v ⊗ₜ[R] w) ⊗ₜ[R] x)) = v ⊗ₜ[R] (w ⊗ₜ[R] x) := rfl
end Examples

end TensorProductTask

end MyProjects.LinearAlgebra.X
