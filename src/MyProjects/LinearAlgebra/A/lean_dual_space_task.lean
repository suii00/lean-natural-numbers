import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.LinearAlgebra.Dual.Defs

/-!
  Bourbaki の精神（順序対と射影）:
  双対空間 `Module.Dual R V` は「射（線形汎関数）の集合」であり、
  等式は射の振る舞い（加法・スカラー倍）を読むことで成分的に確認できる。
  ここでは双対の和・評価・二重双対の評価、ペアリングの双線形性を
  既存の標準補題だけで示す。
-/

noncomputable section

namespace MyProjects.LinearAlgebra.A

-- 双対空間の元（線形汎関数）の和の定義が線形であることの証明
theorem dual_add_is_linear {R V : Type*}
  [CommSemiring R] [AddCommMonoid V] [Module R V]
  (φ ψ : Module.Dual R V) (v : V) :
  (φ + ψ) v = φ v + ψ v := by
  -- これは線形写像の和の定義（点ごとの加法）。
  simpa [LinearMap.add_apply]

-- 評価写像の線形性：eval_v : V* → R が線形写像であること
theorem eval_map_is_linear {R V : Type*}
  [CommSemiring R] [AddCommMonoid V] [Module R V]
  (v : V) (φ ψ : Module.Dual R V) :
  φ v + ψ v = (φ + ψ) v := by
  -- 上の等式の対称形。右辺を定義で展開すれば自明。
  simpa [LinearMap.add_apply]

-- 発展：双対の双対への自然な埋め込み（有限次元では同型）
theorem double_dual_eval {R V : Type*}
  [CommSemiring R] [AddCommMonoid V] [Module R V]
  (v : V) (φ : Module.Dual R V) :
  Module.Dual.eval R V v φ = φ v := by
  -- 既存の単純化補題
  simpa using (Module.Dual.eval_apply (R:=R) (M:=V) v φ)

-- Bourbakiスタイル：双対ペアリング ⟨v, φ⟩ = φ(v) の双線形性
theorem dual_pairing_bilinear {R V : Type*}
  [CommSemiring R] [AddCommMonoid V] [Module R V]
  (v w : V) (φ : Module.Dual R V) (a : R) :
  φ (a • v + w) = a * (φ v) + φ w := by
  -- 射の加法性と斉次性を順に読む。`R` 上の `•` は乗法に一致。
  calc
    φ (a • v + w) = φ (a • v) + φ w := by simpa using (LinearMap.map_add φ (a • v) w)
    _ = a • φ v + φ w := by simpa using (LinearMap.map_smul φ a v)
    _ = a * (φ v) + φ w := by simpa [smul_eq_mul]

/-! ## Bourbaki スタイルの軽い example
  射（双対の元）の和・評価・二重双対評価を、定義と既存補題により確認。 -/

section Examples
  variable {R V : Type*}
  variable [CommSemiring R] [AddCommMonoid V] [Module R V]
  variable (φ ψ : Module.Dual R V) (v w : V) (a : R)

  example : (φ + ψ) v = φ v + ψ v := by simpa [LinearMap.add_apply]
  example : φ v + ψ v = (φ + ψ) v := by simpa [LinearMap.add_apply]
  example : Module.Dual.eval R V v φ = φ v := by simpa using (Module.Dual.eval_apply (R:=R) (M:=V) v φ)
  example : φ (a • v + w) = a * φ v + φ w := by
    simpa [smul_eq_mul] using (dual_pairing_bilinear (R:=R) (v:=v) (w:=w) (φ:=φ) (a:=a))
end Examples

end MyProjects.LinearAlgebra.A
