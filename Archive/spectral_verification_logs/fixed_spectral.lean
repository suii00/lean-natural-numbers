import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Topology.Algebra.Module.Basic

open scoped InnerProduct

-- コンパクトノルム空間上の自己随伴作用素のスペクトルは実数値集合である
theorem self_adjoint_spectrum_real {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E] (T : E →L[𝕜] E) 
  (hT : IsSelfAdjoint T) :
  ∀ μ : 𝕜, μ ∈ spectrum 𝕜 T → ∃ r : ℝ, μ = r :=
by
  intro μ hμ
  -- 自己随伴作用素のスペクトルが実数であることを示す
  have h_real := IsSelfAdjoint.conj_eigenvalue_eq_self hT
  -- Mathlibの既存の定理を活用
  sorry -- 証明は後で完成させる