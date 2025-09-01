import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.SelfAdjoint

open InnerProductSpace

-- 最も直接的なアプローチ
theorem self_adjoint_spectrum_real_direct {𝕜 : Type*} [RCLike 𝕜] {E : Type*} 
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] 
  (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) :
  ∀ μ : 𝕜, μ ∈ spectrum 𝕜 T → μ.im = 0 :=
by
  intro μ hμ
  -- 直接Mathlibの定理を適用
  exact IsSelfAdjoint.mem_spectrum_eq_re hT hμ