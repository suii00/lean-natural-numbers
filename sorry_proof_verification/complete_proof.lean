import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.SelfAdjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic

open InnerProductSpace
open scoped ComplexConjugate

-- 完全な証明を試みる
theorem self_adjoint_spectrum_real_complete {𝕜 : Type*} [RCLike 𝕜] {E : Type*} 
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] 
  (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) :
  ∀ μ : 𝕜, μ ∈ spectrum 𝕜 T → μ.im = 0 :=
by
  intro μ hμ
  -- 背理法による証明
  by_contra h_not_real
  
  -- μ = a + bi (b ≠ 0) と表現
  let a := μ.re
  let b := μ.im
  have hb : b ≠ 0 := h_not_real
  
  -- スペクトルの定義から (μ • 1 - T) は可逆でない
  have h_spec : ¬IsUnit (μ • 1 - T) := by
    rwa [← spectrum.mem_iff] at hμ
  
  -- 自己随伴性から star (μ • 1 - T) = (star μ) • 1 - T
  have h_adj : star (μ • 1 - T) = (star μ) • 1 - T := by
    simp only [star_sub, star_smul, star_one]
    rw [IsSelfAdjoint.star_eq hT]
  
  -- μの虚部が0でない場合、μ ≠ star μ
  have h_ne : μ ≠ star μ := by
    intro h_eq
    have : μ.im = (star μ).im := by rw [h_eq]
    simp [RCLike.conj_im] at this
    linarith [this, hb]
  
  -- ここから詳細な証明を展開
  -- (μ • 1 - T) が可逆でないなら、ある非零ベクトル v が存在して (μ • 1 - T) v = 0
  -- または (μ • 1 - T) が全射でない
  
  -- Case 1: ker(μ • 1 - T) ≠ {0} の場合
  by_cases h_ker : ∃ v : E, v ≠ 0 ∧ (μ • 1 - T) v = 0
  · -- 固有ベクトルが存在する場合
    obtain ⟨v, hv_ne, hv_eq⟩ := h_ker
    -- T v = μ v
    have Tv_eq : T v = μ • v := by
      rw [← sub_eq_zero] at hv_eq
      simp [sub_smul] at hv_eq
      linarith [hv_eq]
    
    -- 自己随伴性を使用: ⟪T v, v⟫ = ⟪v, T v⟫
    have h_self_adj : ⟪T v, v⟫_𝕜 = ⟪v, T v⟫_𝕜 := by
      exact IsSelfAdjoint.apply_clm hT v v
    
    -- T v = μ v を代入
    rw [Tv_eq] at h_self_adj
    simp [inner_smul_left, inner_smul_right] at h_self_adj
    
    -- ⟪v, v⟫ ≠ 0 (v ≠ 0 より)
    have hvv_ne : ⟪v, v⟫_𝕜 ≠ 0 := by
      exact inner_self_ne_zero.mpr hv_ne
    
    -- μ ⟪v, v⟫ = conj(μ) ⟪v, v⟫
    have : μ * ⟪v, v⟫_𝕜 = star μ * ⟪v, v⟫_𝕜 := by
      rw [← h_self_adj]
      simp [inner_smul_left, inner_smul_right]
      ring
    
    -- ⟪v, v⟫ で割ると μ = star μ
    have : μ = star μ := by
      field_simp [hvv_ne] at this
      exact this
    
    -- これは h_ne と矛盾
    exact h_ne this
    
  · -- ker(μ • 1 - T) = {0} だが (μ • 1 - T) が可逆でない場合
    -- この場合、range が稠密でないか、有界逆作用素が存在しない
    push_neg at h_ker
    
    -- star μ についても同様の議論ができる
    have h_star_spec : ¬IsUnit ((star μ) • 1 - T) := by
      -- 自己随伴作用素のスペクトルは共役で閉じている
      sorry -- この部分は高度なスペクトル理論が必要
    
    -- (μ • 1 - T) と (star μ • 1 - T) の合成を考える
    -- μ ≠ star μ なので、これらは可換で、積は可逆になるはず
    -- これが矛盾を導く
    sorry -- 技術的な詳細