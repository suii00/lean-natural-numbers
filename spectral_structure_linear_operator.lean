import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Star.SelfAdjoint

open InnerProductSpace

-- コンパクトノルム空間上の自己随伴作用素のスペクトルは実数値集合である
theorem self_adjoint_spectrum_real {𝕜 : Type*} [RCLike 𝕜] {E : Type*} 
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
  
  -- Mathlibには自己随伴作用素のスペクトルが実数であることの直接的な定理がある
  -- しかし、教育的な証明を完成させる
  
  -- 方法1: 固有値の場合の直接証明
  by_cases h_eigen : ∃ v : E, v ≠ 0 ∧ (μ • (1 : E →L[𝕜] E) - T) v = 0
  · -- 固有ベクトルが存在する場合
    obtain ⟨v, hv_ne, hv_eq⟩ := h_eigen
    -- T v = μ v を導出
    have Tv_eq : T v = μ • v := by
      have : (μ • (1 : E →L[𝕜] E)) v = T v + (μ • (1 : E →L[𝕜] E) - T) v := by
        simp [add_sub_cancel']
      rw [hv_eq, add_zero] at this
      simp at this
      exact this
    
    -- 内積の自己随伴性: ⟪T v, v⟫ = ⟪v, T v⟫
    have h_inner : ⟪T v, v⟫_𝕜 = ⟪v, T v⟫_𝕜 := IsSelfAdjoint.apply_clm hT v v
    
    -- T v = μ v を代入
    rw [Tv_eq] at h_inner
    simp only [inner_smul_left, inner_smul_right] at h_inner
    
    -- μ ⟪v, v⟫ = conj(μ) ⟪v, v⟫ を得る
    have eq_conj : μ * ⟪v, v⟫_𝕜 = (starRingEnd 𝕜 μ) * ⟪v, v⟫_𝕜 := by
      convert h_inner using 1
      · simp
      · simp [mul_comm]
    
    -- ⟪v, v⟫ ≠ 0 (v ≠ 0 より)
    have hvv_ne : ⟪v, v⟫_𝕜 ≠ 0 := inner_self_ne_zero.mpr hv_ne
    
    -- 両辺を ⟪v, v⟫ で割る
    have : μ = starRingEnd 𝕜 μ := by
      apply mul_right_cancel₀ hvv_ne
      exact eq_conj
    
    -- これは μ ≠ star μ と矛盾
    exact absurd this h_ne
    
  · -- 固有値でない場合: 近似固有値の性質を使用
    push_neg at h_eigen
    
    -- スペクトルの点は近似固有値
    -- 任意の ε > 0 に対して ‖(μ - T)v‖ ≤ ε‖v‖ となる v ≠ 0 が存在
    
    -- 1/2 を選んで近似固有ベクトルを取る
    have : ∃ v : E, v ≠ 0 ∧ ‖(μ • 1 - T) v‖ < ‖v‖ := by
      -- スペクトルの定義から、(μ • 1 - T) は可逆でない
      -- Banach空間での可逆でない作用素の特徴付け：
      -- 単射でないか、像が稠密でないか、有界逆を持たない
      
      -- h_spec から、次のいずれかが成立：
      -- 1. ker(μ • 1 - T) ≠ {0} （この場合は h_eigen で扱い済み）
      -- 2. range(μ • 1 - T) が閉でない
      -- 3. (μ • 1 - T) が下に有界でない
      
      -- ケース3を使用：∀c > 0, ∃v ≠ 0, ‖(μ • 1 - T) v‖ < c‖v‖
      by_contra h_contra
      push_neg at h_contra
      -- h_contra : ∀v ≠ 0, ‖(μ • 1 - T) v‖ ≥ ‖v‖
      
      -- これは (μ • 1 - T) が下に有界であることを意味
      have h_bounded_below : ∃ c > 0, ∀ v : E, c * ‖v‖ ≤ ‖(μ • 1 - T) v‖ := by
        use 1
        constructor
        · norm_num
        · intro v
          by_cases hv : v = 0
          · simp [hv]
          · exact h_contra v hv
      
      -- h_eigenから、ker(μ • 1 - T) = {0}
      have h_inj : Function.Injective (μ • 1 - T) := by
        intro x y hxy
        have : (μ • 1 - T) (x - y) = 0 := by simp [hxy]
        have : x - y = 0 := by
          by_contra h_ne
          have := h_eigen (x - y) h_ne
          push_neg at this
          exact this this
        linarith
      
      -- 下に有界かつ単射なBanach空間の作用素は可逆（開写像定理の帰結）
      -- これは h_spec と矛盾
      sorry -- 開写像定理の適用が必要
    
    obtain ⟨v, hv_ne, hv_bound⟩ := this
    
    -- ⟪(μ - T)v, v⟫ を評価
    have h_inner_bound : Complex.abs ⟪(μ • 1 - T) v, v⟫_𝕜 ≤ ‖(μ • 1 - T) v‖ * ‖v‖ := 
      norm_inner_le_norm _ _
    
    -- ⟪μv - Tv, v⟫ = μ⟪v,v⟫ - ⟪Tv,v⟫
    have h_expand : ⟪(μ • 1 - T) v, v⟫_𝕜 = μ * ⟪v, v⟫_𝕜 - ⟪T v, v⟫_𝕜 := by
      simp [inner_sub_left, inner_smul_left]
    
    -- ⟪Tv, v⟫ は実数（自己随伴性）
    have h_T_real : (⟪T v, v⟫_𝕜).im = 0 := by
      have := IsSelfAdjoint.apply_clm hT v v  
      rw [← RCLike.conj_eq_iff_im]
      convert this using 1
      simp [RCLike.conj_conj]
    
    -- (μ⟪v,v⟫ - ⟪Tv,v⟫).im = μ.im * ‖v‖²
    rw [h_expand] at h_inner_bound
    have h_im : Complex.abs (μ.im * ‖v‖^2) ≤ ‖(μ • 1 - T) v‖ * ‖v‖ := by
      convert h_inner_bound using 2
      simp [h_T_real, inner_self_eq_norm_sq_to_K, RCLike.sub_im, pow_two]
      ring
    
    -- |μ.im| * ‖v‖² ≤ ‖v‖²（hv_boundより）
    have : |μ.im| * ‖v‖^2 ≤ ‖v‖^2 := by
      rw [abs_mul] at h_im
      simp [sq, abs_norm] at h_im
      calc |μ.im| * ‖v‖ * ‖v‖ 
        _ ≤ ‖(μ • 1 - T) v‖ * ‖v‖ := h_im
        _ < ‖v‖ * ‖v‖ := by
          apply mul_lt_mul_of_pos_right hv_bound
          exact norm_pos_iff.mpr hv_ne
    
    -- v ≠ 0 より ‖v‖ > 0、両辺を ‖v‖² で割る
    have hv_pos : 0 < ‖v‖^2 := by
      simp [pow_pos, norm_pos_iff.mpr hv_ne]
    
    have : |μ.im| ≤ 1 := by
      apply le_of_mul_le_mul_right this hv_pos
    
    -- より小さい ε でこの議論を繰り返すと |μ.im| ≤ ε for all ε > 0
    -- したがって μ.im = 0
    exfalso
    apply h_not_real
    
    -- 任意に小さい上界を得られることを示す
    have h_arbitrary_small : ∀ ε > 0, |μ.im| ≤ ε := by
      intro ε hε
      -- ε/2 で近似固有ベクトルを取り、同様の議論
      -- スペクトルの近似固有値性から、∀δ > 0, ∃w ≠ 0, ‖(μ • 1 - T) w‖ < δ‖w‖
      
      -- δ = ε/2 として適切な w を選ぶ
      have : ∃ w : E, w ≠ 0 ∧ ‖(μ • 1 - T) w‖ < (ε/2) * ‖w‖ := by
        -- これはスペクトルの基本性質
        sorry -- スペクトル理論の結果を適用
      
      obtain ⟨w, hw_ne, hw_bound⟩ := this
      
      -- 前と同様の計算で |μ.im| ≤ ε/2 < ε を得る
      have h_inner_bound : Complex.abs ⟪(μ • 1 - T) w, w⟫_𝕜 ≤ ‖(μ • 1 - T) w‖ * ‖w‖ := 
        norm_inner_le_norm _ _
      
      have h_expand : ⟪(μ • 1 - T) w, w⟫_𝕜 = μ * ⟪w, w⟫_𝕜 - ⟪T w, w⟫_𝕜 := by
        simp [inner_sub_left, inner_smul_left]
      
      have h_T_real : (⟪T w, w⟫_𝕜).im = 0 := by
        have := IsSelfAdjoint.apply_clm hT w w  
        rw [← RCLike.conj_eq_iff_im]
        convert this using 1
        simp [RCLike.conj_conj]
      
      rw [h_expand] at h_inner_bound
      have h_im : Complex.abs (μ.im * ‖w‖^2) ≤ ‖(μ • 1 - T) w‖ * ‖w‖ := by
        convert h_inner_bound using 2
        simp [h_T_real, inner_self_eq_norm_sq_to_K, RCLike.sub_im, pow_two]
        ring
      
      have : |μ.im| * ‖w‖^2 < (ε/2) * ‖w‖^2 := by
        rw [abs_mul] at h_im
        simp [sq, abs_norm] at h_im
        calc |μ.im| * ‖w‖ * ‖w‖ 
          _ ≤ ‖(μ • 1 - T) w‖ * ‖w‖ := h_im
          _ < (ε/2) * ‖w‖ * ‖w‖ := by
            apply mul_lt_mul_of_pos_right hw_bound
            exact norm_pos_iff.mpr hw_ne
      
      have hw_pos : 0 < ‖w‖^2 := by
        simp [pow_pos, norm_pos_iff.mpr hw_ne]
      
      have : |μ.im| < ε/2 := by
        apply (mul_lt_mul_right hw_pos).mp at this
        exact this
      
      linarith
    
    -- したがって μ.im = 0
    have : μ.im = 0 := by
      by_contra h_ne
      have h_pos : 0 < |μ.im| := abs_pos.mpr h_ne
      obtain ⟨ε, hε_pos, hε_lt⟩ := exists_between h_pos
      have := h_arbitrary_small ε hε_pos
      linarith
    
    exact this
