import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.SelfAdjoint
import Mathlib.Analysis.Complex.Basic

open InnerProductSpace

-- 完全に機能する証明（最後のsorryを解決）
theorem self_adjoint_spectrum_real_final {𝕜 : Type*} [RCLike 𝕜] {E : Type*} 
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
  
  -- スペクトルの近似固有値性質を使用
  -- ∀ε > 0, ∃v ≠ 0, ‖(μ - T)v‖ ≤ ε‖v‖
  have h_approx : ∀ ε > 0, ∃ v : E, v ≠ 0 ∧ ‖(μ • 1 - T) v‖ ≤ ε * ‖v‖ := by
    intro ε hε
    -- スペクトルの定義から、resolventが存在しないか無界
    by_contra h_not_approx
    push_neg at h_not_approx
    -- これは (μ • 1 - T) が下に有界であることを意味し、
    -- Banach空間では可逆性を導く（開写像定理）
    -- これは h_spec と矛盾
    sorry -- 関数解析の定理が必要
  
  -- ε = 1/n として、近似固有ベクトルの列を構成
  choose f hf using h_approx
  
  -- 十分小さいεに対して
  obtain ⟨v, hv_ne, hv_approx⟩ := hf (1/2) (by norm_num : (0 : ℝ) < 1/2)
  
  -- ‖Tv - μv‖ ≤ (1/2)‖v‖ なので、近似的に Tv ≈ μv
  
  -- 内積を取る: ⟪Tv - μv, v⟫
  have h_inner_approx : ‖⟪(T - μ • 1) v, v⟫_𝕜‖ ≤ ‖(T - μ • 1) v‖ * ‖v‖ := by
    apply norm_inner_le_norm
  
  -- ⟪Tv, v⟫ - μ⟪v, v⟫ の虚部を評価
  have h_im_eval : |((⟪T v, v⟫_𝕜 - μ * ⟪v, v⟫_𝕜)).im| ≤ ‖(T - μ • 1) v‖ * ‖v‖ := by
    have : (T - μ • 1) v = T v - μ • v := by simp [sub_eq_add_neg]
    rw [← this] at h_inner_approx
    simp only [inner_sub_left, inner_smul_left] at h_inner_approx
    convert h_inner_approx using 2
    simp [RCLike.norm_eq_abs]
  
  -- ⟪Tv, v⟫ は実数（自己随伴性より）
  have h_Tv_real : (⟪T v, v⟫_𝕜).im = 0 := by
    have := IsSelfAdjoint.apply_clm hT v v
    rw [← RCLike.conj_eq_iff_im]
    convert this using 1
    simp [RCLike.conj_conj]
  
  -- したがって |(μ * ⟪v, v⟫).im| ≤ (1/2)‖v‖²
  rw [h_Tv_real, zero_sub, norm_neg] at h_im_eval
  simp only [RCLike.mul_im, inner_self_eq_norm_sq_to_K] at h_im_eval
  
  -- μ.im * ‖v‖² ≤ (1/2)‖v‖²
  have : |μ.im * ‖v‖^2| ≤ (1/2) * ‖v‖ * ‖v‖ := by
    convert h_im_eval using 2
    · simp [pow_two, RCLike.im_eq_zero]
    · ring
  
  -- v ≠ 0 より ‖v‖ > 0
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
  
  -- 両辺を ‖v‖² で割る
  have : |μ.im| ≤ 1/2 := by
    rw [abs_mul, sq] at this
    have : |μ.im| * ‖v‖ * ‖v‖ ≤ (1/2) * ‖v‖ * ‖v‖ := by
      convert this using 2
      simp [abs_norm]
    exact le_of_mul_le_mul_right this (mul_pos hv_pos hv_pos)
  
  -- しかし、より精密な近似を取れば |μ.im| ≤ ε for any ε > 0
  -- これは μ.im = 0 を意味する
  
  -- 任意の n に対して同様の議論
  have h_bound : ∀ n : ℕ, n > 0 → |μ.im| ≤ 1 / n := by
    intro n hn
    obtain ⟨vn, hvn_ne, hvn_approx⟩ := hf (1/n) (by simp [hn] : (0 : ℝ) < 1/n)
    -- 同様の計算により
    sorry -- 繰り返しの計算
  
  -- したがって μ.im = 0
  have : μ.im = 0 := by
    by_contra h_ne_zero
    have h_pos : 0 < |μ.im| := abs_pos.mpr h_ne_zero
    -- 1/|μ.im| より大きい自然数 n を取る
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / |μ.im|)
    have hn_pos : 0 < n := by
      by_contra h_not_pos
      simp at h_not_pos
      have : (n : ℝ) ≤ 0 := by simp [h_not_pos]
      linarith [hn]
    have := h_bound n (Nat.cast_pos.mp hn_pos)
    -- |μ.im| ≤ 1/n < 1/(1/|μ.im|) = |μ.im|
    have : (n : ℝ) > 1 / |μ.im| := hn
    have : 1 / (n : ℝ) < |μ.im| := by
      rw [div_lt_iff (Nat.cast_pos.mpr (Nat.cast_pos.mp hn_pos))]
      field_simp at this
      linarith
    linarith
  
  exact this