import Formalization.LocalTaylorEstimate

/-! The quadratic remainder is o(epsilon), giving the uniform lower bound (6.59). -/

namespace PiIrrationality

open Filter Asymptotics
open scoped Topology

theorem tendsto_mul_log_inv_sq_zero :
    Tendsto (fun e : ℝ => e * Real.log (1 / e) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have ht := (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero.comp
    tendsto_inv_nhdsGT_zero
  simpa only [Function.comp_def, id_eq, one_div, div_inv_eq_mul, mul_comm] using ht

theorem log_quadratic_remainder_isLittleO :
    (fun e : ℝ => (e * Real.log (1 / e)) ^ 2) =o[𝓝[>] 0] (fun e : ℝ => e) := by
  apply (isLittleO_iff_tendsto (fun e he => by simp [he])).mpr
  apply tendsto_mul_log_inv_sq_zero.congr'
  filter_upwards [self_mem_nhdsWithin] with e he
  have he' : e ≠ 0 := ne_of_gt he
  field_simp

theorem parameterAuxiliaryBound_candidate_log_remainder :
    ∃ rho C : ℝ, 0 < rho ∧ 0 ≤ C ∧
      ∀ h : ℝ × ℝ, 0 < parameterNormOne h → parameterNormOne h < rho →
        |parameterAuxiliaryBound (candidate + h) - parameterAuxiliaryBound candidate +
          candidateSensitivity * candidateSectorVariation h *
            Real.log (1 / parameterNormOne h)| ≤ C * parameterNormOne h := by
  obtain ⟨rho, C₁, C₂, hrho, hC₁, hC₂, hbound⟩ :=
    parameterAuxiliaryBound_candidate_taylor_estimate
  obtain ⟨delta, hdelta, hdelta_bound⟩ :=
    Metric.tendsto_nhdsWithin_nhds.mp tendsto_mul_log_inv_sq_zero 1 (by norm_num)
  refine ⟨min rho delta, C₁ + C₂, by positivity, by positivity, ?_⟩
  intro h he hsmall
  have hb := hbound h he (hsmall.trans_le (min_le_left _ _)).le
  have hdist : dist (parameterNormOne h) 0 < delta := by
    rw [Real.dist_eq, sub_zero, abs_of_pos he]
    exact hsmall.trans_le (min_le_right _ _)
  have hquad := hdelta_bound (show parameterNormOne h ∈ Set.Ioi (0 : ℝ) from he) hdist
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hquad
  have hmul := mul_le_mul_of_nonneg_left hquad.le he.le
  have hquad' : (parameterNormOne h * Real.log (1 / parameterNormOne h)) ^ 2 ≤
      parameterNormOne h := by nlinarith only [hmul]
  have hCquad := mul_le_mul_of_nonneg_left hquad' hC₂
  nlinarith only [hb, hCquad]

theorem parameterAuxiliaryBound_candidate_quantitative_lower :
    ∃ rho C : ℝ, 0 < rho ∧ 0 ≤ C ∧
      ∀ h : ℝ × ℝ, 0 < parameterNormOne h → parameterNormOne h < rho →
        candidateSensitivity * ((557 : ℝ) / 4139253) * parameterNormOne h *
            Real.log (1 / parameterNormOne h) - C * parameterNormOne h ≤
          parameterAuxiliaryBound (candidate + h) - parameterAuxiliaryBound candidate := by
  obtain ⟨rho, C, hrho, hC, hbound⟩ := parameterAuxiliaryBound_candidate_log_remainder
  refine ⟨min rho 1, C, by positivity, hC, ?_⟩
  intro h he hsmall
  have hb := (abs_le.mp (hbound h he (hsmall.trans_le (min_le_left _ _)))).1
  have hlog : 0 ≤ Real.log (1 / parameterNormOne h) := by
    apply Real.log_nonneg
    exact (le_div_iff₀ he).mpr (by linarith [hsmall.trans_le (min_le_right rho 1)])
  have hK : 0 ≤ candidateSensitivity := by linarith [candidateSensitivity_bounds.1]
  have hD := mul_le_mul_of_nonneg_left (candidateSectorVariation_bound h) hK
  have hmain := mul_le_mul_of_nonneg_right hD hlog
  nlinarith only [hb, hmain]

theorem parameterAuxiliaryBound_directional_quantitative_lower :
    ∃ rho C : ℝ, 0 < rho ∧ 0 ≤ C ∧
      ∀ v : ℝ × ℝ, parameterNormOne v = 1 →
        ∀ e : ℝ, 0 < e → e < rho →
          candidateSensitivity * ((557 : ℝ) / 4139253) * e * Real.log (1 / e) - C * e ≤
            parameterAuxiliaryBound (candidate + e • v) - parameterAuxiliaryBound candidate := by
  obtain ⟨rho, C, hrho, hC, hbound⟩ := parameterAuxiliaryBound_candidate_quantitative_lower
  refine ⟨rho, C, hrho, hC, ?_⟩
  intro v hv e he herho
  have hn : parameterNormOne (e • v) = e := by
    rw [parameterNormOne_smul, hv, abs_of_pos he, mul_one]
  simpa only [hn] using hbound (e • v) (by rwa [hn]) (by rwa [hn])

end PiIrrationality
