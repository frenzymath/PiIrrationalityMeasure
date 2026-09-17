import Formalization.SavingPhiLogVariation

/-! The saving decrease dominates every fixed linear error near the candidate. -/

namespace PiIrrationality

theorem savingPhi_candidate_decrease_dominates {M : ℝ} (hM : 0 ≤ M) :
    ∃ r : ℝ, 0 < r ∧ ∀ h : ℝ × ℝ,
      0 < parameterNormOne h → parameterNormOne h < r →
      savingPhi (candidate + h) - savingPhi candidate < -M * parameterNormOne h := by
  obtain ⟨rho, C, hrho, hC, hmodel⟩ := savingPhi_candidate_log_variation
  let kappa : ℝ := 557 / 4139253
  have hk : 0 < kappa := by norm_num [kappa]
  let A := (C + M + 1) / kappa
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨min rho (Real.exp (-A)), lt_min hrho (Real.exp_pos _), ?_⟩
  intro h hd hdr
  have hsmall := hdr.trans_le (min_le_right rho (Real.exp (-A)))
  have hlog' : Real.log (parameterNormOne h) < -A :=
    (Real.log_lt_iff_lt_exp hd).mpr hsmall
  have hlog : A < Real.log (1 / parameterNormOne h) := by
    rw [one_div, Real.log_inv]
    linarith
  have hl0 : 0 ≤ Real.log (1 / parameterNormOne h) := (hA.trans hlog).le
  have hD := mul_le_mul_of_nonneg_right (candidateSectorVariation_bound h) hl0
  have he := (abs_le.mp (hmodel h hd (hdr.trans_le (min_le_left _ _)).le)).2
  have hscale : C + M + 1 < kappa * Real.log (1 / parameterNormOne h) := by
    have ht := (div_lt_iff₀ hk).mp hlog
    nlinarith only [ht]
  have hprod := mul_lt_mul_of_pos_right hscale hd
  dsimp only [kappa] at hD hprod
  nlinarith only [he, hD, hprod, hd]

end PiIrrationality
