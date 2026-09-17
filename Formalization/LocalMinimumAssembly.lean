import Formalization.ParameterCostDominance

/-! The local-minimum assembly, leaving only the actual saddle-rate regularity. -/

namespace PiIrrationality

open Filter
open scoped Topology

theorem differentiableAt_parameter_linear_bound {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f p) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ q in 𝓝 p, |f q - f p| ≤ L * parameterNormOne (q - p) := by
  obtain ⟨L, hL, hb⟩ := hf.isBigO_sub.exists_pos
  refine ⟨L, hL.le, ?_⟩
  filter_upwards [hb.bound] with q hq
  rw [Real.norm_eq_abs] at hq
  exact hq.trans (mul_le_mul_of_nonneg_left (norm_le_parameterNormOne _) hL.le)

theorem auxiliaryBound_sub_numerator (r s c r0 s0 c0 : ℝ) :
    (r + c) * (-s0 - c0) - (r0 + c0) * (-s - c) =
      (r - r0) * (-s0 - c0) + (s - s0) * (r0 + c0) + (c - c0) * (r0 - s0) := by
  ring

theorem theorem12_of_differentiable_rates (r s : ℝ × ℝ → ℝ)
    (hr : DifferentiableAt ℝ r candidate) (hs : DifferentiableAt ℝ s candidate)
    (hnum : 0 < r candidate + parameterCost candidate)
    (hden : 0 < -s candidate - parameterCost candidate) :
    theorem12 r s parameterCost := by
  let N := r candidate + parameterCost candidate
  let D := -s candidate - parameterCost candidate
  have hN : 0 < N := hnum
  have hD : 0 < D := hden
  have hND : 0 < r candidate - s candidate := by dsimp [N, D] at hN hD; linarith
  obtain ⟨Lr, hLr, hbr⟩ := differentiableAt_parameter_linear_bound hr
  obtain ⟨Ls, hLs, hbs⟩ := differentiableAt_parameter_linear_bound hs
  let M := (D * Lr + N * Ls) / (r candidate - s candidate)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨rho, hrho, hcost⟩ := parameterCost_candidate_increase_dominates hM
  have hdcont : ContinuousAt (fun p => -s p - parameterCost p) candidate :=
    hs.continuousAt.neg.sub (continuousAt_parameterCost candidate_admissible)
  have hdnear : ∀ᶠ p in 𝓝 candidate, 0 < -s p - parameterCost p :=
    hdcont.eventually_const_lt hden
  obtain ⟨delta, hdelta, hball⟩ := Metric.eventually_nhds_iff.mp
    (hbr.and (hbs.and hdnear))
  refine ⟨min delta (rho / 2), by positivity, ?_⟩
  intro p _ hp hdist
  have hsmall : dist p candidate < delta := by
    rw [dist_eq_norm]
    exact hdist.trans_le (min_le_left _ _)
  obtain ⟨hpr, hps, hpd⟩ := hball hsmall
  have hpn : 0 < parameterNormOne (p - candidate) :=
    (norm_pos_iff.mpr (sub_ne_zero.mpr hp)).trans_le (norm_le_parameterNormOne _)
  have hprho : parameterNormOne (p - candidate) < rho := by
    have ht := hdist.trans_le (min_le_right delta (rho / 2))
    exact (parameterNormOne_le_two_norm _).trans_lt (by linarith)
  have hc := hcost (p - candidate) hpn hprho
  have he : candidate + (p - candidate) = p := by abel
  rw [he] at hc
  have hc' := mul_lt_mul_of_pos_right hc hND
  have hMcancel : M * parameterNormOne (p - candidate) * (r candidate - s candidate) =
      (D * Lr + N * Ls) * parameterNormOne (p - candidate) := by
    dsimp [M]
    field_simp
  rw [hMcancel] at hc'
  have hrlower := mul_le_mul_of_nonneg_right (abs_le.mp hpr).1 hD.le
  have hslower := mul_le_mul_of_nonneg_right (abs_le.mp hps).1 hN.le
  have hcross : (r candidate + parameterCost candidate) * (-s p - parameterCost p) <
      (r p + parameterCost p) * (-s candidate - parameterCost candidate) := by
    have hid := auxiliaryBound_sub_numerator (r p) (s p) (parameterCost p)
      (r candidate) (s candidate) (parameterCost candidate)
    dsimp only [D, N] at hc' hrlower hslower
    nlinarith only [hc', hrlower, hslower, hid]
  unfold AuxiliaryBound
  linarith [(div_lt_div_iff₀ hden hpd).mpr hcross]

end PiIrrationality
