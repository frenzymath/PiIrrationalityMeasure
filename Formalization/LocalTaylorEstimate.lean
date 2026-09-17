import Formalization.QuotientRemainder
import Formalization.LocalOptimalityNumerics

/-! Uniform linear and quadratic remainders in (6.58), for all nearby displacements. -/

namespace PiIrrationality

open Filter
open scoped Topology

theorem parameterAuxiliaryBound_candidate_taylor_estimate :
    ∃ rho C₁ C₂ : ℝ, 0 < rho ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ h : ℝ × ℝ, 0 < parameterNormOne h → parameterNormOne h ≤ rho →
        |parameterAuxiliaryBound (candidate + h) - parameterAuxiliaryBound candidate +
          candidateSensitivity * candidateSectorVariation h *
            Real.log (1 / parameterNormOne h)| ≤
          C₁ * parameterNormOne h +
            C₂ * (parameterNormOne h * Real.log (1 / parameterNormOne h)) ^ 2 := by
  obtain ⟨Lr, hLr, hbr⟩ := differentiableAt_parameter_linear_bound
    analyticAt_parameterCoefficientRate.differentiableAt
  obtain ⟨Ls, hLs, hbs⟩ := differentiableAt_parameter_linear_bound
    analyticAt_parameterIntegralRate.differentiableAt
  obtain ⟨rho, C, hrho, hC, hphi⟩ := savingPhi_candidate_log_variation
  have hD := paperTau_pos
  have hcont : ContinuousAt
      (fun p => -parameterIntegralRate p - parameterCost p) candidate :=
    analyticAt_parameterIntegralRate.continuousAt.neg.sub
      (continuousAt_parameterCost candidate_admissible)
  have hden : ∀ᶠ p in 𝓝 candidate,
      paperTau / 2 < -parameterIntegralRate p - parameterCost p := by
    apply hcont.eventually_const_lt
    dsimp only
    rw [parameterRate_denominator_candidate]
    linarith [paperTau_pos]
  obtain ⟨delta, hdelta, hball⟩ := Metric.eventually_nhds_iff.mp
    (hbr.and (hbs.and hden))
  let Lg : ℝ := 6 + 5 * |Real.log 2|
  let A := Lr + Lg
  let B := Ls + Lg
  let W := C + 1
  let R₁ := (paperTau * A + |paperSigma| * B) / paperTau ^ 2
  let R₂ := 2 * (paperTau * (A + W) + |paperSigma| * (B + W)) * (B + W) /
    paperTau ^ 3
  have hA : 0 ≤ A := by dsimp [A, Lg]; positivity
  have hB : 0 ≤ B := by dsimp [B, Lg]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hR₁ : 0 ≤ R₁ := by dsimp [R₁]; positivity
  have hR₂ : 0 ≤ R₂ := by dsimp [R₂]; positivity
  have hK : 0 ≤ candidateSensitivity := by linarith [candidateSensitivity_bounds.1]
  refine ⟨min rho (min (delta / 2) (Real.exp (-1))),
    R₁ + candidateSensitivity * C, R₂, by positivity, by positivity, hR₂, ?_⟩
  intro h he hsmall
  have he_rho := hsmall.trans (min_le_left _ _)
  have he_delta : parameterNormOne h ≤ delta / 2 :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have he_exp : parameterNormOne h ≤ Real.exp (-1) :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hpball : dist (candidate + h) candidate < delta := by
    rw [dist_eq_norm, add_sub_cancel_left]
    exact (norm_le_parameterNormOne h).trans_lt (by linarith)
  obtain ⟨hr, hs, hd⟩ := hball hpball
  rw [add_sub_cancel_left] at hr hs
  have hL : 1 ≤ Real.log (1 / parameterNormOne h) := by
    have hl := Real.log_le_log he he_exp
    rw [Real.log_exp] at hl
    rw [one_div, Real.log_inv]
    linarith
  let a := parameterCoefficientRate (candidate + h) - parameterCoefficientRate candidate +
    (parameterSmoothCost (candidate + h) - parameterSmoothCost candidate)
  let b := -(parameterIntegralRate (candidate + h) - parameterIntegralRate candidate) -
    (parameterSmoothCost (candidate + h) - parameterSmoothCost candidate)
  let w := savingPhi (candidate + h) - savingPhi candidate
  have ha : |a| ≤ A * parameterNormOne h := by
    have hg := parameterSmoothCost_abs_sub_le candidate h
    have ht := abs_add_le
      (parameterCoefficientRate (candidate + h) - parameterCoefficientRate candidate)
      (parameterSmoothCost (candidate + h) - parameterSmoothCost candidate)
    dsimp only [a, A, Lg]
    nlinarith only [hr, hg, ht]
  have hb : |b| ≤ B * parameterNormOne h := by
    have hg := parameterSmoothCost_abs_sub_le candidate h
    have ht := abs_sub
      (-(parameterIntegralRate (candidate + h) - parameterIntegralRate candidate))
      (parameterSmoothCost (candidate + h) - parameterSmoothCost candidate)
    rw [abs_neg] at ht
    dsimp only [b, B, Lg]
    nlinarith only [hs, hg, ht]
  have hwerr := hphi h he he_rho
  have hw : |w| ≤ W * (parameterNormOne h * Real.log (1 / parameterNormOne h)) := by
    have ht := abs_add_le
      (w - candidateSectorVariation h * Real.log (1 / parameterNormOne h))
      (candidateSectorVariation h * Real.log (1 / parameterNormOne h))
    rw [sub_add_cancel, abs_mul, abs_of_nonneg (by linarith :
      0 ≤ Real.log (1 / parameterNormOne h))] at ht
    have hmain := mul_le_mul_of_nonneg_right (candidateSectorVariation_abs_le h)
      (show 0 ≤ Real.log (1 / parameterNormOne h) by linarith)
    have hlin := mul_le_mul_of_nonneg_left hL (mul_nonneg hC he.le)
    dsimp only [W]
    change |w - candidateSectorVariation h * Real.log (1 / parameterNormOne h)| ≤
      C * parameterNormOne h at hwerr
    nlinarith only [ht, hwerr, hmain, hlin]
  have hnum : paperSigma + a - w =
      parameterCoefficientRate (candidate + h) + parameterCost (candidate + h) := by
    rw [← parameterRate_numerator_candidate]
    dsimp [a, w, parameterCost]
    ring
  have hdeneq : paperTau + b + w =
      -parameterIntegralRate (candidate + h) - parameterCost (candidate + h) := by
    rw [← parameterRate_denominator_candidate]
    dsimp [b, w, parameterCost]
    ring
  have hrem := quotient_saving_remainder_bound (N := paperSigma) paperTau_pos
    (a := a) (b := b) (w := w) (by rw [hdeneq]; exact hd.le)
    hA hB hW he.le hL ha hb hw
  rw [hnum, hdeneq, show (paperTau + paperSigma) / paperTau ^ 2 =
    candidateSensitivity by rw [candidateSensitivity_eq_rates]; ring] at hrem
  have hrem' : |parameterAuxiliaryBound (candidate + h) - parameterAuxiliaryBound candidate +
      candidateSensitivity * w| ≤ R₁ * parameterNormOne h +
        R₂ * (parameterNormOne h * Real.log (1 / parameterNormOne h)) ^ 2 := by
    convert hrem using 1
    rw [parameterAuxiliaryBound_candidate]
    dsimp [parameterAuxiliaryBound, AuxiliaryBound, paperAuxiliaryValue]
    ring
  have hcorr : |candidateSensitivity *
      (candidateSectorVariation h * Real.log (1 / parameterNormOne h) - w)| ≤
      candidateSensitivity * C * parameterNormOne h := by
    rw [abs_mul, abs_of_nonneg hK, abs_sub_comm]
    exact (mul_le_mul_of_nonneg_left hwerr hK).trans_eq (by ring)
  have ht := abs_add_le
    (parameterAuxiliaryBound (candidate + h) - parameterAuxiliaryBound candidate +
      candidateSensitivity * w)
    (candidateSensitivity * (candidateSectorVariation h *
      Real.log (1 / parameterNormOne h) - w))
  have heq : parameterAuxiliaryBound (candidate + h) - parameterAuxiliaryBound candidate +
      candidateSensitivity * w + candidateSensitivity *
        (candidateSectorVariation h * Real.log (1 / parameterNormOne h) - w) =
      parameterAuxiliaryBound (candidate + h) - parameterAuxiliaryBound candidate +
        candidateSensitivity * candidateSectorVariation h *
          Real.log (1 / parameterNormOne h) := by ring
  rw [heq] at ht
  nlinarith only [ht, hrem', hcorr]

theorem parameterAuxiliaryBound_directional_taylor_estimate :
    ∃ rho C₁ C₂ : ℝ, 0 < rho ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ v : ℝ × ℝ, parameterNormOne v = 1 →
        ∀ e : ℝ, 0 < e → e ≤ rho →
          |parameterAuxiliaryBound (candidate + e • v) - parameterAuxiliaryBound candidate +
            candidateSensitivity * candidateSectorVariation v * e * Real.log (1 / e)| ≤
            C₁ * e + C₂ * (e * Real.log (1 / e)) ^ 2 := by
  obtain ⟨rho, C₁, C₂, hrho, hC₁, hC₂, hbound⟩ :=
    parameterAuxiliaryBound_candidate_taylor_estimate
  refine ⟨rho, C₁, C₂, hrho, hC₁, hC₂, ?_⟩
  intro v hv e he herho
  have hn : parameterNormOne (e • v) = e := by
    rw [parameterNormOne_smul, hv, abs_of_pos he, mul_one]
  have hb := hbound (e • v) (by rwa [hn]) (by rwa [hn])
  simpa only [hn, candidateSectorVariation_smul v he.le, mul_left_comm, mul_assoc,
    mul_comm] using hb

end PiIrrationality
