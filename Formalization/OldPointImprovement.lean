import Formalization.OldPointAnalytic
import Formalization.OldPointNumerics
import Formalization.OldPointLogVariation
import Formalization.LocalLogLowerBound

/-! The actual one-sided logarithmic improvement at the old point, (6.32)--(6.33). -/

namespace PiIrrationality

open Filter
open scoped Topology

noncomputable def oldParameterAuxiliaryBound : ℝ × ℝ → ℝ :=
  AuxiliaryBound oldParameterCoefficientRate oldParameterIntegralRate parameterCost

theorem oldPoint_saving_derivative :
    HasDerivAt (auxiliaryH oldCoefficientRate oldIntegralRate (parameterSmoothCost oldPoint))
      (-oldK) (savingPhi oldPoint) ∧ -oldK < 0 := by
  have hD : 0 < oldTau := by linarith [oldTau_enclosure.1]
  have he : -oldIntegralRate - parameterSmoothCost oldPoint + savingPhi oldPoint = oldTau := by
    dsimp [oldTau, parameterCost]
    ring
  have hd := auxiliaryH_hasDerivAt (r := oldCoefficientRate) (by rw [he]; exact hD.ne')
  rw [he, neg_div] at hd
  exact ⟨hd, by linarith [oldK_enclosure.1]⟩

theorem oldParameterAuxiliaryBound_taylor :
    ∃ rho C₁ C₂ : ℝ, 0 < rho ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ e : ℝ, 0 < e → e ≤ rho →
        |oldParameterAuxiliaryBound (oldPoint + e • ((1 : ℝ) / 2, 1)) -
          oldParameterAuxiliaryBound oldPoint + oldK * e * Real.log (1 / e)| ≤
            C₁ * e + C₂ * (e * Real.log (1 / e)) ^ 2 := by
  obtain ⟨Lr, hLr, hbr⟩ := differentiableAt_parameter_linear_bound
    analyticAt_oldParameterCoefficientRate.differentiableAt
  obtain ⟨Ls, hLs, hbs⟩ := differentiableAt_parameter_linear_bound
    analyticAt_oldParameterIntegralRate.differentiableAt
  obtain ⟨rho, C, hrho, hC, hphi⟩ := savingPhi_oldPoint_log_variation
  have hD : 0 < oldTau := by linarith [oldTau_enclosure.1]
  have hcost : ContinuousAt parameterCost oldPoint := by
    apply ContinuousAt.sub (f := parameterSmoothCost)
    · unfold parameterSmoothCost
      fun_prop
    · exact continuousAt_savingPhi (by norm_num [oldPoint]) (by norm_num [oldPoint])
        (by norm_num [oldPoint])
  have hcont : ContinuousAt
      (fun p => -oldParameterIntegralRate p - parameterCost p) oldPoint :=
    analyticAt_oldParameterIntegralRate.continuousAt.neg.sub hcost
  have hden : ∀ᶠ p in 𝓝 oldPoint,
      oldTau / 2 < -oldParameterIntegralRate p - parameterCost p := by
    apply hcont.eventually_const_lt
    dsimp only
    rw [oldParameterIntegralRate_at]
    change oldTau / 2 < oldTau
    linarith
  obtain ⟨delta, hdelta, hball⟩ := Metric.eventually_nhds_iff.mp
    (hbr.and (hbs.and hden))
  let Lg : ℝ := 6 + 5 * |Real.log 2|
  let A := (3 / 2) * (Lr + Lg)
  let B := (3 / 2) * (Ls + Lg)
  let W := C + 1
  let N := oldCoefficientRate + parameterCost oldPoint
  let R₁ := (oldTau * A + |N| * B) / oldTau ^ 2
  let R₂ := 2 * (oldTau * (A + W) + |N| * (B + W)) * (B + W) / oldTau ^ 3
  have hA : 0 ≤ A := by dsimp [A, Lg]; positivity
  have hB : 0 ≤ B := by dsimp [B, Lg]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hR₁ : 0 ≤ R₁ := by dsimp [R₁]; positivity
  have hR₂ : 0 ≤ R₂ := by dsimp [R₂]; positivity
  have hK : 0 ≤ oldK := by linarith [oldK_enclosure.1]
  refine ⟨min rho (min (delta / 2) (Real.exp (-1))), R₁ + oldK * C, R₂,
    by positivity, by positivity, hR₂, ?_⟩
  intro e he hsmall
  let h : ℝ × ℝ := e • ((1 : ℝ) / 2, 1)
  have hn : parameterNormOne h = (3 / 2) * e := by
    rw [parameterNormOne_smul, abs_of_pos he]
    norm_num [parameterNormOne]
    ring
  have he_rho := hsmall.trans (min_le_left _ _)
  have he_delta : e ≤ delta / 2 := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have he_exp : e ≤ Real.exp (-1) := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hpball : dist (oldPoint + h) oldPoint < delta := by
    rw [dist_eq_norm, add_sub_cancel_left]
    have hnorm := norm_le_parameterNormOne h
    rw [hn] at hnorm
    linarith
  obtain ⟨hr, hs, hd⟩ := hball hpball
  rw [add_sub_cancel_left, hn] at hr hs
  have hL : 1 ≤ Real.log (1 / e) := by
    have hl := Real.log_le_log he he_exp
    rw [Real.log_exp] at hl
    rw [one_div, Real.log_inv]
    linarith
  let a := oldParameterCoefficientRate (oldPoint + h) - oldParameterCoefficientRate oldPoint +
    (parameterSmoothCost (oldPoint + h) - parameterSmoothCost oldPoint)
  let b := -(oldParameterIntegralRate (oldPoint + h) - oldParameterIntegralRate oldPoint) -
    (parameterSmoothCost (oldPoint + h) - parameterSmoothCost oldPoint)
  let w := savingPhi (oldPoint + h) - savingPhi oldPoint
  have ha : |a| ≤ A * e := by
    have hg := parameterSmoothCost_abs_sub_le oldPoint h
    rw [hn] at hg
    have ht := abs_add_le
      (oldParameterCoefficientRate (oldPoint + h) - oldParameterCoefficientRate oldPoint)
      (parameterSmoothCost (oldPoint + h) - parameterSmoothCost oldPoint)
    dsimp only [a, A, Lg]
    nlinarith only [hr, hg, ht]
  have hb : |b| ≤ B * e := by
    have hg := parameterSmoothCost_abs_sub_le oldPoint h
    rw [hn] at hg
    have ht := abs_sub
      (-(oldParameterIntegralRate (oldPoint + h) - oldParameterIntegralRate oldPoint))
      (parameterSmoothCost (oldPoint + h) - parameterSmoothCost oldPoint)
    rw [abs_neg] at ht
    dsimp only [b, B, Lg]
    nlinarith only [hs, hg, ht]
  have hwerr : |w - e * Real.log (1 / e)| ≤ C * e := hphi e he he_rho
  have hw : |w| ≤ W * (e * Real.log (1 / e)) := by
    have ht := abs_add_le (w - e * Real.log (1 / e)) (e * Real.log (1 / e))
    rw [sub_add_cancel, abs_of_nonneg (by positivity : 0 ≤ e * Real.log (1 / e))] at ht
    have hlin := mul_le_mul_of_nonneg_left hL (mul_nonneg hC he.le)
    dsimp only [W]
    nlinarith only [ht, hwerr, hlin]
  have hnum : N + a - w = oldParameterCoefficientRate (oldPoint + h) + parameterCost (oldPoint + h) := by
    dsimp [N, a, w, parameterCost]
    rw [oldParameterCoefficientRate_at]
    ring
  have hdeneq : oldTau + b + w = -oldParameterIntegralRate (oldPoint + h) - parameterCost (oldPoint + h) := by
    dsimp [oldTau, b, w, parameterCost]
    rw [oldParameterIntegralRate_at]
    ring
  have hrem := quotient_saving_remainder_bound (N := N) hD
    (a := a) (b := b) (w := w) (by rw [hdeneq]; exact hd.le)
    hA hB hW he.le hL ha hb hw
  have hk : (oldTau + N) / oldTau ^ 2 = oldK := by
    dsimp [N, oldTau, oldK]
    ring
  rw [hnum, hdeneq, hk] at hrem
  have hrem' : |oldParameterAuxiliaryBound (oldPoint + h) - oldParameterAuxiliaryBound oldPoint +
      oldK * w| ≤ R₁ * e + R₂ * (e * Real.log (1 / e)) ^ 2 := by
    convert! hrem using 1
    dsimp [oldParameterAuxiliaryBound, AuxiliaryBound, N, oldTau]
    rw [oldParameterCoefficientRate_at, oldParameterIntegralRate_at]
    ring
  have hcorr : |oldK * (e * Real.log (1 / e) - w)| ≤ oldK * C * e := by
    rw [abs_mul, abs_of_nonneg hK, abs_sub_comm]
    exact (mul_le_mul_of_nonneg_left hwerr hK).trans_eq (by ring)
  have ht := abs_add_le
    (oldParameterAuxiliaryBound (oldPoint + h) - oldParameterAuxiliaryBound oldPoint + oldK * w)
    (oldK * (e * Real.log (1 / e) - w))
  have heq : oldParameterAuxiliaryBound (oldPoint + h) - oldParameterAuxiliaryBound oldPoint +
      oldK * w + oldK * (e * Real.log (1 / e) - w) =
        oldParameterAuxiliaryBound (oldPoint + h) - oldParameterAuxiliaryBound oldPoint +
          oldK * e * Real.log (1 / e) := by ring
  rw [heq] at ht
  nlinarith only [ht, hrem', hcorr]

theorem oldParameterAuxiliaryBound_log_variation :
    ∃ rho C : ℝ, 0 < rho ∧ 0 ≤ C ∧ ∀ e : ℝ, 0 < e → e < rho →
      |oldParameterAuxiliaryBound (oldPoint + e • ((1 : ℝ) / 2, 1)) -
        oldParameterAuxiliaryBound oldPoint + oldK * e * Real.log (1 / e)| ≤ C * e := by
  obtain ⟨rho, C₁, C₂, hrho, hC₁, hC₂, hbound⟩ := oldParameterAuxiliaryBound_taylor
  obtain ⟨delta, hdelta, hdelta_bound⟩ :=
    Metric.tendsto_nhdsWithin_nhds.mp tendsto_mul_log_inv_sq_zero 1 (by norm_num)
  refine ⟨min rho delta, C₁ + C₂, by positivity, by positivity, ?_⟩
  intro e he hsmall
  have hb := hbound e he (hsmall.trans_le (min_le_left _ _)).le
  have hquad := hdelta_bound he (by
    rw [Real.dist_eq, sub_zero, abs_of_pos he]
    exact hsmall.trans_le (min_le_right _ _))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hquad
  have hmul := mul_le_mul_of_nonneg_left hquad.le he.le
  have hquad' : (e * Real.log (1 / e)) ^ 2 ≤ e := by nlinarith only [hmul]
  have hCquad := mul_le_mul_of_nonneg_left hquad' hC₂
  nlinarith only [hb, hCquad]

theorem oldParameterAuxiliaryBound_strict_improvement :
    ∃ rho : ℝ, 0 < rho ∧ ∀ e : ℝ, 0 < e → e < rho →
      oldParameterAuxiliaryBound (oldPoint + e • ((1 : ℝ) / 2, 1)) <
        oldParameterAuxiliaryBound oldPoint := by
  obtain ⟨rho, C, hrho, hC, hbound⟩ := oldParameterAuxiliaryBound_log_variation
  refine ⟨min rho (Real.exp (-(C + 1))), by positivity, ?_⟩
  intro e he hsmall
  have hb := (abs_le.mp (hbound e he (hsmall.trans_le (min_le_left _ _)))).2
  have hlog : C + 1 < Real.log (1 / e) := by
    have hl := Real.log_lt_log he (hsmall.trans_le (min_le_right _ _))
    rw [Real.log_exp] at hl
    rw [one_div, Real.log_inv]
    linarith
  have hK : 1 < oldK := by linarith [oldK_enclosure.1]
  have hKe : e < oldK * e := by nlinarith
  have hmain := mul_lt_mul_of_pos_right hKe (show 0 < Real.log (1 / e) by linarith)
  nlinarith

theorem oldPoint_perturbation_admissible {e : ℝ} (he : 0 < e) (he1 : e < 1 / 30) :
    Admissible (oldPoint + e • ((1 : ℝ) / 2, 1)) := by
  dsimp [Admissible, oldPoint]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem oldPoint_improvement_neighborhood :
    ∃ rho : ℝ, 0 < rho ∧ ∀ e : ℝ, 0 < e → e < rho →
      Admissible (oldPoint + e • ((1 : ℝ) / 2, 1)) ∧
      0 < -oldParameterIntegralRate (oldPoint + e • ((1 : ℝ) / 2, 1)) -
        parameterCost (oldPoint + e • ((1 : ℝ) / 2, 1)) ∧
      oldParameterAuxiliaryBound (oldPoint + e • ((1 : ℝ) / 2, 1)) <
        oldParameterAuxiliaryBound oldPoint := by
  obtain ⟨rho, hrho, himprove⟩ := oldParameterAuxiliaryBound_strict_improvement
  have hcost : ContinuousAt parameterCost oldPoint := by
    apply ContinuousAt.sub (f := parameterSmoothCost)
    · unfold parameterSmoothCost
      fun_prop
    · exact continuousAt_savingPhi (by norm_num [oldPoint]) (by norm_num [oldPoint])
        (by norm_num [oldPoint])
  have hcont : ContinuousAt
      (fun p => -oldParameterIntegralRate p - parameterCost p) oldPoint :=
    analyticAt_oldParameterIntegralRate.continuousAt.neg.sub hcost
  have hden : ∀ᶠ p in 𝓝 oldPoint, 0 < -oldParameterIntegralRate p - parameterCost p := by
    apply hcont.eventually_const_lt
    dsimp only
    rw [oldParameterIntegralRate_at]
    change 0 < oldTau
    linarith [oldTau_enclosure.1]
  obtain ⟨delta, hdelta, hball⟩ := Metric.eventually_nhds_iff.mp hden
  refine ⟨min rho (min (delta / 2) (1 / 30)), by positivity, ?_⟩
  intro e he hsmall
  have he_rho := hsmall.trans_le (min_le_left _ _)
  have he_delta := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have he30 := hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨oldPoint_perturbation_admissible he he30, ?_, himprove e he he_rho⟩
  apply hball
  rw [dist_eq_norm, add_sub_cancel_left]
  have hn := norm_le_parameterNormOne (e • ((1 : ℝ) / 2, 1))
  rw [parameterNormOne_smul, abs_of_pos he] at hn
  rw [show parameterNormOne ((1 : ℝ) / 2, 1) = 3 / 2 by norm_num [parameterNormOne]] at hn
  linarith

end PiIrrationality
