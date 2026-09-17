import Formalization.IntegralDecay
import Formalization.IntegerCoefficientGrowth

/-! Growth and decay rates for the actual integer forms in (5.15)--(5.16). -/

namespace PiIrrationality

open Filter
open scoped Topology

noncomputable def paperSigma : ℝ :=
  coefficientGrowthRate + normalizationCost primeSavingSeries

noncomputable def paperTau : ℝ :=
  -integralDecayRate - normalizationCost primeSavingSeries

noncomputable def paperAuxiliaryValue : ℝ := 1 + paperSigma / paperTau

theorem paper_linearForm_abs (n : ℕ) (hn : 0 < n) :
    |linearForm Real.pi (integerCoeffU n) (integerCoeffV n)| =
      (normalizationMultiplier n : ℝ) * ‖paperIntegral n‖ := by
  have h := congrArg norm (paper_integerLinearForm n hn)
  rw [norm_mul] at h
  have hc : (normalizationMultiplier n : ℂ) =
      ((normalizationMultiplier n : ℝ) : ℂ) := by norm_cast
  have hL : (integerCoeffU n : ℂ) + (integerCoeffV n : ℂ) * (Real.pi : ℂ) =
      ((linearForm Real.pi (integerCoeffU n) (integerCoeffV n) : ℝ) : ℂ) := by
    unfold linearForm
    push_cast
    rfl
  rw [hc, hL, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (normalizationMultiplier_real_pos n)] at h
  exact h.symm

theorem paper_linearForm_log (n : ℕ) (hn : 0 < n) :
    Real.log |linearForm Real.pi (integerCoeffU n) (integerCoeffV n)| =
      Real.log (normalizationMultiplier n : ℝ) + Real.log ‖paperIntegral n‖ := by
  rw [paper_linearForm_abs n hn]
  exact Real.log_mul (normalizationMultiplier_real_pos n).ne'
    (norm_ne_zero_iff.mpr (paperIntegral_ne_zero n hn))

theorem paper_linearForm_log_upper (n : ℕ) (hn : 0 < n) :
    Real.log |linearForm Real.pi (integerCoeffU n) (integerCoeffV n)| /
        (5570 * (n : ℝ)) ≤
      Real.log (normalizationMultiplier n : ℝ) / (5570 * (n : ℝ)) + integralDecayRate +
        Real.log contourAmplitude / (5570 * (n : ℝ)) := by
  rw [paper_linearForm_log n hn, add_div]
  linarith [paperIntegral_log_upper n hn]

theorem paper_linearForm_log_upper_eventually {epsilon : ℝ} (he : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      Real.log |linearForm Real.pi (integerCoeffU n) (integerCoeffV n)| /
        (5570 * (n : ℝ)) < -paperTau + epsilon := by
  have hM := normalizationCost_limit.eventually
    (gt_mem_nhds (show normalizationCost primeSavingSeries <
      normalizationCost primeSavingSeries + epsilon / 2 by linarith))
  have hJ := paperIntegral_log_upper_eventually (show 0 < epsilon / 2 by linarith)
  filter_upwards [eventually_gt_atTop (0 : ℕ), hM, hJ] with n hn hm hj
  rw [paper_linearForm_log n hn, add_div]
  unfold paperTau
  linarith

theorem paper_linearForm_log_limsup :
    limsup (fun n : ℕ => ((Real.log |linearForm Real.pi (integerCoeffU n) (integerCoeffV n)| /
      (5570 * (n : ℝ)) : ℝ) : EReal)) atTop ≤ (-paperTau : ℝ) := by
  have hd : Tendsto (fun n : ℕ => 5570 * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have h : Tendsto (fun n : ℕ =>
      Real.log (normalizationMultiplier n : ℝ) / (5570 * (n : ℝ)) + integralDecayRate +
        Real.log contourAmplitude / (5570 * (n : ℝ))) atTop (𝓝 (-paperTau)) := by
    have hz : Tendsto (fun n : ℕ => Real.log contourAmplitude / (5570 * (n : ℝ)))
        atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds.div_atTop hd
    have ht := (normalizationCost_limit.add_const integralDecayRate).add hz
    have he : normalizationCost primeSavingSeries + integralDecayRate + 0 = -paperTau := by
      unfold paperTau
      ring
    rwa [he] at ht
  have hE := EReal.tendsto_coe.mpr h
  calc
    _ ≤ limsup (fun n : ℕ => ((Real.log (normalizationMultiplier n : ℝ) /
        (5570 * (n : ℝ)) + integralDecayRate +
          Real.log contourAmplitude / (5570 * (n : ℝ)) : ℝ) : EReal)) atTop := by
      refine limsup_le_limsup ?_
        (isCoboundedUnder_le_of_le atTop (fun _ => bot_le))
        ⟨⊤, Eventually.of_forall (fun _ => le_top)⟩
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      exact_mod_cast paper_linearForm_log_upper n hn
    _ = _ := hE.limsup_eq

theorem paper_integerCoeffV_log_limit :
    Tendsto (fun n : ℕ => Real.log |(integerCoeffV n : ℝ)| / (5570 * (n : ℝ)))
      atTop (𝓝 paperSigma) := integerCoeffV_log_limit

end PiIrrationality
