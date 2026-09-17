import Formalization.ParameterComplexSaddle
import Formalization.RealSaddlePhase
import Formalization.IntegralDecay

/-! The actual two phase-rate functions (6.8), their regularity, and candidate values. -/

namespace PiIrrationality

open scoped ContDiff

noncomputable def parameterCoefficientRate (p : ℝ × ℝ) : ℝ :=
  complexPhase p.1 p.2 (parameterRealSaddle p : ℂ)

noncomputable def parameterIntegralRate (p : ℝ × ℝ) : ℝ :=
  complexPhase p.1 p.2 (parameterComplexSaddle p)

theorem analyticAt_complexPhase_comp {y : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (hy : AnalyticAt ℝ y p) (hy0 : y p ≠ 0)
    (hq0 : y p ^ 2 + 6 * y p + 25 ≠ 0) (hp0 : 25 - y p ≠ 0) :
    AnalyticAt ℝ (fun q => complexPhase q.1 q.2 (y q)) p := by
  have hc : ContDiffAt ℝ ω y p := hy.contDiffAt
  have hq : ContDiffAt ℝ ω (fun q => y q ^ 2 + 6 * y q + 25) p := by fun_prop
  have hp : ContDiffAt ℝ ω (fun q => 25 - y q) p := by fun_prop
  have hl := (hc.norm ℂ hy0).log (norm_ne_zero_iff.mpr hy0)
  have hlq := (hq.norm ℂ hq0).log (norm_ne_zero_iff.mpr hq0)
  have hlp := (hp.norm ℂ hp0).log (norm_ne_zero_iff.mpr hp0)
  have hfst : ContDiffAt ℝ ω (fun q : ℝ × ℝ => q.1) p := by fun_prop
  have hsnd : ContDiffAt ℝ ω (fun q : ℝ × ℝ => q.2) p := by fun_prop
  exact ((hfst.mul hl).add (hsnd.mul hlq) |>.sub hlp).analyticAt

theorem parameterCoefficientRate_candidate :
    parameterCoefficientRate candidate = coefficientGrowthRate := by
  rw [parameterCoefficientRate, parameterRealSaddle_candidate]
  convert realSaddle_phase_eq_coefficientGrowthRate using 1 <;> norm_num [candidate]

theorem parameterIntegralRate_candidate : parameterIntegralRate candidate = integralDecayRate := by
  rw [parameterIntegralRate, parameterComplexSaddle_candidate]
  unfold integralDecayRate
  congr 1 <;> norm_num [candidate]

theorem analyticAt_parameterCoefficientRate : AnalyticAt ℝ parameterCoefficientRate candidate := by
  have hy : AnalyticAt ℝ (fun p => (parameterRealSaddle p : ℂ)) candidate :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp candidate
      analyticAt_parameterRealSaddle.contDiffAt).analyticAt
  apply analyticAt_complexPhase_comp hy
  · rw [parameterRealSaddle_candidate]
    exact_mod_cast stationaryRoot_pos.ne'
  · rw [parameterRealSaddle_candidate]
    have he : (stationaryRoot : ℂ) ^ 2 + 6 * stationaryRoot + 25 =
        ((stationaryRoot ^ 2 + 6 * stationaryRoot + 25 : ℝ) : ℂ) := by push_cast; rfl
    rw [he]
    exact_mod_cast (show (0 : ℝ) < stationaryRoot ^ 2 + 6 * stationaryRoot + 25 by
      nlinarith [stationaryRoot_pos]).ne'
  · rw [parameterRealSaddle_candidate]
    have he : (25 : ℂ) - stationaryRoot = ((25 - stationaryRoot : ℝ) : ℂ) := by push_cast; rfl
    rw [he]
    exact_mod_cast (show (25 : ℝ) - stationaryRoot ≠ 0 by linarith [stationaryRoot_mem.1])

theorem analyticAt_parameterIntegralRate : AnalyticAt ℝ parameterIntegralRate candidate := by
  apply analyticAt_complexPhase_comp analyticAt_parameterComplexSaddle
  all_goals rw [parameterComplexSaddle_candidate]
  · exact Complex.slitPlane_ne_zero saddle_slitPlane_conditions.1
  · exact Complex.slitPlane_ne_zero saddle_slitPlane_conditions.2.1
  · exact Complex.slitPlane_ne_zero saddle_slitPlane_conditions.2.2

end PiIrrationality
