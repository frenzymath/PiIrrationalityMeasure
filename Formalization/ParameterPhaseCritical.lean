import Formalization.ParameterContour

/-! Stationarity of the actual phase on the parameter-dependent contour. -/

namespace PiIrrationality

open Filter
open scoped Topology

theorem parameterPhaseSlope_cleared (p : ℝ × ℝ) {z : ℂ} (hz : z ≠ 0)
    (hq : z ^ 2 + 6 * z + 25 ≠ 0) (hp : 25 - z ≠ 0) :
    -z * (z ^ 2 + 6 * z + 25) * (25 - z) * complexPhaseSlope p.1 p.2 z =
      parameterStationaryComplex p z := by
  unfold complexPhaseSlope parameterStationaryComplex
  push_cast
  have hq' : 25 + z * 6 + z ^ 2 ≠ 0 := by convert! hq using 1 <;> ring
  rw [show z ^ 2 + 6 * z + 25 = 25 + z * 6 + z ^ 2 by ring]
  field_simp [hz, hq, hq', hp]
  ring

theorem parameterSaddle_slitPlane_near_candidate : ∀ᶠ p in 𝓝 candidate,
    parameterComplexSaddle p ∈ Complex.slitPlane ∧
    parameterComplexSaddle p ^ 2 + 6 * parameterComplexSaddle p + 25 ∈ Complex.slitPlane ∧
    25 - parameterComplexSaddle p ∈ Complex.slitPlane := by
  have hc := analyticAt_parameterComplexSaddle.continuousAt
  have hq : ContinuousAt
      (fun p => parameterComplexSaddle p ^ 2 + 6 * parameterComplexSaddle p + 25) candidate := by
    fun_prop
  have hp : ContinuousAt (fun p => 25 - parameterComplexSaddle p) candidate := by fun_prop
  have hz0 : parameterComplexSaddle candidate ∈ Complex.slitPlane := by
    rw [parameterComplexSaddle_candidate]; exact saddle_slitPlane_conditions.1
  have hq0 : parameterComplexSaddle candidate ^ 2 + 6 * parameterComplexSaddle candidate + 25 ∈
      Complex.slitPlane := by
    rw [parameterComplexSaddle_candidate]; exact saddle_slitPlane_conditions.2.1
  have hp0 : 25 - parameterComplexSaddle candidate ∈ Complex.slitPlane := by
    rw [parameterComplexSaddle_candidate]; exact saddle_slitPlane_conditions.2.2
  exact (hc.eventually (Complex.isOpen_slitPlane.mem_nhds hz0)).and
    ((hq.eventually (Complex.isOpen_slitPlane.mem_nhds hq0)).and
      (hp.eventually (Complex.isOpen_slitPlane.mem_nhds hp0)))

theorem parameterHolomorphicPhase_stationary_near_candidate : ∀ᶠ p in 𝓝 candidate,
    HasDerivAt (holomorphicPhase p.1 p.2) 0 (parameterComplexSaddle p) := by
  filter_upwards [parameterSaddle_slitPlane_near_candidate,
    parameterComplexSaddle_near_candidate] with p hp hroot
  obtain ⟨hz, hq, hp⟩ := hp
  have hz' := Complex.slitPlane_ne_zero hz
  have hq' := Complex.slitPlane_ne_zero hq
  have hp' := Complex.slitPlane_ne_zero hp
  have h := parameterPhaseSlope_cleared p hz' hq' hp'
  rw [hroot.1] at h
  have hslope : complexPhaseSlope p.1 p.2 (parameterComplexSaddle p) = 0 :=
    (mul_eq_zero.mp h).resolve_left
      (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hz') hq') hp')
  simpa only [hslope] using holomorphicPhase_hasDerivAt p.1 p.2 hz hq hp

theorem parameterArcPhase_stationary_near_candidate : ∀ᶠ p in 𝓝 candidate,
    HasDerivAt (fun t => complexPhase p.1 p.2 (gammaPath (parameterSaddleEta p) t))
      0 (parameterSaddleLambda p) := by
  filter_upwards [parameterHolomorphicPhase_stationary_near_candidate,
    parameterContour_near_candidate] with p hF hp
  rw [← hp.2.2.2.2] at hF
  have h := hF.scomp (parameterSaddleLambda p)
    (gammaPath_hasDerivAt (parameterSaddleEta p) (parameterSaddleLambda p))
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (parameterSaddleLambda p) h
  simpa only [Function.comp_def, smul_zero, Complex.reCLM_apply, Complex.zero_re,
    holomorphicPhase_re] using hr

end PiIrrationality
