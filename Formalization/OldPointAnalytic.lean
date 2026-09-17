import Formalization.OldPointSaddles

/-! Actual analytic real and complex saddle branches at the old point. -/

namespace PiIrrationality

open Filter
open scoped Topology ContDiff

theorem oldPoint_real_analytic_branch :
    ∃ g : ℝ × ℝ → ℝ, g oldPoint = oldStationaryRoot ∧ AnalyticAt ℝ g oldPoint ∧
      ∀ᶠ p in 𝓝 oldPoint, parameterStationary p (g p) = 0 ∧ 25 < g p := by
  have hd : 0 < parameterStationaryDerivative oldPoint oldStationaryRoot := by
    have he : 3 * parameterStationaryDerivative oldPoint oldStationaryRoot =
        6 * oldStationaryRoot ^ 2 - 250 * oldStationaryRoot - 500 := by
      dsimp [parameterStationaryDerivative, oldPoint]
      ring
    linarith [oldStationaryRoot_simple]
  obtain ⟨g, hg, hga, hroot⟩ := exists_analytic_scalar_implicit
    (analyticAt_parameterStationary oldPoint oldStationaryRoot)
    (parameterStationary_hasDerivAt oldPoint oldStationaryRoot) hd.ne'
  refine ⟨g, hg, hga, ?_⟩
  have hy : 25 < g oldPoint := by rw [hg]; linarith [oldStationaryRoot_coarse.1]
  have hnear := hga.continuousAt.eventually_const_lt hy
  filter_upwards [hroot, hnear] with p hp hyp
  refine ⟨?_, hyp⟩
  have hz : parameterStationary oldPoint oldStationaryRoot = 0 := by
    have h := oldPoint_stationary oldStationaryRoot
    rw [oldStationaryRoot_spec.2] at h
    linarith
  simpa only [hz] using hp

noncomputable def oldParameterRealSaddle : ℝ × ℝ → ℝ :=
  oldPoint_real_analytic_branch.choose

theorem oldParameterRealSaddle_at : oldParameterRealSaddle oldPoint = oldStationaryRoot :=
  oldPoint_real_analytic_branch.choose_spec.1

theorem analyticAt_oldParameterRealSaddle : AnalyticAt ℝ oldParameterRealSaddle oldPoint :=
  oldPoint_real_analytic_branch.choose_spec.2.1

theorem oldParameterRealSaddle_near : ∀ᶠ p in 𝓝 oldPoint,
    parameterStationary p (oldParameterRealSaddle p) = 0 ∧ 25 < oldParameterRealSaddle p :=
  oldPoint_real_analytic_branch.choose_spec.2.2

noncomputable def oldParameterSaddleU (p : ℝ × ℝ) : ℝ :=
  ((19 * p.1 + 44 * p.2 + 6) / (p.1 + 2 * p.2 - 1) - oldParameterRealSaddle p) / 2

noncomputable def oldParameterSaddleNormSq (p : ℝ × ℝ) : ℝ :=
  625 * p.1 / ((p.1 + 2 * p.2 - 1) * oldParameterRealSaddle p)

noncomputable def oldParameterSaddleVSq (p : ℝ × ℝ) : ℝ :=
  oldParameterSaddleNormSq p - oldParameterSaddleU p ^ 2

noncomputable def oldParameterComplexSaddle (p : ℝ × ℝ) : ℂ :=
  (oldParameterSaddleU p : ℂ) + (Real.sqrt (oldParameterSaddleVSq p) : ℂ) * Complex.I

theorem oldParameterSaddleU_at : oldParameterSaddleU oldPoint = oldSaddleU := by
  rw [oldParameterSaddleU, oldParameterRealSaddle_at]
  norm_num [oldPoint, oldSaddleU]

theorem oldParameterSaddleNormSq_at : oldParameterSaddleNormSq oldPoint = oldSaddleNormSq := by
  rw [oldParameterSaddleNormSq, oldParameterRealSaddle_at]
  norm_num [oldPoint, oldSaddleNormSq]
  ring

theorem oldParameterSaddleVSq_at : oldParameterSaddleVSq oldPoint = oldSaddleVSq := by
  rw [oldParameterSaddleVSq, oldParameterSaddleU_at, oldParameterSaddleNormSq_at]
  rfl

theorem oldParameterComplexSaddle_at : oldParameterComplexSaddle oldPoint = oldSaddleUpper := by
  rw [oldParameterComplexSaddle, oldParameterSaddleU_at, oldParameterSaddleVSq_at]
  rfl

theorem contDiffAt_oldParameterSaddleU : ContDiffAt ℝ ω oldParameterSaddleU oldPoint := by
  have hA : ContDiffAt ℝ ω (fun p : ℝ × ℝ => p.1 + 2 * p.2 - 1) oldPoint := by fun_prop
  have hB : ContDiffAt ℝ ω (fun p : ℝ × ℝ => 19 * p.1 + 44 * p.2 + 6) oldPoint := by fun_prop
  have hA0 : oldPoint.1 + 2 * oldPoint.2 - 1 ≠ 0 := by norm_num [oldPoint]
  exact ((hB.div hA hA0).sub analyticAt_oldParameterRealSaddle.contDiffAt).div_const 2

theorem contDiffAt_oldParameterSaddleNormSq : ContDiffAt ℝ ω oldParameterSaddleNormSq oldPoint := by
  have hA : ContDiffAt ℝ ω (fun p : ℝ × ℝ => p.1 + 2 * p.2 - 1) oldPoint := by fun_prop
  have hD : ContDiffAt ℝ ω (fun p : ℝ × ℝ => 625 * p.1) oldPoint := by fun_prop
  have hA0 : oldPoint.1 + 2 * oldPoint.2 - 1 ≠ 0 := by norm_num [oldPoint]
  have hr0 : oldParameterRealSaddle oldPoint ≠ 0 := by
    rw [oldParameterRealSaddle_at]
    exact oldStationaryRoot_spec.1.ne'
  exact hD.div (hA.mul analyticAt_oldParameterRealSaddle.contDiffAt) (mul_ne_zero hA0 hr0)

theorem contDiffAt_oldParameterSaddleVSq : ContDiffAt ℝ ω oldParameterSaddleVSq oldPoint :=
  contDiffAt_oldParameterSaddleNormSq.sub (contDiffAt_oldParameterSaddleU.pow 2)

theorem analyticAt_oldParameterComplexSaddle : AnalyticAt ℝ oldParameterComplexSaddle oldPoint := by
  have hU : ContDiffAt ℝ ω (fun p => (oldParameterSaddleU p : ℂ)) oldPoint :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp oldPoint contDiffAt_oldParameterSaddleU
  have hV : ContDiffAt ℝ ω (fun p => (Real.sqrt (oldParameterSaddleVSq p) : ℂ)) oldPoint :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp oldPoint (contDiffAt_oldParameterSaddleVSq.sqrt
      (by rw [oldParameterSaddleVSq_at]; exact oldSaddleVSq_pos.ne'))
  exact (hU.add (hV.mul contDiffAt_const)).analyticAt

theorem oldParameterSaddle_coefficients {p : ℝ × ℝ}
    (hA : p.1 + 2 * p.2 - 1 ≠ 0) (hr : oldParameterRealSaddle p ≠ 0)
    (hroot : parameterStationary p (oldParameterRealSaddle p) = 0) :
    (p.1 + 2 * p.2 - 1) * (2 * oldParameterSaddleU p + oldParameterRealSaddle p) =
        19 * p.1 + 44 * p.2 + 6 ∧
    (p.1 + 2 * p.2 - 1) *
        (oldParameterSaddleNormSq p + 2 * oldParameterRealSaddle p * oldParameterSaddleU p) =
        -(125 * p.1 + 150 * p.2 + 25) ∧
    (p.1 + 2 * p.2 - 1) * oldParameterRealSaddle p * oldParameterSaddleNormSq p = 625 * p.1 := by
  have hsum : (p.1 + 2 * p.2 - 1) *
      (2 * oldParameterSaddleU p + oldParameterRealSaddle p) = 19 * p.1 + 44 * p.2 + 6 := by
    unfold oldParameterSaddleU
    field_simp
    ring
  have hprod : (p.1 + 2 * p.2 - 1) * oldParameterRealSaddle p * oldParameterSaddleNormSq p =
      625 * p.1 := by
    unfold oldParameterSaddleNormSq
    field_simp
  refine ⟨hsum, ?_, hprod⟩
  apply mul_left_cancel₀ hr
  have hs := congrArg (fun t : ℝ => t * oldParameterRealSaddle p ^ 2) hsum
  unfold parameterStationary at hroot
  nlinarith only [hs, hprod, hroot]

theorem oldParameterComplexSaddle_near : ∀ᶠ p in 𝓝 oldPoint,
    parameterStationaryComplex p (oldParameterComplexSaddle p) = 0 ∧
      0 < (oldParameterComplexSaddle p).im := by
  have hA : ∀ᶠ p : ℝ × ℝ in 𝓝 oldPoint, 0 < p.1 + 2 * p.2 - 1 := by
    have h : ContinuousAt (fun p : ℝ × ℝ => p.1 + 2 * p.2 - 1) oldPoint := by fun_prop
    exact h.eventually_const_lt (by norm_num [oldPoint])
  have hV : ∀ᶠ p in 𝓝 oldPoint, 0 < oldParameterSaddleVSq p :=
    contDiffAt_oldParameterSaddleVSq.continuousAt.eventually_const_lt
      (by rw [oldParameterSaddleVSq_at]; exact oldSaddleVSq_pos)
  filter_upwards [hA, hV, oldParameterRealSaddle_near] with p hAp hVp hrp
  have hcoeff := oldParameterSaddle_coefficients hAp.ne' (by linarith [hrp.2]) hrp.1
  have hfac (z : ℂ) : parameterStationaryComplex p z =
      ((p.1 + 2 * p.2 - 1 : ℝ) : ℂ) * (z - (oldParameterRealSaddle p : ℂ)) *
        (z ^ 2 - 2 * (oldParameterSaddleU p : ℂ) * z + (oldParameterSaddleNormSq p : ℂ)) := by
    have hs := congrArg Complex.ofReal hcoeff.1
    have hp := congrArg Complex.ofReal hcoeff.2.1
    have hn := congrArg Complex.ofReal hcoeff.2.2
    push_cast at hs hp hn
    unfold parameterStationaryComplex
    push_cast
    linear_combination z ^ 2 * hs - z * hp + hn
  have hquad : oldParameterComplexSaddle p ^ 2 -
      2 * (oldParameterSaddleU p : ℂ) * oldParameterComplexSaddle p +
        (oldParameterSaddleNormSq p : ℂ) = 0 := by
    have hv := Real.sq_sqrt hVp.le
    change Real.sqrt (oldParameterSaddleVSq p) ^ 2 =
      oldParameterSaddleNormSq p - oldParameterSaddleU p ^ 2 at hv
    apply Complex.ext <;> simp [oldParameterComplexSaddle, pow_two]
    · nlinarith only [hv]
    · ring
  refine ⟨by rw [hfac, hquad, mul_zero], ?_⟩
  simpa [oldParameterComplexSaddle] using Real.sqrt_pos.mpr hVp

noncomputable def oldParameterCoefficientRate (p : ℝ × ℝ) : ℝ :=
  complexPhase p.1 p.2 (oldParameterRealSaddle p : ℂ)

noncomputable def oldParameterIntegralRate (p : ℝ × ℝ) : ℝ :=
  complexPhase p.1 p.2 (oldParameterComplexSaddle p)

theorem oldParameterCoefficientRate_at : oldParameterCoefficientRate oldPoint = oldCoefficientRate := by
  rw [oldParameterCoefficientRate, oldParameterRealSaddle_at]
  rfl

theorem oldParameterIntegralRate_at : oldParameterIntegralRate oldPoint = oldIntegralRate := by
  rw [oldParameterIntegralRate, oldParameterComplexSaddle_at]
  rfl

theorem analyticAt_oldParameterCoefficientRate : AnalyticAt ℝ oldParameterCoefficientRate oldPoint := by
  have hy : AnalyticAt ℝ (fun p => (oldParameterRealSaddle p : ℂ)) oldPoint :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp oldPoint
      analyticAt_oldParameterRealSaddle.contDiffAt).analyticAt
  apply analyticAt_complexPhase_comp hy
  all_goals rw [oldParameterRealSaddle_at]
  · exact_mod_cast oldStationaryRoot_spec.1.ne'
  · have h : (oldStationaryRoot : ℂ) ^ 2 + 6 * oldStationaryRoot + 25 =
        ((oldStationaryRoot ^ 2 + 6 * oldStationaryRoot + 25 : ℝ) : ℂ) := by push_cast; rfl
    rw [h]
    exact_mod_cast (show oldStationaryRoot ^ 2 + 6 * oldStationaryRoot + 25 ≠ 0 by
      nlinarith [oldStationaryRoot_spec.1])
  · have h : (25 : ℂ) - oldStationaryRoot = ((25 - oldStationaryRoot : ℝ) : ℂ) := by push_cast; rfl
    rw [h]
    exact_mod_cast (show (25 : ℝ) - oldStationaryRoot ≠ 0 by linarith [oldStationaryRoot_coarse.1])

theorem analyticAt_oldParameterIntegralRate : AnalyticAt ℝ oldParameterIntegralRate oldPoint := by
  apply analyticAt_complexPhase_comp analyticAt_oldParameterComplexSaddle
  all_goals rw [oldParameterComplexSaddle_at]
  · intro he
    have h := oldSaddleUpper_im_pos
    rw [he, Complex.zero_im] at h
    linarith
  · intro he
    have h : 0 < oldSaddleQuadraticNormSq := by
      rw [oldSaddleQuadraticNormSq_formula]
      positivity [oldStationaryRoot_spec.1]
    unfold oldSaddleQuadraticNormSq at h
    rw [he, Complex.normSq_zero] at h
    linarith
  · intro he
    have h : 0 < oldSaddlePoleNormSq := by
      rw [oldSaddlePoleNormSq_formula]
      exact div_pos (by norm_num) (by linarith [oldStationaryRoot_coarse.1])
    unfold oldSaddlePoleNormSq at h
    rw [he, Complex.normSq_zero] at h
    linarith

end PiIrrationality
