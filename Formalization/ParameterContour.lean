import Formalization.ParameterRates
import Formalization.ParameterSaddleRoots

/-! The parameter-dependent contour in (6.48)--(6.49). -/

namespace PiIrrationality

open Filter
open scoped Topology ContDiff

noncomputable def parameterSaddleZ (p : ℝ × ℝ) : ℂ :=
  saddleQ / parameterComplexSaddle p

noncomputable def parameterSaddleLambda (p : ℝ × ℝ) : ℝ :=
  1 / (parameterSaddleZ p).re

noncomputable def parameterSaddleEta (p : ℝ × ℝ) : ℝ :=
  -(parameterSaddleZ p).im / ((parameterSaddleZ p).re - 1)

theorem parameterSaddleZ_candidate :
    parameterSaddleZ candidate = (saddleX : ℂ) + (saddleY : ℂ) * Complex.I := by
  rw [parameterSaddleZ, parameterComplexSaddle_candidate]
  apply (div_eq_iff (Complex.slitPlane_ne_zero saddle_slitPlane_conditions.1)).mpr
  exact saddle_ratio_mul.symm

theorem parameterSaddleLambda_candidate : parameterSaddleLambda candidate = saddleLambda := by
  simp [parameterSaddleLambda, parameterSaddleZ_candidate, saddleLambda]

theorem parameterSaddleEta_candidate : parameterSaddleEta candidate = saddleEta := by
  simp [parameterSaddleEta, parameterSaddleZ_candidate, saddleEta]

theorem analyticAt_parameterSaddleZ : AnalyticAt ℝ parameterSaddleZ candidate := by
  have hy : parameterComplexSaddle candidate ≠ 0 := by
    rw [parameterComplexSaddle_candidate]
    exact Complex.slitPlane_ne_zero saddle_slitPlane_conditions.1
  have hc : ContDiffAt ℝ ω (fun _ : ℝ × ℝ => saddleQ) candidate := contDiffAt_const
  simpa only [parameterSaddleZ, div_eq_mul_inv, Pi.inv_apply] using!
    (hc.mul (analyticAt_parameterComplexSaddle.contDiffAt.inv hy)).analyticAt

theorem analyticAt_parameterSaddleLambda : AnalyticAt ℝ parameterSaddleLambda candidate := by
  have hx : ContDiffAt ℝ ω (fun p => (parameterSaddleZ p).re) candidate :=
    Complex.reCLM.contDiff.contDiffAt.comp candidate analyticAt_parameterSaddleZ.contDiffAt
  apply (contDiffAt_const.div hx ?_).analyticAt
  simpa [parameterSaddleZ_candidate] using saddleX_pos.ne'

theorem analyticAt_parameterSaddleEta : AnalyticAt ℝ parameterSaddleEta candidate := by
  have hx : ContDiffAt ℝ ω (fun p => (parameterSaddleZ p).re) candidate :=
    Complex.reCLM.contDiff.contDiffAt.comp candidate analyticAt_parameterSaddleZ.contDiffAt
  have hy : ContDiffAt ℝ ω (fun p => (parameterSaddleZ p).im) candidate :=
    Complex.imCLM.contDiff.contDiffAt.comp candidate analyticAt_parameterSaddleZ.contDiffAt
  apply (hy.neg.div (hx.sub contDiffAt_const) ?_).analyticAt
  simp only [parameterSaddleZ_candidate, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero,
    zero_mul, sub_zero, add_zero]
  linarith [saddleX_gt_one]

theorem gammaPath_ratio_identity {z : ℂ} (hx : z.re ≠ 0) (hxm : z.re - 1 ≠ 0) :
    gammaPath (-z.im / (z.re - 1)) (1 / z.re) = saddleQ / z := by
  have hxC : (z.re : ℂ) ≠ 0 := by exact_mod_cast hx
  have hxmC : (z.re : ℂ) - 1 ≠ 0 := by exact_mod_cast hxm
  have hz : z ≠ 0 := by intro h; apply hx; simp [h]
  have he : (z.re : ℂ) + (z.im : ℂ) * Complex.I = z := Complex.re_add_im z
  have hfactor :
      1 - Complex.I * ((-z.im / (z.re - 1) : ℝ) : ℂ) *
        (1 - ((1 / z.re : ℝ) : ℂ)) = z / (z.re : ℂ) := by
    calc
      _ = ((z.re : ℂ) + (z.im : ℂ) * Complex.I) / (z.re : ℂ) := by
        push_cast
        field_simp [hxC, hxmC]
        ring
      _ = z / (z.re : ℂ) := by rw [he]
  unfold gammaPath
  rw [hfactor]
  push_cast
  change saddleQ * (1 / (z.re : ℂ)) / (z / (z.re : ℂ)) = saddleQ / z
  field_simp [hxC, hz]

theorem parameterContour_near_candidate : ∀ᶠ p in 𝓝 candidate,
    (9 : ℝ) / 10 < parameterSaddleEta p ∧ parameterSaddleEta p < 23 / 25 ∧
    (12 : ℝ) / 25 < parameterSaddleLambda p ∧ parameterSaddleLambda p < 49 / 100 ∧
    gammaPath (parameterSaddleEta p) (parameterSaddleLambda p) = parameterComplexSaddle p := by
  have he0 : (9 : ℝ) / 10 < parameterSaddleEta candidate := by
    rw [parameterSaddleEta_candidate]
    exact saddleEta_gt_nine_tenths
  have he1 : parameterSaddleEta candidate < (23 : ℝ) / 25 := by
    rw [parameterSaddleEta_candidate]
    have h := saddleEta_paper_bounds.2
    dsimp [saddleEtaUpper] at h
    linarith
  have hl0 : (12 : ℝ) / 25 < parameterSaddleLambda candidate := by
    rw [parameterSaddleLambda_candidate]
    have h := saddleLambda_paper_bounds.1
    dsimp [saddleLambdaLower] at h
    linarith
  have hl1 : parameterSaddleLambda candidate < (49 : ℝ) / 100 := by
    rw [parameterSaddleLambda_candidate]
    have h := saddleLambda_paper_bounds.2
    dsimp [saddleLambdaUpper] at h
    linarith
  have hx : ∀ᶠ p in 𝓝 candidate, 1 < (parameterSaddleZ p).re := by
    have hc : ContinuousAt (fun p => (parameterSaddleZ p).re) candidate :=
      Complex.continuous_re.continuousAt.comp analyticAt_parameterSaddleZ.continuousAt
    exact hc.eventually_const_lt (by simpa [parameterSaddleZ_candidate] using saddleX_gt_one)
  filter_upwards [analyticAt_parameterSaddleEta.continuousAt.eventually_const_lt he0,
    analyticAt_parameterSaddleEta.continuousAt.eventually_lt_const he1,
    analyticAt_parameterSaddleLambda.continuousAt.eventually_const_lt hl0,
    analyticAt_parameterSaddleLambda.continuousAt.eventually_lt_const hl1, hx] with p he0 he1 hl0 hl1 hx
  refine ⟨he0, he1, hl0, hl1, ?_⟩
  rw [parameterSaddleEta, parameterSaddleLambda,
    gammaPath_ratio_identity (by linarith) (by linarith), parameterSaddleZ]
  have hq : saddleQ ≠ 0 := by norm_num [saddleQ, Complex.ext_iff]
  field_simp

theorem parameterContour_geometry_near_candidate : ∀ᶠ p in 𝓝 candidate,
    ∀ t : ℝ, t ∈ Set.Ioo 0 1 →
      0 < (gammaPath (parameterSaddleEta p) t).im ∧
      ‖gammaPath (parameterSaddleEta p) t‖ ≤ 5 ∧
      20 ≤ ‖25 - gammaPath (parameterSaddleEta p) t‖ := by
  filter_upwards [parameterContour_near_candidate] with p hp
  intro t ht
  have he : 0 < parameterSaddleEta p := by linarith [hp.1]
  have he1 : parameterSaddleEta p < 1 := by linarith [hp.2.1]
  have hn := gammaPath_norm_le_five (eta := parameterSaddleEta p) ht.1.le ht.2.le
  refine ⟨gammaPath_im_pos he.le (by linarith) ht.1 ht.2.le, hn, ?_⟩
  have h := norm_sub_norm_le (25 : ℂ) (gammaPath (parameterSaddleEta p) t)
  norm_num at h
  linarith

end PiIrrationality
