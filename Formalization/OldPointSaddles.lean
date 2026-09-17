import Formalization.OldPointRoot
import Formalization.ParameterRates

/-! The actual old complex saddle and the squared-modulus identities in (A.28). -/

namespace PiIrrationality

noncomputable def oldSaddleU : ℝ := (125 / 2 - oldStationaryRoot) / 2
noncomputable def oldSaddleNormSq : ℝ := 625 / (2 * oldStationaryRoot)
noncomputable def oldSaddleVSq : ℝ := oldSaddleNormSq - oldSaddleU ^ 2
noncomputable def oldSaddleV : ℝ := Real.sqrt oldSaddleVSq
noncomputable def oldSaddleUpper : ℂ := (oldSaddleU : ℂ) + (oldSaddleV : ℂ) * Complex.I

theorem oldStationaryRoot_coarse : 66 < oldStationaryRoot ∧ oldStationaryRoot < 133 / 2 := by
  obtain ⟨hL, hU⟩ := oldStationaryRoot_isolation
  norm_num [oldRootLower, oldRootUpper] at hL hU
  constructor <;> linarith

theorem oldSaddleU_bounds : -2 < oldSaddleU ∧ oldSaddleU < 0 := by
  unfold oldSaddleU
  constructor <;> linarith [oldStationaryRoot_coarse.1, oldStationaryRoot_coarse.2]

theorem oldSaddleNormSq_gt : 4 < oldSaddleNormSq := by
  unfold oldSaddleNormSq
  apply (lt_div_iff₀ (by linarith [oldStationaryRoot_spec.1])).mpr
  linarith [oldStationaryRoot_coarse.2]

theorem oldSaddleVSq_pos : 0 < oldSaddleVSq := by
  have hU := oldSaddleU_bounds
  have hU2 : oldSaddleU ^ 2 < 4 := by
    nlinarith [mul_pos (show 0 < oldSaddleU + 2 by linarith) (neg_pos.mpr hU.2)]
  unfold oldSaddleVSq
  linarith [oldSaddleNormSq_gt]

theorem oldSaddleV_sq : oldSaddleV ^ 2 = oldSaddleVSq := Real.sq_sqrt oldSaddleVSq_pos.le

theorem oldSaddleUpper_im_pos : 0 < oldSaddleUpper.im := by
  simpa [oldSaddleUpper, oldSaddleV] using Real.sqrt_pos.mpr oldSaddleVSq_pos

theorem oldSaddle_coefficients :
    oldStationaryRoot + 2 * oldSaddleU = 125 / 2 ∧
    2 * oldSaddleU * oldStationaryRoot + oldSaddleNormSq = -250 ∧
    oldStationaryRoot * oldSaddleNormSq = 625 / 2 := by
  refine ⟨by dsimp [oldSaddleU]; ring, ?_, ?_⟩
  · have h : oldStationaryRoot *
        (2 * oldSaddleU * oldStationaryRoot + oldSaddleNormSq + 250) =
          -oldStationaryCubic oldStationaryRoot / 2 := by
      unfold oldSaddleU oldSaddleNormSq oldStationaryCubic
      field_simp [oldStationaryRoot_spec.1.ne']
      ring
    rw [oldStationaryRoot_spec.2] at h
    have hz : 2 * oldSaddleU * oldStationaryRoot + oldSaddleNormSq + 250 = 0 :=
      (mul_eq_zero.mp (by simpa using h)).resolve_left oldStationaryRoot_spec.1.ne'
    linarith
  · unfold oldSaddleNormSq
    field_simp [oldStationaryRoot_spec.1.ne']

theorem oldStationaryComplex_factorization (z : ℂ) :
    parameterStationaryComplex oldPoint z = (2 / 3 : ℂ) *
      (z - (oldStationaryRoot : ℂ)) * (z - oldSaddleUpper) * (z - star oldSaddleUpper) := by
  have hq : (z - oldSaddleUpper) * (z - star oldSaddleUpper) =
      z ^ 2 - 2 * (oldSaddleU : ℂ) * z + (oldSaddleNormSq : ℂ) := by
    have hv := oldSaddleV_sq
    unfold oldSaddleVSq at hv
    apply Complex.ext <;> simp [oldSaddleUpper, pow_two]
    · nlinarith only [hv]
    · ring
  rw [mul_assoc ((2 / 3 : ℂ) * (z - (oldStationaryRoot : ℂ))), hq]
  obtain ⟨hS, hP, hN⟩ := oldSaddle_coefficients
  have hs := congrArg Complex.ofReal hS
  have hp := congrArg Complex.ofReal hP
  have hn := congrArg Complex.ofReal hN
  push_cast at hs hp hn
  dsimp [parameterStationaryComplex, oldPoint]
  push_cast
  linear_combination (2 / 3 : ℂ) * z ^ 2 * hs - (2 / 3 : ℂ) * z * hp + (2 / 3 : ℂ) * hn

theorem oldSaddleUpper_stationary : parameterStationaryComplex oldPoint oldSaddleUpper = 0 := by
  rw [oldStationaryComplex_factorization]
  simp

theorem oldSaddleUpper_unique {z : ℂ} (hz : parameterStationaryComplex oldPoint z = 0)
    (hi : 0 < z.im) : z = oldSaddleUpper := by
  rw [oldStationaryComplex_factorization] at hz
  have hlead : (2 / 3 : ℂ) ≠ 0 := by norm_num
  simp only [mul_eq_zero, hlead, false_or, sub_eq_zero] at hz
  rcases hz with (hr | hu) | hl
  · rw [hr, Complex.ofReal_im] at hi
    exact (lt_irrefl _ hi).elim
  · exact hu
  · rw [hl] at hi
    simp only [Complex.star_def, Complex.conj_im] at hi
    linarith [oldSaddleUpper_im_pos]

theorem oldSaddleUpper_normSq : Complex.normSq oldSaddleUpper = oldSaddleNormSq := by
  have hv := oldSaddleV_sq
  unfold oldSaddleVSq at hv
  simp [oldSaddleUpper, Complex.normSq_apply]
  nlinarith

noncomputable def oldSaddleQuadraticNormSq : ℝ :=
  Complex.normSq (oldSaddleUpper ^ 2 + 6 * oldSaddleUpper + 25)

noncomputable def oldSaddlePoleNormSq : ℝ := Complex.normSq (25 - oldSaddleUpper)

theorem oldSaddleQuadraticNormSq_eq :
    oldSaddleQuadraticNormSq = oldSaddleNormSq ^ 2 + 12 * oldSaddleU * oldSaddleNormSq +
      100 * oldSaddleU ^ 2 + 300 * oldSaddleU - 14 * oldSaddleNormSq + 625 := by
  have h : oldSaddleQuadraticNormSq = (oldSaddleU ^ 2 + oldSaddleV ^ 2) ^ 2 +
      12 * oldSaddleU * (oldSaddleU ^ 2 + oldSaddleV ^ 2) +
      100 * oldSaddleU ^ 2 + 300 * oldSaddleU - 14 * (oldSaddleU ^ 2 + oldSaddleV ^ 2) + 625 := by
    simp [oldSaddleQuadraticNormSq, oldSaddleUpper, Complex.normSq_apply, pow_two]
    ring
  have hv : oldSaddleU ^ 2 + oldSaddleV ^ 2 = oldSaddleNormSq := by
    have hv := oldSaddleV_sq
    unfold oldSaddleVSq at hv
    linarith
  rwa [hv] at h

theorem oldSaddlePoleNormSq_eq :
    oldSaddlePoleNormSq = 625 - 50 * oldSaddleU + oldSaddleNormSq := by
  have h : oldSaddlePoleNormSq = 625 - 50 * oldSaddleU + oldSaddleU ^ 2 + oldSaddleV ^ 2 := by
    simp [oldSaddlePoleNormSq, oldSaddleUpper, Complex.normSq_apply]
    ring
  have hv := oldSaddleV_sq
  unfold oldSaddleVSq at hv
  linarith

theorem oldSaddleQuadraticNormSq_formula :
    oldSaddleQuadraticNormSq = 1280000 /
      (oldStationaryRoot ^ 2 + 6 * oldStationaryRoot + 25) := by
  have h : oldStationaryRoot ^ 2 *
      (oldSaddleQuadraticNormSq * (oldStationaryRoot ^ 2 + 6 * oldStationaryRoot + 25) -
        1280000) = (25 / 4 : ℝ) * oldStationaryCubic oldStationaryRoot *
          (oldStationaryCubic oldStationaryRoot + 128 * oldStationaryRoot) := by
    rw [oldSaddleQuadraticNormSq_eq]
    unfold oldSaddleU oldSaddleNormSq oldStationaryCubic
    field_simp [oldStationaryRoot_spec.1.ne']
    ring
  rw [oldStationaryRoot_spec.2, mul_zero, zero_mul] at h
  have hz := sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left
    (pow_ne_zero 2 oldStationaryRoot_spec.1.ne'))
  exact (eq_div_iff (by nlinarith [oldStationaryRoot_spec.1] :
    oldStationaryRoot ^ 2 + 6 * oldStationaryRoot + 25 ≠ 0)).mpr hz

theorem oldSaddlePoleNormSq_formula :
    oldSaddlePoleNormSq = 30000 / (oldStationaryRoot - 25) := by
  have h : oldStationaryRoot * (oldSaddlePoleNormSq * (oldStationaryRoot - 25) - 30000) =
      (25 / 2 : ℝ) * oldStationaryCubic oldStationaryRoot := by
    rw [oldSaddlePoleNormSq_eq]
    unfold oldSaddleU oldSaddleNormSq oldStationaryCubic
    field_simp [oldStationaryRoot_spec.1.ne']
    ring
  rw [oldStationaryRoot_spec.2, mul_zero] at h
  have hz := sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left oldStationaryRoot_spec.1.ne')
  exact (eq_div_iff (by linarith [oldStationaryRoot_coarse.1] : oldStationaryRoot - 25 ≠ 0)).mpr hz

noncomputable def oldCoefficientRate : ℝ := complexPhase (1 / 3) (2 / 3) oldStationaryRoot
noncomputable def oldIntegralRate : ℝ := complexPhase (1 / 3) (2 / 3) oldSaddleUpper

theorem oldCoefficientRate_formula :
    oldCoefficientRate = (1 / 3) * Real.log oldStationaryRoot +
      (2 / 3) * Real.log (oldStationaryRoot ^ 2 + 6 * oldStationaryRoot + 25) -
      Real.log (oldStationaryRoot - 25) := by
  have hr := oldStationaryRoot_spec.1
  have hp : 0 < oldStationaryRoot ^ 2 + 6 * oldStationaryRoot + 25 := by positivity
  have heA : (oldStationaryRoot : ℂ) ^ 2 + 6 * oldStationaryRoot + 25 =
      ((oldStationaryRoot ^ 2 + 6 * oldStationaryRoot + 25 : ℝ) : ℂ) := by push_cast; rfl
  have heJ : (25 : ℂ) - oldStationaryRoot = ((25 - oldStationaryRoot : ℝ) : ℂ) := by push_cast; rfl
  unfold oldCoefficientRate complexPhase
  rw [heA, heJ]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, abs_of_pos hp,
    abs_of_neg (show 25 - oldStationaryRoot < 0 by linarith [oldStationaryRoot_coarse.1]), neg_sub]

theorem oldIntegralRate_formula :
    oldIntegralRate = (1 / 6) * Real.log (625 / (2 * oldStationaryRoot)) +
      (1 / 3) * Real.log (1280000 / (oldStationaryRoot ^ 2 + 6 * oldStationaryRoot + 25)) -
      (1 / 2) * Real.log (30000 / (oldStationaryRoot - 25)) := by
  rw [← oldSaddleQuadraticNormSq_formula, ← oldSaddlePoleNormSq_formula]
  change oldIntegralRate = (1 / 6) * Real.log oldSaddleNormSq +
    (1 / 3) * Real.log oldSaddleQuadraticNormSq - (1 / 2) * Real.log oldSaddlePoleNormSq
  rw [← oldSaddleUpper_normSq]
  unfold oldIntegralRate complexPhase oldSaddleQuadraticNormSq oldSaddlePoleNormSq
  simp only [log_complex_normSq]
  ring

noncomputable def oldStationaryPoly : Polynomial ℤ :=
  Polynomial.C 2 * Polynomial.X ^ 3 - Polynomial.C 125 * Polynomial.X ^ 2 -
    Polynomial.C 500 * Polynomial.X - Polynomial.C 625

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem oldStationaryPoly_resultant :
    oldStationaryPoly.resultant
      (Polynomial.X ^ 2 + Polynomial.C 6 * Polynomial.X + Polynomial.C 25) 3 2 = 5120000 := by
  have hm : Polynomial.sylvester oldStationaryPoly
      (Polynomial.X ^ 2 + Polynomial.C 6 * Polynomial.X + Polynomial.C 25) 3 2 =
      !![(25 : ℤ), 0, 0, -625, 0; 6, 25, 0, -500, -625;
        1, 6, 25, -125, -500; 0, 1, 6, 2, -125; 0, 0, 1, 0, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [oldStationaryPoly, Polynomial.sylvester, Fin.addCases,
        Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    decide +kernel
  rw [Polynomial.resultant, hm]
  norm_num [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove]
  decide +kernel

theorem oldStationaryCubic_at_pole : oldStationaryCubic 25 = -60000 := by
  norm_num [oldStationaryCubic]

end PiIrrationality
