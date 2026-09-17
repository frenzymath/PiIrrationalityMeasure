import Formalization.OriginalContourBounds

/-! Equality of the original and smooth contour amplitudes in (4.27). -/

namespace PiIrrationality

noncomputable def originalContourWeight (e t : ℝ) : ℝ :=
  ‖deriv (tauPlus e) t‖ / ‖25 - gammaPath e t‖

theorem originalContourWeight_comp_sq {e u : ℝ}
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hu : 0 < u) :
    originalContourWeight e (u ^ 2) * (2 * u) = contourWeight e u := by
  unfold originalContourWeight contourWeight
  rw [(tauPlus_hasDerivAt_sqrt he0 he1 (sq_pos_of_pos hu)).deriv,
    Real.sqrt_sq hu.le, norm_smul, Real.norm_of_nonneg (by positivity)]
  field_simp

theorem originalContourWeight_intervalIntegrable {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    IntervalIntegrable (originalContourWeight e) MeasureTheory.volume 0 1 := by
  have hs : ∀ u ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by
    intro u _
    simpa using hasDerivAt_pow 2 u
  have hpos : ∀ u ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1), 0 ≤ 2 * u := by
    intro u hu
    norm_num at hu
    exact mul_nonneg (by norm_num) hu.1.le
  have hcomp := (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (continuous_pow 2).continuousOn hs hpos (g := originalContourWeight e))
  norm_num only [zero_pow (by decide : 2 ≠ 0), one_pow] at hcomp
  apply hcomp.mp
  apply (contourWeight_intervalIntegrable he0 he1).congr
  intro u hu
  have hu0 : 0 < u := by simpa using hu.1
  exact (originalContourWeight_comp_sq he0 he1 hu0).symm

theorem originalContourWeight_integral_eq {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    (∫ t in (0 : ℝ)..1, originalContourWeight e t) =
      ∫ u in (0 : ℝ)..1, contourWeight e u := by
  have hs : ∀ u ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by
    intro u _
    simpa using hasDerivAt_pow 2 u
  have hpos : ∀ u ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1), 0 ≤ 2 * u := by
    intro u hu
    norm_num at hu
    exact mul_nonneg (by norm_num) hu.1.le
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (continuous_pow 2).continuousOn hs hpos (g := originalContourWeight e)
  norm_num only [zero_pow (by decide : 2 ≠ 0), one_pow] at h
  rw [← h]
  apply intervalIntegral.integral_congr_ae
  exact Filter.Eventually.of_forall (fun u hu =>
    originalContourWeight_comp_sq he0 he1 (by simpa using hu.1))

theorem contourAmplitude_original_formula :
    contourAmplitude = 10 * ∫ t in (0 : ℝ)..1,
      ‖deriv (tauPlus saddleEta) t‖ / ‖25 - gammaPath saddleEta t‖ := by
  rw [show (fun t => ‖deriv (tauPlus saddleEta) t‖ /
      ‖25 - gammaPath saddleEta t‖) = originalContourWeight saddleEta by rfl,
    originalContourWeight_integral_eq saddleEta_pos.le saddleEta_lt_one.le]
  rfl

end PiIrrationality
