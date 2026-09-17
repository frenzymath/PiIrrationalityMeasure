import Formalization.OldPointSaddles
import Formalization.OldPointSaving

/-! Logarithmic simplifications of the actual old rates. -/

namespace PiIrrationality

theorem oldIntegralRate_from_real :
    oldIntegralRate = (3 * Real.log 2 - Real.log 3 - oldCoefficientRate) / 2 := by
  have hr := oldStationaryRoot_spec.1.ne'
  have hA : oldStationaryRoot ^ 2 + 6 * oldStationaryRoot + 25 ≠ 0 := by
    nlinarith [oldStationaryRoot_spec.1]
  have hJ : oldStationaryRoot - 25 ≠ 0 := by linarith [oldStationaryRoot_coarse.1]
  have h625 : Real.log 625 = 4 * Real.log 5 := by
    have h := Real.log_pow (5 : ℝ) 4
    norm_num only [show (5 : ℝ) ^ 4 = 625 by norm_num, Nat.cast_ofNat] at h
    exact h
  have h128 : Real.log 1280000 = 11 * Real.log 2 + 4 * Real.log 5 := by
    rw [show (1280000 : ℝ) = 2 ^ 11 * 5 ^ 4 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  have h300 : Real.log 30000 = Real.log 3 + 4 * Real.log 2 + 4 * Real.log 5 := by
    rw [show (30000 : ℝ) = (3 * 2 ^ 4) * 5 ^ 4 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]
    norm_num
  rw [oldIntegralRate_formula, oldCoefficientRate_formula,
    Real.log_div (by norm_num) (mul_ne_zero (by norm_num) hr),
    Real.log_mul (by norm_num) hr, Real.log_div (by norm_num) hA,
    Real.log_div (by norm_num) hJ, h625, h128, h300]
  ring

theorem parameterCost_oldPoint_log_formula :
    parameterCost oldPoint = 4 / 3 - (3 / 2) * Real.log 2 + (1 / 2) * Real.log 3 -
      Real.pi / (6 * Real.sqrt 3) := by
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  rw [parameterCost_oldPoint, Real.log_div (mul_ne_zero (by norm_num) hs) (by norm_num),
    Real.log_mul (by norm_num) hs, Real.log_sqrt (by norm_num)]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat] at h
    exact h
  rw [h4]
  ring

end PiIrrationality
