import Formalization.CoefficientGrowth
import Formalization.DenominatorGrowth
import Formalization.IntegerLinearForm

/-! The ordinary growth of the actual integer coefficient used in Section 5. -/

namespace PiIrrationality

open Filter
open scoped Topology

theorem integerCoeffV_abs_formula (n : ℕ) (hn : 1 ≤ n) :
    |(integerCoeffV n : ℝ)| = (normalizationMultiplier n : ℝ) *
      |(↑(-laurentCoeffRat n 0 / 2) : ℝ)| := by
  have h := congrArg (fun z : ℚ => (z : ℝ)) (integerCoeffV_cast n hn)
  push_cast at h
  rw [h, normalizedPiCoeff]
  push_cast
  rw [show -(normalizationMultiplier n : ℝ) * (laurentCoeffRat n 0 : ℝ) / 2 =
    (normalizationMultiplier n : ℝ) * (-(laurentCoeffRat n 0 : ℝ) / 2) by ring,
    abs_mul, abs_of_pos (normalizationMultiplier_real_pos n)]

theorem integerCoeffV_log_limit :
    Tendsto (fun n : ℕ => Real.log |(integerCoeffV n : ℝ)| / (5570 * (n : ℝ)))
      atTop (𝓝 (coefficientGrowthRate + normalizationCost primeSavingSeries)) := by
  have h := paper_pi_coeff_log_limit.add normalizationCost_limit
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hc : (↑(-laurentCoeffRat n 0 / 2) : ℝ) ≠ 0 := by
    have hq : (-laurentCoeffRat n 0 / 2 : ℚ) ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr (laurentCoeffRat_zero_pos n).ne') (by norm_num)
    exact_mod_cast hq
  rw [integerCoeffV_abs_formula n hn,
    Real.log_mul (normalizationMultiplier_real_pos n).ne' (abs_ne_zero.mpr hc)]
  ring

end PiIrrationality
