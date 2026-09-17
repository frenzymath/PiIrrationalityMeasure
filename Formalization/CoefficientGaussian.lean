import Formalization.CoefficientCharacteristic
import Formalization.GaussianPowerLimit

/-! The centered tilted law satisfies the Gaussian expansion and power limit. -/

namespace PiIrrationality

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Topology

noncomputable def coefficientVariance (x : ℝ) : ℝ := x * deriv coefficientMean x

theorem coefficientVariance_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < coefficientVariance x := by
  rw [coefficientVariance, ← coefficientLaw_variance hx0 hx1]
  exact coefficientLaw_variance_pos hx0 hx1

theorem coefficientLaw_memLp_two {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    MemLp (fun k : ℕ => (k : ℝ)) 2 (coefficientLaw x hx0 hx1 1).toMeasure := by
  apply memLp_of_mem_interior_integrableExpSet _ 2
  exact coefficientLaw_interior_integrableExpSet hx0 hx1 (by simpa using hx1)

theorem coefficientCentered_memLp_two {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    MemLp (fun k : ℕ => (k : ℝ) - coefficientMean x) 2
      (coefficientLaw x hx0 hx1 1).toMeasure :=
  (coefficientLaw_memLp_two hx0 hx1).sub (memLp_const (coefficientMean x))

theorem coefficientCentered_expectation {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∫ k : ℕ, ((k : ℝ) - coefficientMean x) ∂(coefficientLaw x hx0.le hx1 1).toMeasure = 0 := by
  rw [integral_sub ((coefficientLaw_memLp_two hx0.le hx1).integrable (by norm_num))
    (integrable_const _), coefficientLaw_expectation hx0 hx1]
  simp

theorem coefficientCentered_second_moment {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∫ k : ℕ, ((k : ℝ) - coefficientMean x) ^ 2
      ∂(coefficientLaw x hx0.le hx1 1).toMeasure = coefficientVariance x := by
  rw [coefficientVariance, ← coefficientLaw_variance hx0 hx1, variance_eq_integral (by fun_prop),
    coefficientLaw_expectation hx0 hx1]

theorem coefficientCentered_taylor {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (fun t : ℝ => coefficientCenteredChar x t -
      (1 - (coefficientVariance x : ℂ) * (t : ℂ) ^ 2 / 2))
      =o[𝓝 0] (fun t : ℝ => t ^ 2) := by
  have h := centered_charFun_taylor (coefficientCentered_memLp_two hx0.le hx1)
    (coefficientCentered_expectation hx0 hx1)
  simpa only [coefficientLaw_centered_charFun hx0.le hx1,
    coefficientCentered_second_moment hx0 hx1] using h

theorem coefficientCentered_gaussian_bound {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∀ᶠ t : ℝ in 𝓝 0,
      ‖coefficientCenteredChar x t‖ ≤ Real.exp (-(coefficientVariance x / 4) * t ^ 2) :=
  quadratic_expansion_gaussian_bound (coefficientVariance_pos hx0 hx1)
    (coefficientCentered_taylor hx0 hx1)

theorem coefficientCentered_power_limit {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (u : ℝ) :
    Tendsto (fun n : ℕ => coefficientCenteredChar x ((Real.sqrt (n : ℝ))⁻¹ * u) ^ n) atTop
      (𝓝 (Complex.exp (-(coefficientVariance x : ℂ) * (u : ℂ) ^ 2 / 2))) :=
  quadratic_expansion_power_limit (coefficientCentered_taylor hx0 hx1) u

end PiIrrationality
