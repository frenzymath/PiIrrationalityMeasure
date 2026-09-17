import Formalization.CoefficientGaussian
import Formalization.GlobalGaussianBound
import Formalization.GaussianIntegralLimit
import Formalization.LatticeFourierInversion

/-! The actual single-lattice-point Gaussian asymptotic used in Section 4.1. -/

namespace PiIrrationality

open MeasureTheory Filter
open scoped Topology

theorem coefficientCentered_global_gaussian_bound {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, |t| ≤ Real.pi →
      ‖coefficientCenteredChar x t‖ ≤ Real.exp (-c * t ^ 2) := by
  obtain ⟨c, hc, hb⟩ := local_gaussian_global_bound Real.pi_pos
    (show 0 < coefficientVariance x / 4 by exact div_pos (coefficientVariance_pos hx0 hx1) (by norm_num))
    (coefficientCenteredChar_continuous hx0.le hx1).continuousOn
    (fun t ht ht0 => coefficientCenteredChar_norm_strict hx0 hx1 (abs_pos.mpr ht0) (abs_le.mpr ht))
    (coefficientCentered_gaussian_bound hx0 hx1)
  exact ⟨c, hc, fun t ht => hb t (abs_le.mp ht)⟩

theorem coefficientCentered_integral_limit {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ) : ℂ) *
      ∫ t in -Real.pi..Real.pi, coefficientCenteredChar x t ^ n) atTop
        (𝓝 (Real.sqrt (2 * Real.pi / coefficientVariance x) : ℂ)) := by
  obtain ⟨c, hc, hb⟩ := coefficientCentered_global_gaussian_bound hx0 hx1
  exact gaussian_integral_power_limit Real.pi_pos hc
    (coefficientCenteredChar_continuous hx0.le hx1)
    (fun t ht => hb t (abs_le.mpr ht)) (coefficientCentered_power_limit hx0 hx1)

theorem coefficientCentered_integral {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (q : ℕ) (hm : coefficientMean x = (q : ℝ)) (n : ℕ) :
    (∫ t in -Real.pi..Real.pi, coefficientCenteredChar x t ^ n) =
      (2 * Real.pi : ℂ) * (coefficientProbability x n (q * n) : ℂ) := by
  have h := lattice_fourier_inversion (coefficientLaw x hx0 hx1 n) (q * n)
  simp_rw [coefficientLaw_charFun hx0 hx1, coefficientLaw_toReal] at h
  have he (t : ℝ) : coefficientCenteredChar x t ^ n =
      coefficientChar x t ^ n * Complex.exp (-((q * n : ℕ) : ℂ) * (t : ℂ) * Complex.I) := by
    simp only [coefficientCenteredChar, mul_pow, ← Complex.exp_nat_mul, hm,
      Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_natCast, Nat.cast_mul]
    congr 1
    congr 1
    ring
  simpa only [← he] using h

theorem gaussian_normalization (v : ℝ) :
    Real.sqrt (2 * Real.pi / v) / (2 * Real.pi) = 1 / Real.sqrt (2 * Real.pi * v) := by
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  calc
    Real.sqrt (2 * Real.pi / v) / (2 * Real.pi) =
        (Real.sqrt (2 * Real.pi) / (2 * Real.pi)) / Real.sqrt v := by
      rw [Real.sqrt_div hπ]
      ring
    _ = (1 / Real.sqrt (2 * Real.pi)) / Real.sqrt v := by rw [Real.sqrt_div_self']
    _ = _ := by rw [Real.sqrt_mul hπ]; ring

theorem coefficientProbability_local_limit {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (q : ℕ) (hm : coefficientMean x = (q : ℝ)) :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * coefficientProbability x n (q * n)) atTop
      (𝓝 (1 / Real.sqrt (2 * Real.pi * coefficientVariance x))) := by
  have h := (coefficientCentered_integral_limit hx0 hx1).div_const (2 * Real.pi : ℂ)
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 : ℝ) * Real.pi ≠ 0 by positivity)
  have h' : Tendsto (fun n : ℕ => ((Real.sqrt (n : ℝ) * coefficientProbability x n (q * n) : ℝ) : ℂ))
      atTop (𝓝 ((1 / Real.sqrt (2 * Real.pi * coefficientVariance x) : ℝ) : ℂ)) := by
    convert! h using 1
    · ext n
      rw [coefficientCentered_integral hx0.le hx1 q hm]
      push_cast
      field_simp [hπ] <;> ring
    · have hn := congrArg Complex.ofReal (gaussian_normalization (coefficientVariance x))
      push_cast at hn
      simpa only [Complex.ofReal_div, Complex.ofReal_one] using congrArg nhds hn.symm
  simpa only [Function.comp_def, Complex.ofReal_re] using (Complex.continuous_re.tendsto _).comp h'

theorem coefficientProbability_saddle_local_limit :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) *
      coefficientProbability coefficientSaddle n (5570 * n)) atTop
        (𝓝 (1 / Real.sqrt (2 * Real.pi * coefficientVariance coefficientSaddle))) :=
  coefficientProbability_local_limit coefficientSaddle_mem.1 coefficientSaddle_mem.2
    5570 coefficientSaddle_mean

end PiIrrationality
