import Formalization.CoefficientLocalLimit
import Formalization.CoefficientExtraction

/-! The actual diagonal coefficient asymptotic (4.10). -/

namespace PiIrrationality

open Filter Asymptotics PowerSeries
open scoped Topology

theorem sqrt_scaled_asymptotic {p : ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (h : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * p n) atTop
      (𝓝 (1 / Real.sqrt C))) :
    p ~[atTop] (fun n : ℕ => 1 / Real.sqrt (C * n)) := by
  apply isEquivalent_of_tendsto_one
  have hs : Real.sqrt C ≠ 0 := (Real.sqrt_pos.mpr hC).ne'
  convert! h.mul_const (Real.sqrt C) using 1
  · ext n
    simp only [Pi.div_apply, one_div, div_inv_eq_mul, Real.sqrt_mul hC.le]
    ring
  · simp [hs]

theorem coefficientProbability_asymptotic {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (q : ℕ) (hm : coefficientMean x = (q : ℝ)) :
    (fun n : ℕ => coefficientProbability x n (q * n)) ~[atTop]
      (fun n : ℕ => 1 / Real.sqrt (2 * Real.pi * coefficientVariance x * n)) :=
  sqrt_scaled_asymptotic (mul_pos (by positivity) (coefficientVariance_pos hx0 hx1))
    (coefficientProbability_local_limit hx0 hx1 q hm)

theorem Sseries_diagonal_asymptotic {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (q : ℕ) (hm : coefficientMean x = (q : ℝ)) :
    (fun n : ℕ => (↑(coeff (q * n) (Sseries ^ n)) : ℝ)) ~[atTop]
      (fun n : ℕ => SReal x ^ n / x ^ (q * n) /
        Real.sqrt (2 * Real.pi * coefficientVariance x * n)) := by
  have hr : (fun n : ℕ => SReal x ^ n / x ^ (q * n)) ~[atTop]
      (fun n : ℕ => SReal x ^ n / x ^ (q * n)) := IsEquivalent.refl
  have h := hr.mul
    (coefficientProbability_asymptotic hx0 hx1 q hm)
  have he (n : ℕ) : (↑(coeff (q * n) (Sseries ^ n)) : ℝ) =
      SReal x ^ n / x ^ (q * n) * coefficientProbability x n (q * n) := by
    simpa only [coefficientLaw_toReal] using coefficientLaw_extraction hx0 hx1 n (q * n)
  change (fun n : ℕ => SReal x ^ n / x ^ (q * n) *
    coefficientProbability x n (q * n)) ~[atTop]
      (fun n : ℕ => SReal x ^ n / x ^ (q * n) *
        (1 / Real.sqrt (2 * Real.pi * coefficientVariance x * n))) at h
  simpa only [Pi.mul_apply, ← he, mul_one_div] using h

theorem Sseries_saddle_asymptotic :
    (fun n : ℕ => (↑(coeff (5570 * n) (Sseries ^ n)) : ℝ)) ~[atTop]
      (fun n : ℕ => SReal coefficientSaddle ^ n / coefficientSaddle ^ (5570 * n) /
        Real.sqrt (2 * Real.pi * coefficientVariance coefficientSaddle * n)) :=
  Sseries_diagonal_asymptotic coefficientSaddle_mem.1 coefficientSaddle_mem.2
    5570 coefficientSaddle_mean

end PiIrrationality
