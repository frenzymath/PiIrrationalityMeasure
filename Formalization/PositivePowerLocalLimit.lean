import Formalization.PositivePowerCharacteristic
import Formalization.CoefficientLocalLimit

/-! The local Gaussian limit for all positive-power generating functions. -/

namespace PiIrrationality.PositivePower

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Topology

variable (u v : ℕ) {d : ℕ} (hd : 0 < d)

theorem law_memLp_two {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    MemLp (fun k : ℕ => (k : ℝ)) 2 (law u v hd x hx0 hx1 1).toMeasure := by
  apply memLp_of_mem_interior_integrableExpSet _ 2
  exact law_interior_integrableExpSet u v hd hx0 hx1 (by simpa using hx1)

theorem centered_memLp_two {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    MemLp (fun k : ℕ => (k : ℝ) - mean u v d x) 2
      (law u v hd x hx0 hx1 1).toMeasure :=
  (law_memLp_two u v hd hx0 hx1).sub (memLp_const _)

theorem centered_expectation {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∫ k : ℕ, ((k : ℝ) - mean u v d x) ∂(law u v hd x hx0.le hx1 1).toMeasure = 0 := by
  rw [integral_sub ((law_memLp_two u v hd hx0.le hx1).integrable (by norm_num))
    (integrable_const _), law_expectation u v hd hx0 hx1]
  simp

theorem centered_second_moment {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∫ k : ℕ, ((k : ℝ) - mean u v d x) ^ 2
      ∂(law u v hd x hx0.le hx1 1).toMeasure = saddleVariance u v d x := by
  rw [← law_variance u v hd hx0 hx1, variance_eq_integral (by fun_prop),
    law_expectation u v hd hx0 hx1]

include hd in
theorem centered_taylor {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (fun t : ℝ => centeredCharacteristic u v d x t -
      (1 - (saddleVariance u v d x : ℂ) * (t : ℂ) ^ 2 / 2))
      =o[𝓝 0] (fun t : ℝ => t ^ 2) := by
  have h := centered_charFun_taylor (centered_memLp_two u v hd hx0.le hx1)
    (centered_expectation u v hd hx0 hx1)
  simpa only [law_centered_charFun u v hd hx0.le hx1,
    centered_second_moment u v hd hx0 hx1] using h

include hd in
theorem centered_global_gaussian_bound {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, |t| ≤ Real.pi →
      ‖centeredCharacteristic u v d x t‖ ≤ Real.exp (-c * t ^ 2) := by
  have hvar := saddleVariance_pos u v hd hx0 hx1
  obtain ⟨c, hc, hb⟩ := local_gaussian_global_bound Real.pi_pos
    (div_pos hvar (by norm_num : (0 : ℝ) < 4))
    (centeredCharacteristic_continuous u v hx0.le hx1).continuousOn
    (fun t ht ht0 => centeredCharacteristic_norm_strict u v hd hx0 hx1
      (abs_pos.mpr ht0) (abs_le.mpr ht))
    (quadratic_expansion_gaussian_bound hvar (centered_taylor u v hd hx0 hx1))
  exact ⟨c, hc, fun t ht => hb t (abs_le.mp ht)⟩

include hd in
theorem centered_integral_limit {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ) : ℂ) *
      ∫ t in -Real.pi..Real.pi, centeredCharacteristic u v d x t ^ n) atTop
        (𝓝 (Real.sqrt (2 * Real.pi / saddleVariance u v d x) : ℂ)) := by
  obtain ⟨c, hc, hb⟩ := centered_global_gaussian_bound u v hd hx0 hx1
  exact gaussian_integral_power_limit Real.pi_pos hc
    (centeredCharacteristic_continuous u v hx0.le hx1)
    (fun t ht => hb t (abs_le.mpr ht))
    (quadratic_expansion_power_limit (centered_taylor u v hd hx0 hx1))

include hd in
theorem centered_integral {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (q : ℕ) (hm : mean u v d x = (q : ℝ)) (n : ℕ) :
    (∫ t in -Real.pi..Real.pi, centeredCharacteristic u v d x t ^ n) =
      (2 * Real.pi : ℂ) * (probability u v d x n (q * n) : ℂ) := by
  have h := lattice_fourier_inversion (law u v hd x hx0 hx1 n) (q * n)
  simp_rw [law_charFun u v hd hx0 hx1, law_toReal] at h
  have he (t : ℝ) : centeredCharacteristic u v d x t ^ n =
      characteristic u v d x t ^ n *
        Complex.exp (-((q * n : ℕ) : ℂ) * (t : ℂ) * Complex.I) := by
    simp only [centeredCharacteristic, mul_pow, ← Complex.exp_nat_mul, hm,
      Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_natCast, Nat.cast_mul]
    congr 1
    congr 1
    ring
  simpa only [← he] using h

include hd in
theorem probability_local_limit {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (q : ℕ) (hm : mean u v d x = (q : ℝ)) :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * probability u v d x n (q * n)) atTop
      (𝓝 (1 / Real.sqrt (2 * Real.pi * saddleVariance u v d x))) := by
  have h := (centered_integral_limit u v hd hx0 hx1).div_const (2 * Real.pi : ℂ)
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (show (2 : ℝ) * Real.pi ≠ 0 by positivity)
  have h' : Tendsto
      (fun n : ℕ => ((Real.sqrt (n : ℝ) * probability u v d x n (q * n) : ℝ) : ℂ))
      atTop (𝓝 ((1 / Real.sqrt (2 * Real.pi * saddleVariance u v d x) : ℝ) : ℂ)) := by
    convert! h using 1
    · ext n
      rw [centered_integral u v hd hx0.le hx1 q hm]
      push_cast
      field_simp [hπ] <;> ring
    · have hn := congrArg Complex.ofReal (gaussian_normalization (saddleVariance u v d x))
      push_cast at hn
      simpa only [Complex.ofReal_div, Complex.ofReal_one] using congrArg nhds hn.symm
  simpa only [Function.comp_def, Complex.ofReal_re] using (Complex.continuous_re.tendsto _).comp h'

end PiIrrationality.PositivePower
