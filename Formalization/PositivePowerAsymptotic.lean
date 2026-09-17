import Formalization.PositivePowerLocalLimit
import Formalization.CoefficientGrowth

/-! Ordinary diagonal coefficient asymptotics and logarithmic rates for arbitrary powers. -/

namespace PiIrrationality.PositivePower

open Filter Asymptotics PowerSeries
open scoped Topology

variable (u v : ℕ) {d : ℕ} (hd : 0 < d)

include hd in
theorem probability_asymptotic {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (q : ℕ) (hm : mean u v d x = (q : ℝ)) :
    (fun n : ℕ => probability u v d x n (q * n)) ~[atTop]
      (fun n : ℕ => 1 / Real.sqrt (2 * Real.pi * saddleVariance u v d x * n)) :=
  sqrt_scaled_asymptotic (mul_pos (by positivity) (saddleVariance_pos u v hd hx0 hx1))
    (probability_local_limit u v hd hx0 hx1 q hm)

include hd in
theorem series_diagonal_asymptotic {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (q : ℕ) (hm : mean u v d x = (q : ℝ)) :
    (fun n : ℕ => (↑(coeff (q * n) (series u v d ^ n)) : ℝ)) ~[atTop]
      (fun n : ℕ => realValue u v d x ^ n / x ^ (q * n) /
        Real.sqrt (2 * Real.pi * saddleVariance u v d x * n)) := by
  have hr : (fun n : ℕ => realValue u v d x ^ n / x ^ (q * n)) ~[atTop]
      (fun n : ℕ => realValue u v d x ^ n / x ^ (q * n)) := IsEquivalent.refl
  have h := hr.mul (probability_asymptotic u v hd hx0 hx1 q hm)
  have he (n : ℕ) : (↑(coeff (q * n) (series u v d ^ n)) : ℝ) =
      realValue u v d x ^ n / x ^ (q * n) * probability u v d x n (q * n) :=
    probability_extraction u v hx0 hx1 n (q * n)
  change (fun n : ℕ => realValue u v d x ^ n / x ^ (q * n) *
    probability u v d x n (q * n)) ~[atTop]
      (fun n : ℕ => realValue u v d x ^ n / x ^ (q * n) *
        (1 / Real.sqrt (2 * Real.pi * saddleVariance u v d x * n))) at h
  simpa only [Pi.mul_apply, ← he, mul_one_div] using h

include hd in
theorem probability_log_limit {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (q : ℕ) (hm : mean u v d x = (q : ℝ)) :
    Tendsto (fun n : ℕ => Real.log (probability u v d x n (q * n)) / (n : ℝ))
      atTop (𝓝 0) := by
  apply sqrt_scaled_log_limit (L := 1 / Real.sqrt (2 * Real.pi * saddleVariance u v d x))
    (one_div_pos.mpr (Real.sqrt_pos.mpr
      (mul_pos (by positivity) (saddleVariance_pos u v hd hx0 hx1))))
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact probability_pos u v hd hx0 hx1 hn _
  · exact probability_local_limit u v hd hx0 hx1 q hm

include hd in
theorem series_diagonal_log_formula {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (q : ℕ) {n : ℕ} (hn : 0 < n) :
    Real.log (↑(coeff (q * n) (series u v d ^ n)) : ℝ) / (n : ℝ) =
      Real.log (realValue u v d x) - q * Real.log x +
        Real.log (probability u v d x n (q * n)) / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs := (realValue_pos u v d hx0.le hx1).ne'
  rw [probability_extraction u v hx0 hx1,
    Real.log_mul (div_ne_zero (pow_ne_zero _ hs) (pow_ne_zero _ hx0.ne'))
      (probability_pos u v hd hx0 hx1 hn _).ne',
    Real.log_div (pow_ne_zero _ hs) (pow_ne_zero _ hx0.ne'),
    Real.log_pow, Real.log_pow, Nat.cast_mul]
  field_simp

include hd in
theorem series_diagonal_log_limit {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (q : ℕ) (hm : mean u v d x = (q : ℝ)) :
    Tendsto (fun n : ℕ => Real.log (↑(coeff (q * n) (series u v d ^ n)) : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log (realValue u v d x) - q * Real.log x)) := by
  have h := (probability_log_limit u v hd hx0 hx1 q hm).const_add
    (Real.log (realValue u v d x) - q * Real.log x)
  rw [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (series_diagonal_log_formula u v hd hx0 hx1 q hn).symm

end PiIrrationality.PositivePower
