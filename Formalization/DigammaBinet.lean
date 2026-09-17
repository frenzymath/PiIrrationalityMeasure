import Formalization.BinetRecurrence
import Formalization.PrimeSavingDigamma
import Formalization.PrimeSeriesTail

/-! Identification of the Laplace expression with the actual digamma function. -/

namespace PiIrrationality

open Filter
open scoped Topology

theorem binetLaplace_shift_limit {y : ℝ} (hy : 0 < y) :
    Tendsto (fun n : ℕ => binetLaplace (y + n)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => y + (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop y tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun n : ℕ => 1 / (12 * (y + n) ^ 2)) atTop (𝓝 0) := by
    have h := (hn.inv_tendsto_atTop.pow 2).const_mul ((1 : ℝ) / 12)
    simpa only [Pi.inv_apply, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul,
      mul_one, one_mul, inv_pow, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm] using h
  exact squeeze_zero (fun n => (binetLaplace_pos (add_pos_of_pos_of_nonneg hy
    (Nat.cast_nonneg n))).le) (fun n => (binetLaplace_lt_inv_sq
      (add_pos_of_pos_of_nonneg hy (Nat.cast_nonneg n))).le) hb

theorem binetDigamma_sub_log_limit {y : ℝ} (hy : 0 < y) :
    Tendsto (fun n : ℕ => binetDigamma (y + n) - Real.log (y + n)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => y + (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop y tendsto_natCast_atTop_atTop
  have h := (hn.const_div_atTop ((1 : ℝ) / 2)).neg.sub (binetLaplace_shift_limit hy)
  simp only [neg_zero, sub_zero] at h
  convert! h using 1
  funext n
  unfold binetDigamma
  field_simp
  ring

theorem log_shift_sub_harmonic_limit {y : ℝ} (hy : 0 < y) :
    Tendsto (fun n : ℕ => Real.log (y + n) - (harmonic n : ℝ)) atTop
      (𝓝 (-Real.eulerMascheroniConstant)) := by
  have hl : Tendsto (fun n : ℕ => Real.log (y + n) - Real.log n) atTop (𝓝 0) := by
    apply (periodicLogTail_limit 0 y 0).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hyn : y + (n : ℝ) ≠ 0 := (add_pos hy hnR).ne'
    simp only [periodicLogTail, add_zero, add_comm]
    rw [Real.log_div hyn hnR.ne']
  have h := hl.sub Real.tendsto_harmonic_sub_log
  simp only [zero_sub] at h
  convert! h using 1
  funext n
  ring

theorem binetDigamma_eq_realDigamma {y : ℝ} (hy : 0 < y) :
    binetDigamma y = realDigamma y := by
  have hc := Complex.hasSum_digamma_of_re_pos (z₀ := (y : ℂ)) hy
  have hs : HasSum (fun q : ℕ => 1 / ((q : ℝ) + 1) - 1 / (y + q))
      (realDigamma y + Real.eulerMascheroniConstant) := by
    simpa only [realDigamma, Complex.add_re, Complex.sub_re, ← Complex.ofReal_natCast,
      ← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_inv,
      Complex.ofReal_re, one_div] using Complex.hasSum_re hc
  have hbh : Tendsto (fun n : ℕ => binetDigamma (y + n) - (harmonic n : ℝ)) atTop
      (𝓝 (-Real.eulerMascheroniConstant)) := by
    have h := (binetDigamma_sub_log_limit hy).add (log_shift_sub_harmonic_limit hy)
    simp only [zero_add] at h
    convert! h using 1
    funext n
    ring
  have hlim := hbh.add hs.tendsto_sum_nat
  have heq (n : ℕ) : binetDigamma (y + n) - (harmonic n : ℝ) +
      ∑ q ∈ Finset.range n, (1 / ((q : ℝ) + 1) - 1 / (y + q)) = binetDigamma y := by
    rw [binetDigamma_add_nat hy, Finset.sum_sub_distrib]
    have hh : (∑ q ∈ Finset.range n, 1 / ((q : ℝ) + 1)) = (harmonic n : ℝ) := by
      simpa only [one_div] using Complex.sum_inv_natCast_add_one_real n
    rw [hh]
    ring
  simp only [heq] at hlim
  have hval : -Real.eulerMascheroniConstant + (realDigamma y + Real.eulerMascheroniConstant) =
      realDigamma y := by ring
  rw [hval] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

theorem realDigamma_binetLaplace {y : ℝ} (hy : 0 < y) :
    realDigamma y = Real.log y - 1 / (2 * y) - binetLaplace y := by
  rw [← binetDigamma_eq_realDigamma hy]
  rfl

theorem realDigamma_bernoulli_remainder {y : ℝ} (hy : 0 < y) (N : ℕ) :
    |realDigamma y - Real.log y + 1 / (2 * y) + binetLaplaceApprox y N| <
      |(bernoulli (2 * (N + 1)) : ℝ)| /
        ((2 * (N + 1) : ℕ) * y ^ (2 * (N + 1))) := by
  rw [realDigamma_binetLaplace hy]
  have he : Real.log y - 1 / (2 * y) - binetLaplace y - Real.log y + 1 / (2 * y) +
      binetLaplaceApprox y N = -(binetLaplace y - binetLaplaceApprox y N) := by ring
  rw [he, abs_neg]
  exact binetLaplace_remainder_abs_lt hy N

end PiIrrationality
