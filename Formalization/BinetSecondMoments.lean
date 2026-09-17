import Formalization.BinetSecondFormula

/-! The Bernoulli moment identity for the second Binet kernel used in (3.21). -/

namespace PiIrrationality

open MeasureTheory Set

theorem binetSecondMoment_factorial {m : ℕ} (hm : 0 < m) :
    ((2 * m - 1).factorial : ℝ) * positiveBernoulliCoeff m =
      |(bernoulli (2 * m) : ℝ)| / (2 * m : ℕ) := by
  rw [positiveBernoulliCoeff_eq_abs hm]
  have hs : 2 * m = (2 * m - 1) + 1 := by omega
  have hfac : ((2 * m).factorial : ℝ) =
      ((2 * m : ℕ) : ℝ) * ((2 * m - 1).factorial : ℝ) := by
    conv_lhs => rw [hs, Nat.factorial_succ, ← hs]
    push_cast
    rfl
  rw [hfac]
  have hn : (((2 * m - 1).factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * m - 1)
  field_simp

theorem hasSum_binetSecondMoment_integrals {m : ℕ} (hm : 0 < m) :
    HasSum (fun n : ℕ =>
      ∫ t : ℝ in Ioi 0, 2 * (t ^ (2 * m - 1) * Real.exp (-(binetPole n * t))))
      (|(bernoulli (2 * m) : ℝ)| / (2 * m : ℕ)) := by
  have hs := (hasSum_binetMoment hm).mul_left ((2 * m - 1).factorial : ℝ)
  rw [binetSecondMoment_factorial hm] at hs
  convert! hs using 1
  ext n
  rw [integral_const_mul, integral_pow_mul_exp_neg_mul (binetPole_pos n) (2 * m - 1),
    show 2 * m - 1 + 1 = 2 * m by omega]
  ring

theorem binet_second_moment {m : ℕ} (hm : 0 < m) :
    2 * (∫ t : ℝ in Ioi 0, t ^ (2 * m - 1) / (Real.exp (2 * Real.pi * t) - 1)) =
      |(bernoulli (2 * m) : ℝ)| / (2 * m : ℕ) := by
  have hi (n : ℕ) : IntegrableOn
      (fun t : ℝ => 2 * (t ^ (2 * m - 1) * Real.exp (-(binetPole n * t)))) (Ioi 0) :=
    (integrableOn_pow_mul_exp_neg_mul (binetPole_pos n) _).const_mul 2
  have hn (n : ℕ) : (∫ t : ℝ in Ioi 0,
      ‖2 * (t ^ (2 * m - 1) * Real.exp (-(binetPole n * t)))‖) =
        ∫ t : ℝ in Ioi 0, 2 * (t ^ (2 * m - 1) * Real.exp (-(binetPole n * t))) := by
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have htpos : 0 < t := ht
    exact Real.norm_of_nonneg (by positivity)
  have hs : Summable (fun n : ℕ => ∫ t : ℝ in Ioi 0,
      ‖2 * (t ^ (2 * m - 1) * Real.exp (-(binetPole n * t)))‖) := by
    simp only [hn]
    exact (hasSum_binetSecondMoment_integrals hm).summable
  have h := hasSum_integral_of_summable_integral_norm hi hs
  rw [(hasSum_binetSecondMoment_integrals hm).unique h, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have hsum := (hasSum_binetExponentials ht).mul_left (2 * t ^ (2 * m - 1))
  have he (n : ℕ) : 2 * t ^ (2 * m - 1) * Real.exp (-(binetPole n * t)) =
      2 * (t ^ (2 * m - 1) * Real.exp (-(binetPole n * t))) := by ring
  simp_rw [he] at hsum
  rw [hsum.tsum_eq]
  ring

theorem integrableOn_binetSecondMoment {m : ℕ} (hm : 0 < m) :
    IntegrableOn (fun t : ℝ => t ^ (2 * m - 1) / (Real.exp (2 * Real.pi * t) - 1))
      (Ioi 0) := by
  by_contra h
  have he := binet_second_moment hm
  rw [integral_undef h, mul_zero] at he
  have hp : 0 < |(bernoulli (2 * m) : ℝ)| / (2 * m : ℕ) := by
    rw [← binetSecondMoment_factorial hm]
    exact mul_pos (by exact_mod_cast Nat.factorial_pos (2 * m - 1))
      (positiveBernoulliCoeff_pos hm)
  exact hp.ne' he.symm

end PiIrrationality
