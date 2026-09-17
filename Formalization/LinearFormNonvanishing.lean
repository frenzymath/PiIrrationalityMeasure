import Formalization.CoefficientExtraction
import Formalization.IntegerLinearForm
import Formalization.DenominatorGrowth
import Formalization.Hata

/-! Nonvanishing of the actual coefficients and linear forms used in Section 5. -/

namespace PiIrrationality

theorem normalizedPiCoeff_neg (n : ℕ) : normalizedPiCoeff n < 0 := by
  have hM : (0 : ℚ) < normalizationMultiplier n := by
    exact_mod_cast normalizationMultiplier_real_pos n
  unfold normalizedPiCoeff
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (neg_neg_of_pos hM) (laurentCoeffRat_zero_pos n)) (by norm_num)

theorem integerCoeffV_neg (n : ℕ) (hn : 1 ≤ n) : integerCoeffV n < 0 := by
  have h := normalizedPiCoeff_neg n
  rw [← integerCoeffV_cast n hn] at h
  exact_mod_cast h

theorem integerCoeffV_ne_zero (n : ℕ) (hn : 1 ≤ n) : integerCoeffV n ≠ 0 :=
  (integerCoeffV_neg n hn).ne

theorem paper_real_linearForm_ne_zero (n : ℕ) (hn : 1 ≤ n) :
    (integerCoeffU n : ℝ) + (integerCoeffV n : ℝ) * Real.pi ≠ 0 :=
  pi_linearForm_ne_zero (integerCoeffV_ne_zero n hn)

theorem paperIntegral_re_ne_zero (n : ℕ) (hn : 1 ≤ n) : (paperIntegral n).re ≠ 0 := by
  intro hzero
  have h := paper_real_integerLinearForm n hn
  rw [hzero, mul_zero] at h
  exact paper_real_linearForm_ne_zero n hn h.symm

theorem paperIntegral_ne_zero (n : ℕ) (hn : 1 ≤ n) : paperIntegral n ≠ 0 := by
  intro hzero
  exact paperIntegral_re_ne_zero n hn (by rw [hzero, Complex.zero_re])

end PiIrrationality
