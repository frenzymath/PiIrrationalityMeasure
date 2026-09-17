import Formalization.PrimeSavingComputation
import Formalization.DenominatorGrowth

/-! Certified numerical saving and normalization-cost enclosures (3.25)--(3.30). -/

namespace PiIrrationality

theorem primeSavingApproxRat_enclosure :
    (12025657733612918002543147 : ℚ) / 10 ^ 22 < primeSavingApproxRat ∧
      primeSavingApproxRat < (12025657733612918002543148 : ℚ) / 10 ^ 22 := by
  have h := abs_lt.mp roundedSavingTotal_error
  rw [roundedSavingTotal_value] at h
  norm_num at h
  constructor <;> linarith [h.1, h.2]

theorem primeSavingSeries_enclosure :
    (12025657733612918002543146 : ℝ) / 10 ^ 22 < primeSavingSeries ∧
      primeSavingSeries < (12025657733612918002543149 : ℝ) / 10 ^ 22 := by
  have hw : (12025657733612918002543147 : ℝ) / 10 ^ 22 < (primeSavingApproxRat : ℝ) ∧
      (primeSavingApproxRat : ℝ) < (12025657733612918002543148 : ℝ) / 10 ^ 22 := by
    constructor
    · simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
        (Rat.cast_lt (K := ℝ)).mpr primeSavingApproxRat_enclosure.1
    · simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
        (Rat.cast_lt (K := ℝ)).mpr primeSavingApproxRat_enclosure.2
  have he := abs_lt.mp primeSavingApproxRat_error_decimal
  constructor <;> linarith [hw.1, hw.2, he.1, he.2]

set_option maxRecDepth 100000 in
theorem logTwoApproxRat_enclosure :
    (6931471805599453094172321214581765680755 : ℚ) / 10 ^ 40 < logTwoApproxRat ∧
      logTwoApproxRat < (6931471805599453094172321214581765680756 : ℚ) / 10 ^ 40 := by
  decide +kernel

theorem logTwo_enclosure :
    (6931471805599453094172321214581765680755 : ℝ) / 10 ^ 40 < Real.log 2 ∧
      Real.log 2 < (6931471805599453094172321214581765680756 : ℝ) / 10 ^ 40 +
        (15 : ℝ) / 10 ^ 51 := by
  have hl : (6931471805599453094172321214581765680755 : ℝ) / 10 ^ 40 <
      (logTwoApproxRat : ℝ) ∧ (logTwoApproxRat : ℝ) <
        (6931471805599453094172321214581765680756 : ℝ) / 10 ^ 40 := by
    constructor
    · simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
        (Rat.cast_lt (K := ℝ)).mpr logTwoApproxRat_enclosure.1
    · simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
        (Rat.cast_lt (K := ℝ)).mpr logTwoApproxRat_enclosure.2
  constructor
  · linarith [hl.1, logTwoApproxRat_error.1]
  · linarith [hl.2, logTwoApproxRat_error_decimal]

theorem normalizationCost_enclosure :
    (539993819198880114452898006 : ℝ) / 10 ^ 27 < normalizationCost primeSavingSeries ∧
      normalizationCost primeSavingSeries < (539993819198880114452898061 : ℝ) / 10 ^ 27 := by
  rw [normalizationCost_explicit]
  have hw := primeSavingSeries_enclosure
  have hl := logTwo_enclosure
  constructor <;> linarith [hw.1, hw.2, hl.1, hl.2]

end PiIrrationality
