import Formalization.ConstructionCoefficientExtraction
import Formalization.RationalPoleIntegral

/-! The actual integral is a rational linear form with the extracted nonzero pi coefficient. -/

namespace PiIrrationality

open Polynomial

noncomputable def constructionRationalU (a b c n : ℕ) : ℚ :=
  verticalPolynomialIntegralRat (constructionPolynomialPart a b c n) +
    ∑ j ∈ Finset.Icc 1 (c * n), constructionLaurentCoeff a b c n j * poleIntegralRat j

noncomputable def constructionRationalV (a b c n : ℕ) : ℚ :=
  -constructionLaurentCoeff a b c n 0 / 2

theorem constructionVertical_partialFractions (a b c n : ℕ) (s : ℝ) :
    constructionDensity a b c n (verticalSegment s) =
      aeval (verticalSegment s) (constructionPolynomialPart a b c n) +
        (constructionLaurentCoeff a b c n 0 : ℂ) * polePair 0 s +
          ∑ j ∈ Finset.Icc 1 (c * n),
            (constructionLaurentCoeff a b c n (j : ℤ) : ℂ) * polePair j s := by
  have hleft : verticalSegment s + 5 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num [verticalSegment] at this
  have hright : verticalSegment s - 5 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num [verticalSegment] at this
  rw [constructionDensity, construction_partialFractions a b c n _ hleft hright]
  simp_rw [← polePair_eq_nat]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (constructionLaurentCoeff a b c n (j : ℤ) : ℂ) * polePair j s)]
  have hrange : Finset.range (c * n + 1) = insert 0 (Finset.Icc 1 (c * n)) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hrange, Finset.sum_insert (by simp)]
  simp only [Nat.cast_zero]
  ring

theorem constructionIntegral_rational_linearForm (a b c n : ℕ) :
    constructionIntegral a b c n =
      (constructionRationalU a b c n : ℂ) + (constructionRationalV a b c n : ℂ) * Real.pi := by
  have hp := ((constructionPolynomialPart a b c n).continuous_aeval.comp
    verticalSegment_continuous).intervalIntegrable (μ := MeasureTheory.volume) (-2) 2
  have hlog := ((continuous_const (y := (constructionLaurentCoeff a b c n 0 : ℂ))).mul
    (polePair_continuous 0)).intervalIntegrable (μ := MeasureTheory.volume) (-2) 2
  have hncont : Continuous (fun s : ℝ => ∑ j ∈ Finset.Icc 1 (c * n),
      (constructionLaurentCoeff a b c n (j : ℤ) : ℂ) * polePair j s) :=
    continuous_finsetSum _ fun j _ => continuous_const.mul (polePair_continuous j)
  have hnonlog := hncont.intervalIntegrable (μ := MeasureTheory.volume) (-2) 2
  dsimp only [Function.comp_def, Pi.mul_apply] at hp hlog
  change IntervalIntegrable (fun s : ℝ => (constructionLaurentCoeff a b c n 0 : ℂ) * polePair 0 s)
    MeasureTheory.volume (-2) 2 at hlog
  unfold constructionIntegral
  simp_rw [constructionVertical_partialFractions]
  rw [intervalIntegral.integral_add (hp.add hlog) hnonlog, intervalIntegral.integral_add hp hlog]
  have hP := verticalPolynomial_integral_rat (constructionPolynomialPart a b c n)
  have hN := rational_nonlog_pole_integral (c * n) (fun j => constructionLaurentCoeff a b c n j)
  have hL : -(∫ s : ℝ in (-2)..2, (constructionLaurentCoeff a b c n 0 : ℂ) * polePair 0 s) =
      (constructionRationalV a b c n : ℂ) * Real.pi := by
    rw [intervalIntegral.integral_const_mul, logarithmicPole_integral]
    unfold constructionRationalV
    push_cast
    ring
  unfold constructionRationalU
  push_cast
  push_cast at hN
  linear_combination hP + hN + hL

theorem constructionRationalV_neg {a b c : ℕ} (hc : 0 < c) (hce : Even c)
    (hp : Admissible (constructionParameter a b c)) (n : ℕ) : constructionRationalV a b c n < 0 :=
  div_neg_of_neg_of_pos (neg_neg_of_pos (constructionLaurentCoeff_zero_pos hc hce hp n))
    (by norm_num)

theorem rational_pi_linearForm_ne_zero (u v : ℚ) (hv : v ≠ 0) :
    (u : ℝ) + (v : ℝ) * Real.pi ≠ 0 := by
  intro hzero
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hpi : Real.pi = ((-u / v : ℚ) : ℝ) := by
    push_cast
    apply (eq_div_iff hv').mpr
    linarith
  exact irrational_pi.ne_rat (-u / v) hpi

theorem constructionIntegral_re_ne_zero {a b c : ℕ} (hc : 0 < c) (hce : Even c)
    (hp : Admissible (constructionParameter a b c)) (n : ℕ) :
    (constructionIntegral a b c n).re ≠ 0 := by
  have h := congrArg Complex.re (constructionIntegral_rational_linearForm a b c n)
  norm_num only [Complex.add_re, Complex.mul_re, Complex.ratCast_re, Complex.ratCast_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h
  rw [h]
  exact rational_pi_linearForm_ne_zero _ _ (constructionRationalV_neg hc hce hp n).ne

theorem constructionIntegral_ne_zero {a b c : ℕ} (hc : 0 < c) (hce : Even c)
    (hp : Admissible (constructionParameter a b c)) (n : ℕ) :
    constructionIntegral a b c n ≠ 0 := by
  intro h
  exact constructionIntegral_re_ne_zero hc hce hp n (by rw [h, Complex.zero_re])

end PiIrrationality
