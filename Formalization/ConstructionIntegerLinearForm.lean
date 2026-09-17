import Formalization.ConstructionPolynomialIntegral
import Formalization.ConstructionPoleIntegral

/-! The actual general normalized integer linear forms in (6.62). -/

namespace PiIrrationality

theorem constructionNormalizationMultiplier_eight_common (a b c n : ℕ) :
    constructionNormalizationMultiplier a b c n =
      8 * ((2 : ℚ) ^ (1 - (constructionTwoSaving b c : ℤ) * n) *
        constructionReducedLcm a b c n) := by
  unfold constructionNormalizationMultiplier
  rw [show 4 - (constructionTwoSaving b c : ℤ) * n =
      3 + (1 - (constructionTwoSaving b c : ℤ) * n) by omega,
    zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  norm_num
  ring

theorem construction_normalized_rationalU_integral {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n) :
    ∃ U : ℤ, constructionNormalizationMultiplier a b c n * constructionRationalU a b c n =
      (U : ℚ) := by
  obtain ⟨P, hP⟩ := constructionNormalizedPolynomialIntegral_integral hc he hp hn
  have hP' : (2 : ℚ) ^ (1 - (constructionTwoSaving b c : ℤ) * n) *
      constructionReducedLcm a b c n *
        verticalPolynomialIntegralRat (constructionPolynomialPart a b c n) = (P : ℚ) := by
    apply Rat.cast_injective (α := ℂ)
    rw [constructionNormalizedPolynomialIntegral, verticalPolynomial_integral_rat] at hP
    push_cast
    exact hP
  obtain ⟨Q, hQ⟩ := construction_normalized_nonlog_integral hc he hp hn
  refine ⟨8 * (P + Q), ?_⟩
  rw [constructionNormalizationMultiplier_eight_common, constructionRationalU]
  calc
    _ = 8 * ((2 : ℚ) ^ (1 - (constructionTwoSaving b c : ℤ) * n) *
        constructionReducedLcm a b c n *
          verticalPolynomialIntegralRat (constructionPolynomialPart a b c n) +
        (2 : ℚ) ^ (1 - (constructionTwoSaving b c : ℤ) * n) *
          constructionReducedLcm a b c n *
            (∑ j ∈ Finset.Icc 1 (c * n), constructionLaurentCoeff a b c n (j : ℤ) *
              poleIntegralRat j)) := by ring
    _ = _ := by rw [hP', hQ]; push_cast; rfl

noncomputable def constructionIntegerU (a b c n : ℕ) : ℤ :=
  (constructionNormalizationMultiplier a b c n * constructionRationalU a b c n).num

noncomputable def constructionIntegerV (a b c n : ℕ) : ℤ :=
  (constructionNormalizedPiCoeff a b c n).num

theorem constructionIntegerU_cast {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n) :
    (constructionIntegerU a b c n : ℚ) =
      constructionNormalizationMultiplier a b c n * constructionRationalU a b c n := by
  obtain ⟨U, hU⟩ := construction_normalized_rationalU_integral hc he hp hn
  simp only [constructionIntegerU, hU, Rat.num_intCast]

theorem constructionIntegerV_cast {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n) :
    (constructionIntegerV a b c n : ℚ) =
      constructionNormalizationMultiplier a b c n * constructionRationalV a b c n := by
  obtain ⟨V, hV⟩ := constructionNormalizedPiCoeff_integral hc he hp hn
  change ((constructionNormalizedPiCoeff a b c n).num : ℚ) = constructionNormalizedPiCoeff a b c n
  rw [hV, Rat.num_intCast]

theorem constructionIntegerV_neg {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n) :
    constructionIntegerV a b c n < 0 := by
  have h := constructionNormalizedPiCoeff_neg hc he hp n
  rw [constructionNormalizedPiCoeff, ← constructionIntegerV_cast hc he hp hn] at h
  exact_mod_cast h

theorem construction_integer_linearForm {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n) :
    (constructionNormalizationMultiplier a b c n : ℂ) * constructionIntegral a b c n =
      (constructionIntegerU a b c n : ℂ) + (constructionIntegerV a b c n : ℂ) * Real.pi := by
  have hU := congrArg (fun q : ℚ => (q : ℂ)) (constructionIntegerU_cast hc he hp hn)
  have hV := congrArg (fun q : ℚ => (q : ℂ)) (constructionIntegerV_cast hc he hp hn)
  push_cast at hU hV
  rw [constructionIntegral_rational_linearForm, hU, hV]
  ring

theorem construction_real_integer_linearForm {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n) :
    (constructionNormalizationMultiplier a b c n : ℝ) * (constructionIntegral a b c n).re =
      (constructionIntegerU a b c n : ℝ) + (constructionIntegerV a b c n : ℝ) * Real.pi := by
  have h := congrArg Complex.re (construction_integer_linearForm hc he hp hn)
  simpa only [Complex.mul_re, Complex.add_re, Complex.ratCast_re, Complex.ratCast_im,
    Complex.intCast_re, Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero] using h

theorem construction_integer_linearForm_ne_zero {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n) :
    (constructionIntegerU a b c n : ℝ) + (constructionIntegerV a b c n : ℝ) * Real.pi ≠ 0 := by
  rw [← construction_real_integer_linearForm hc he hp hn]
  exact mul_ne_zero (by exact_mod_cast (constructionNormalizationMultiplier_pos a b c n).ne')
    (constructionIntegral_re_ne_zero hc he hp n)

theorem admissible_rational_integer_forms {x y : ℚ}
    (hp : Admissible ((x : ℝ), (y : ℝ))) (N : ℕ) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ N < c ∧ Even c ∧
      constructionParameter a b c = ((x : ℝ), (y : ℝ)) ∧
      ∀ n : ℕ, 0 < n → constructionIntegerV a b c n < 0 ∧
        (constructionNormalizationMultiplier a b c n : ℂ) * constructionIntegral a b c n =
          (constructionIntegerU a b c n : ℂ) + (constructionIntegerV a b c n : ℂ) * Real.pi := by
  obtain ⟨a, b, c, ha, hb, hc, he, hrep, _⟩ := admissible_rational_construction hp N
  have hc0 : 0 < c := by omega
  have hp' : Admissible (constructionParameter a b c) := hrep ▸ hp
  exact ⟨a, b, c, ha, hb, hc, he, hrep, fun n hn =>
    ⟨constructionIntegerV_neg hc0 he hp' hn, construction_integer_linearForm hc0 he hp' hn⟩⟩

end PiIrrationality
