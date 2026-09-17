import Formalization.ConstructionSavingAsymptotic
import Formalization.ConstructionIntegerLinearForm
import Formalization.LocalOptimality
import Formalization.HataRateCriterion

/-! Growth of the actual integer coefficient after the arithmetic normalization. -/

namespace PiIrrationality

open Filter
open scoped Topology

theorem constructionIntegerV_log_limit_near_candidate : ∀ᶠ p in 𝓝 candidate,
    ∀ a b c : ℕ, 0 < c → Even c → constructionParameter a b c = p →
      Tendsto (fun n : ℕ => Real.log |(constructionIntegerV a b c n : ℝ)| /
        ((c : ℝ) * n)) atTop
        (𝓝 (parameterCoefficientRate p + parameterCost p)) := by
  filter_upwards [construction_coefficient_saddle_near_candidate,
    construction_pi_coeff_growth_near_candidate] with p hs hv
  intro a b c hc he hrep
  have hp : Admissible (constructionParameter a b c) := hrep ▸ (hs a b c hc hrep).1
  have hvr : Tendsto (fun n : ℕ => Real.log |(constructionRationalV a b c n : ℝ)| /
      ((c : ℝ) * n)) atTop (𝓝 (parameterCoefficientRate p)) := by
    simpa only [constructionRationalV] using (hv a b c hc he hrep).2
  have hnorm := constructionNormalizationMultiplier_log_limit hc he hp
  have hnorm' := hnorm.div_const (c : ℝ)
  have hnorm'' : Tendsto (fun n : ℕ =>
        Real.log (constructionNormalizationMultiplier a b c n : ℝ) /
          ((c : ℝ) * (n : ℝ))) atTop
        (𝓝 (((constructionDegree a b c : ℝ) -
          (constructionTwoSaving b c : ℝ) * Real.log 2 -
          (c : ℝ) * savingPhi (constructionParameter a b c)) / (c : ℝ))) := by
    apply hnorm'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    field_simp
  have hsum := hnorm''.add hvr
  have hEq (n : ℕ) (hn : 0 < n) :
        Real.log |(constructionIntegerV a b c n : ℝ)| /
            ((c : ℝ) * (n : ℝ)) =
          Real.log (constructionNormalizationMultiplier a b c n : ℝ) /
            ((c : ℝ) * (n : ℝ)) +
          Real.log |(constructionRationalV a b c n : ℝ)| /
            ((c : ℝ) * (n : ℝ)) := by
    have hcast := constructionIntegerV_cast hc he hp hn
    have hcastR : (constructionIntegerV a b c n : ℝ) =
          (constructionNormalizationMultiplier a b c n : ℝ) *
            (constructionRationalV a b c n : ℝ) := by
      exact_mod_cast hcast
    have hmpos : 0 < (constructionNormalizationMultiplier a b c n : ℝ) := by
      exact_mod_cast (constructionNormalizationMultiplier_pos a b c n)
    rw [hcastR, abs_mul, abs_of_pos hmpos]
    have hq := constructionRationalV_neg hc he hp n
    have hqR : (constructionRationalV a b c n : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_lt hq)
    rw [Real.log_mul (by positivity) (abs_ne_zero.mpr hqR)]
    field_simp
  have hconv := hsum.congr'
    (show (fun n : ℕ =>
      Real.log (constructionNormalizationMultiplier a b c n : ℝ) /
        ((c : ℝ) * n) + Real.log |(constructionRationalV a b c n : ℝ)| /
          ((c : ℝ) * n)) =ᶠ[atTop]
      (fun n : ℕ => Real.log |(constructionIntegerV a b c n : ℝ)| /
        ((c : ℝ) * n)) by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      exact (hEq n hn).symm)
  convert hconv using 1
  rw [constructionNormalizationRate_eq_parameterCost hc he hp]
  rw [hrep]
  ring

theorem construction_hata_bound_of_rates {p : ℝ × ℝ} {a b c : ℕ}
    (hc : 0 < c) (hs : 0 < parameterCoefficientRate p + parameterCost p)
    (ht : 0 < -parameterIntegralRate p - parameterCost p)
    (hV : Tendsto (fun n : ℕ => Real.log |(constructionIntegerV a b c n : ℝ)| /
      ((c : ℝ) * n)) atTop (𝓝 (parameterCoefficientRate p + parameterCost p)))
    (hL : limsup (fun n : ℕ =>
      ((Real.log |linearForm Real.pi (constructionIntegerU a b c n)
        (constructionIntegerV a b c n)| / ((c : ℝ) * n) : ℝ) : EReal)) atTop ≤
      ((parameterIntegralRate p + parameterCost p : ℝ) : EReal)) :
    IrrationalityMeasureAtMost Real.pi (parameterAuxiliaryBound p) := by
  have hL' : limsup (fun n : ℕ =>
      ((Real.log |linearForm Real.pi (constructionIntegerU a b c n)
        (constructionIntegerV a b c n)| / ((c : ℝ) * n) : ℝ) : EReal)) atTop ≤
      ((-(-parameterIntegralRate p - parameterCost p) : ℝ) : EReal) := by
    simpa only [neg_sub, sub_neg_eq_add, add_comm] using hL
  have h := hata_irrationality_bound irrational_pi hs ht (by exact_mod_cast hc)
    hV hL'
  simpa only [parameterAuxiliaryBound, AuxiliaryBound] using h

end PiIrrationality
