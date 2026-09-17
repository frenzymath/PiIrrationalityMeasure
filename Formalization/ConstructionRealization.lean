import Formalization.ConstructionIntegerDecay

/-! Proposition 6.4: rational parameters are realized by the actual integer forms. -/

namespace PiIrrationality

open Filter
open scoped Topology

theorem proposition_6_4 :
    ∃ radius : ℝ, 0 < radius ∧ ∀ x y : ℚ,
      parameterNormOne (((x : ℝ), (y : ℝ)) - candidate) < radius →
      ∀ N : ℕ, ∃ a b c : ℕ,
        0 < a ∧ 0 < b ∧ N < c ∧ Even c ∧
        constructionParameter a b c = ((x : ℝ), (y : ℝ)) ∧
        Admissible ((x : ℝ), (y : ℝ)) ∧ 0 < savingPhi ((x : ℝ), (y : ℝ)) ∧
        (1 ≤ a + b - c ∧ 1 ≤ 2 * b - c ∧ 7 * b ≤ 5 * c - 1 ∧
          1 ≤ constructionDegree a b c - c) ∧
        (∀ n : ℕ, 0 < n →
          (constructionNormalizationMultiplier a b c n : ℂ) * constructionIntegral a b c n =
            (constructionIntegerU a b c n : ℂ) +
              (constructionIntegerV a b c n : ℂ) * Real.pi ∧
          (constructionIntegerV a b c n : ℚ) =
            constructionNormalizationMultiplier a b c n * constructionRationalV a b c n ∧
          constructionIntegerV a b c n < 0) ∧
        Tendsto (fun n : ℕ => Real.log (constructionPhi a b c n : ℝ) / ((c : ℝ) * n))
          atTop (𝓝 (savingPhi ((x : ℝ), (y : ℝ)))) ∧
        Tendsto (fun n : ℕ =>
          Real.log (constructionNormalizationMultiplier a b c n : ℝ) / ((c : ℝ) * n))
          atTop (𝓝 (parameterCost ((x : ℝ), (y : ℝ)))) ∧
        Tendsto (fun n : ℕ => Real.log |(constructionIntegerV a b c n : ℝ)| /
          ((c : ℝ) * n)) atTop
          (𝓝 (parameterCoefficientRate ((x : ℝ), (y : ℝ)) +
            parameterCost ((x : ℝ), (y : ℝ)))) ∧
        limsup (fun n : ℕ =>
          ((Real.log |linearForm Real.pi (constructionIntegerU a b c n)
            (constructionIntegerV a b c n)| / ((c : ℝ) * n) : ℝ) : EReal)) atTop ≤
          ((parameterIntegralRate ((x : ℝ), (y : ℝ)) +
            parameterCost ((x : ℝ), (y : ℝ)) : ℝ) : EReal) ∧
        0 < parameterCoefficientRate ((x : ℝ), (y : ℝ)) +
          parameterCost ((x : ℝ), (y : ℝ)) ∧
        0 < -parameterIntegralRate ((x : ℝ), (y : ℝ)) -
          parameterCost ((x : ℝ), (y : ℝ)) ∧
        IrrationalityMeasureAtMost Real.pi (parameterAuxiliaryBound ((x : ℝ), (y : ℝ))) := by
  have hnear := constructionIntegerV_log_limit_near_candidate.and
    (construction_linearForm_limsup_near_candidate.and
      (parameterRates_positive_near_candidate.and savingPhi_pos_near_candidate))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨min r (1 / 5570), by positivity, ?_⟩
  intro x y hdist N
  let p : ℝ × ℝ := ((x : ℝ), (y : ℝ))
  have hp : Admissible p := by
    have h := admissible_candidate_add_of_parameterNormOne_lt
      (hdist.trans_le (min_le_right r (1 / 5570)))
    simpa only [add_sub_cancel] using h
  have hballp : dist p candidate < r := by
    rw [dist_eq_norm]
    exact (norm_le_parameterNormOne _).trans_lt (hdist.trans_le (min_le_left _ _))
  obtain ⟨hV, hL, hpos, hPhi⟩ := hball hballp
  obtain ⟨a, b, c, ha, hb, hc, he, hrep, hm⟩ := admissible_rational_construction hp N
  have hc0 : 0 < c := by omega
  have hcR : (c : ℝ) ≠ 0 := by positivity
  have hac : Admissible (constructionParameter a b c) := hrep ▸ hp
  have hphi := (constructionPhi_log_limit hc0 hac).div_const (c : ℝ)
  rw [mul_div_cancel_left₀ _ hcR, hrep] at hphi
  have hphi' : Tendsto (fun n : ℕ => Real.log (constructionPhi a b c n : ℝ) /
      ((c : ℝ) * n)) atTop (𝓝 (savingPhi p)) := by
    simpa only [div_div, mul_comm] using hphi
  have hnorm := constructionNormalizationCost_limit hc0 he hac
  rw [hrep] at hnorm
  have hs : 0 < parameterCoefficientRate p + parameterCost p := by linarith [hpos.1]
  have ht : 0 < -parameterIntegralRate p - parameterCost p := by linarith [hpos.2]
  exact ⟨a, b, c, ha, hb, hc, he, hrep, hp, hPhi, hm,
    fun n hn => ⟨construction_integer_linearForm hc0 he hac hn,
      constructionIntegerV_cast hc0 he hac hn, constructionIntegerV_neg hc0 he hac hn⟩,
    hphi', hnorm, hV a b c hc0 he hrep, hL a b c hc0 he hrep, hs, ht,
    construction_hata_bound_of_rates hc0 hs ht
      (hV a b c hc0 he hrep) (hL a b c hc0 he hrep)⟩

end PiIrrationality
