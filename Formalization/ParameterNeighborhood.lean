import Formalization.ParameterContour
import Formalization.LocalOptimality

/-! One common parameter neighborhood for the strict conditions of Section 6.7. -/

namespace PiIrrationality

open Filter
open scoped Topology

theorem parameterRate_candidate_margins :
    3 < parameterCoefficientRate candidate + parameterCost candidate ∧
    (3 : ℝ) / 5 < -parameterIntegralRate candidate - parameterCost candidate := by
  rw [parameterRate_numerator_candidate, parameterRate_denominator_candidate]
  constructor
  · linarith [paperSigma_enclosure.1]
  · linarith [paperTau_enclosure.1]

theorem parameterRates_positive_near_candidate : ∀ᶠ p in 𝓝 candidate,
    3 < parameterCoefficientRate p + parameterCost p ∧
    (3 : ℝ) / 5 < -parameterIntegralRate p - parameterCost p := by
  have hc := continuousAt_parameterCost candidate_admissible
  exact ((analyticAt_parameterCoefficientRate.continuousAt.add hc).eventually_const_lt
    parameterRate_candidate_margins.1).and
    ((analyticAt_parameterIntegralRate.continuousAt.neg.sub hc).eventually_const_lt
      parameterRate_candidate_margins.2)

theorem parameterConstruction_common_neighborhood :
    ∃ radius : ℝ, 0 < radius ∧ ∀ p : ℝ × ℝ,
      parameterNormOne (p - candidate) < radius →
      Admissible p ∧ 0 < savingPhi p ∧
      AnalyticAt ℝ parameterRealSaddle p ∧ AnalyticAt ℝ parameterComplexSaddle p ∧
      AnalyticAt ℝ parameterCoefficientRate p ∧ AnalyticAt ℝ parameterIntegralRate p ∧
      (parameterStationary p (parameterRealSaddle p) = 0 ∧ 25 < parameterRealSaddle p) ∧
      (parameterStationaryComplex p (parameterComplexSaddle p) = 0 ∧
        0 < (parameterComplexSaddle p).im) ∧
      ((9 : ℝ) / 10 < parameterSaddleEta p ∧ parameterSaddleEta p < 23 / 25 ∧
        (12 : ℝ) / 25 < parameterSaddleLambda p ∧ parameterSaddleLambda p < 49 / 100 ∧
        gammaPath (parameterSaddleEta p) (parameterSaddleLambda p) = parameterComplexSaddle p) ∧
      3 < parameterCoefficientRate p + parameterCost p ∧
      (3 : ℝ) / 5 < -parameterIntegralRate p - parameterCost p := by
  have h := savingPhi_pos_near_candidate.and
    (analyticAt_parameterRealSaddle.eventually_analyticAt.and
      (analyticAt_parameterComplexSaddle.eventually_analyticAt.and
        (analyticAt_parameterCoefficientRate.eventually_analyticAt.and
          (analyticAt_parameterIntegralRate.eventually_analyticAt.and
            (parameterRealSaddle_near_candidate.and
              (parameterComplexSaddle_near_candidate.and
                (parameterContour_near_candidate.and parameterRates_positive_near_candidate)))))))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨min r (1 / 5570), by positivity, ?_⟩
  intro p hp
  have ha := admissible_candidate_add_of_parameterNormOne_lt
    (hp.trans_le (min_le_right r (1 / 5570)))
  have he : candidate + (p - candidate) = p := by abel
  rw [he] at ha
  refine ⟨ha, hball ?_⟩
  rw [dist_eq_norm]
  exact (norm_le_parameterNormOne _).trans_lt (hp.trans_le (min_le_left _ _))

end PiIrrationality
