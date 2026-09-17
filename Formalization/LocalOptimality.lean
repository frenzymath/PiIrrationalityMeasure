import Formalization.ParameterRates
import Formalization.LocalMinimumAssembly
import Formalization.ParameterChamber
import Formalization.PaperRateNumerics

/-! Theorem 1.2 and the all-real-parameters conclusion of Theorem 6.3. -/

namespace PiIrrationality

noncomputable def parameterAuxiliaryBound : ℝ × ℝ → ℝ :=
  AuxiliaryBound parameterCoefficientRate parameterIntegralRate parameterCost

theorem parameterRate_numerator_candidate :
    parameterCoefficientRate candidate + parameterCost candidate = paperSigma := by
  rw [parameterCoefficientRate_candidate, parameterCost_candidate]
  rfl

theorem parameterRate_denominator_candidate :
    -parameterIntegralRate candidate - parameterCost candidate = paperTau := by
  rw [parameterIntegralRate_candidate, parameterCost_candidate]
  rfl

theorem parameterAuxiliaryBound_candidate : parameterAuxiliaryBound candidate = paperAuxiliaryValue := by
  unfold parameterAuxiliaryBound AuxiliaryBound
  rw [parameterRate_numerator_candidate, parameterRate_denominator_candidate]
  rfl

theorem theorem12_proof : theorem12 parameterCoefficientRate parameterIntegralRate parameterCost := by
  apply theorem12_of_differentiable_rates parameterCoefficientRate parameterIntegralRate
    analyticAt_parameterCoefficientRate.differentiableAt analyticAt_parameterIntegralRate.differentiableAt
  · rw [parameterRate_numerator_candidate]
    exact paperSigma_pos
  · rw [parameterRate_denominator_candidate]
    exact paperTau_pos

theorem parameterAuxiliaryBound_strictLocalMinimizer :
    StrictLocalMinimizer parameterAuxiliaryBound Admissible candidate := theorem12_proof

theorem theorem63_proof :
    ∃ delta : ℝ, 0 < delta ∧ ∀ p : ℝ × ℝ, p ≠ candidate →
      parameterNormOne (p - candidate) < delta →
      Admissible p ∧ parameterAuxiliaryBound candidate < parameterAuxiliaryBound p := by
  obtain ⟨r, hr, hmin⟩ := parameterAuxiliaryBound_strictLocalMinimizer
  refine ⟨min r (1 / 5570), by positivity, ?_⟩
  intro p hp hdist
  have hch := admissible_candidate_add_of_parameterNormOne_lt
    (hdist.trans_le (min_le_right r (1 / 5570)))
  have he : candidate + (p - candidate) = p := by abel
  rw [he] at hch
  exact ⟨hch, hmin p hch hp
    ((norm_le_parameterNormOne _).trans_lt (hdist.trans_le (min_le_left _ _)))⟩

end PiIrrationality
