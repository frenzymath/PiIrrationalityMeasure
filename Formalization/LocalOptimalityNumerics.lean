import Formalization.LocalOptimality
import Formalization.LocalOptimization

/-! The sensitivity coefficient (6.56)--(6.57) and diagonal check (6.60). -/

namespace PiIrrationality

noncomputable def candidateSensitivity : ℝ :=
  (parameterCoefficientRate candidate - parameterIntegralRate candidate) /
    (-parameterIntegralRate candidate - parameterCost candidate) ^ 2

theorem candidateSensitivity_eq_rates :
    candidateSensitivity = (paperSigma + paperTau) / paperTau ^ 2 := by
  have h := parameterRate_numerator_candidate
  have h' := parameterRate_denominator_candidate
  unfold candidateSensitivity
  rw [h']
  congr 1
  linarith

theorem candidateSensitivity_bounds : 11 < candidateSensitivity ∧ candidateSensitivity < 12 := by
  rw [candidateSensitivity_eq_rates]
  have hs0 : (387 : ℝ) / 100 < paperSigma := by linarith [paperSigma_enclosure.1]
  have hs1 : paperSigma < (388 : ℝ) / 100 := by linarith [paperSigma_enclosure.2]
  have ht0 : (634 : ℝ) / 1000 < paperTau := by linarith [paperTau_enclosure.1]
  have ht1 : paperTau < (635 : ℝ) / 1000 := by linarith [paperTau_enclosure.2]
  have ht0sq : ((634 : ℝ) / 1000) ^ 2 < paperTau ^ 2 :=
    (sq_lt_sq₀ (by norm_num) paperTau_pos.le).mpr ht0
  have ht1sq : paperTau ^ 2 < ((635 : ℝ) / 1000) ^ 2 :=
    (sq_lt_sq₀ paperTau_pos.le (by norm_num)).mpr ht1
  have hden : 0 < paperTau ^ 2 := sq_pos_of_pos paperTau_pos
  exact ⟨(lt_div_iff₀ hden).mpr (by linarith), (div_lt_iff₀ hden).mpr (by linarith)⟩

theorem auxiliaryH_candidate_hasDerivAt :
    HasDerivAt
      (auxiliaryH (parameterCoefficientRate candidate) (parameterIntegralRate candidate)
        (parameterSmoothCost candidate))
      (-candidateSensitivity) (savingPhi candidate) := by
  have hden : -parameterIntegralRate candidate - parameterSmoothCost candidate +
      savingPhi candidate = paperTau := by
    have h := parameterRate_denominator_candidate
    unfold parameterCost at h
    linarith
  have h := auxiliaryH_hasDerivAt (r := parameterCoefficientRate candidate)
    (ne_of_gt (hden.symm ▸ paperTau_pos))
  convert h using 1
  unfold candidateSensitivity parameterCost
  ring

theorem candidateSectorVariation_diagonal :
    candidateSectorVariation ((1 : ℝ) / 2, 1) = -(557 : ℝ) / 2759502 ∧
    candidateSectorVariation (-(1 : ℝ) / 2, -1) = -(557 : ℝ) / 2759502 := by
  have hp : CandidateClosedSector 1 ((1 : ℝ) / 2, 1) := by
    apply candidateClosedSector_of_det <;>
      dsimp [candidateSectorRayReal, candidateSectorRay, candidateSectorNext] <;> norm_num
  have hm : CandidateClosedSector 7 (-(1 : ℝ) / 2, -1) := by
    convert hp.neg using 1 <;> norm_num [Fin.ext_iff] <;> decide +kernel
  rw [candidateSectorVariation_eq_form hp, candidateSectorVariation_eq_form hm]
  norm_num [candidateSectorLinearForm, candidateSectorRow, sectorRows]

theorem candidate_diagonal_leading_coefficient_pos :
    0 < candidateSensitivity * ((557 : ℝ) / 2759502) := by
  have h : 0 < candidateSensitivity := by linarith [candidateSensitivity_bounds.1]
  exact mul_pos h (by norm_num)

end PiIrrationality
