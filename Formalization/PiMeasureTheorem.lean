import Formalization.HataRateCriterion
import Formalization.IrrationalityMeasureBounds
import Formalization.PaperRateNumerics

/-! The unconditional irrationality-measure bound of Theorem 1.1. -/

namespace PiIrrationality

theorem pi_irrationalityMeasureAtMost :
    IrrationalityMeasureAtMost Real.pi paperAuxiliaryValue := by
  exact hata_irrationality_bound irrational_pi paperSigma_pos paperTau_pos
    (show (0 : ℝ) < 5570 by norm_num) paper_integerCoeffV_log_limit paper_linearForm_log_limsup

theorem pi_irrationalityMeasure_le_auxiliary :
    IrrationalityMeasure Real.pi ≤ paperAuxiliaryValue :=
  irrationalityMeasure_le_of_atMost Real.pi paperAuxiliaryValue
    (irrationalityMeasure_exponents_bddBelow Real.pi) pi_irrationalityMeasureAtMost

theorem theorem11_proof : theorem11 :=
  pi_irrationalityMeasure_le_auxiliary.trans_lt paperAuxiliaryValue_lt_cutoff

end PiIrrationality
