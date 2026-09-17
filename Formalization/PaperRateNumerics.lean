import Formalization.IntegerLinearFormDecay
import Formalization.IntegralDecayNumerics
import Formalization.CoefficientGrowthNumerics
import Formalization.PrimeSavingNumerics

/-! Exact endpoint arithmetic for the actual rates and bound in (5.18)--(5.23). -/

namespace PiIrrationality

theorem paperSigma_enclosure :
    (387193780537717945273573050982326 : ℝ) / 10 ^ 32 < paperSigma ∧
      paperSigma < (387193780537717945273573056482327 : ℝ) / 10 ^ 32 := by
  have hr := coefficientGrowthRate_enclosure
  have hc := normalizationCost_enclosure
  unfold paperSigma
  constructor <;> linarith [hr.1, hr.2, hc.1, hc.2]

theorem paperTau_enclosure :
    (634550122111144993989685131 : ℝ) / 10 ^ 27 < paperTau ∧
      paperTau < (634550122111144993989685225 : ℝ) / 10 ^ 27 := by
  have hs := integralDecayRate_enclosure
  have hc := normalizationCost_enclosure
  unfold paperTau
  constructor <;> linarith [hs.1, hs.2, hc.1, hc.2]

theorem paperSigma_pos : 0 < paperSigma := by linarith [paperSigma_enclosure.1]

theorem paperTau_pos : 0 < paperTau := by linarith [paperTau_enclosure.1]

theorem paperAuxiliaryValue_enclosure :
    (7101862832356350795733674505 : ℝ) / 10 ^ 27 < paperAuxiliaryValue ∧
      paperAuxiliaryValue < (7101862832356350795733675497 : ℝ) / 10 ^ 27 := by
  have hs := paperSigma_enclosure
  have ht := paperTau_enclosure
  unfold paperAuxiliaryValue
  constructor
  · have h : ((7101862832356350795733674505 : ℝ) / 10 ^ 27 - 1) * paperTau <
        paperSigma := by linarith [hs.1, ht.2]
    have hd := (lt_div_iff₀ paperTau_pos).mpr h
    linarith
  · have h : paperSigma <
        ((7101862832356350795733675497 : ℝ) / 10 ^ 27 - 1) * paperTau := by
      linarith [hs.2, ht.1]
    have hd := (div_lt_iff₀ paperTau_pos).mpr h
    linarith

theorem paperAuxiliaryValue_lt_cutoff : paperAuxiliaryValue < (7101862832357 : ℝ) / 10 ^ 12 := by
  linarith [paperAuxiliaryValue_enclosure.2]

end PiIrrationality
