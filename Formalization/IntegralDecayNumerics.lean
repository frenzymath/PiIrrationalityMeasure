import Formalization.IntegralDecay
import Formalization.SaddleModuli
import Formalization.SaddleLogCertificate

/-! The actual complex phase value, with the strict printed enclosure (4.21). -/

namespace PiIrrationality

theorem integralDecayRate_eq_log_moduli :
    integralDecayRate = (1857 : ℝ) / 11140 * Real.log saddleNormSq +
      (1857 : ℝ) / 5570 * Real.log saddleQuadraticNormSq -
        (1 : ℝ) / 2 * Real.log saddlePoleNormSq := by
  rw [← saddleUpper_normSq]
  unfold integralDecayRate complexPhase saddleQuadraticNormSq saddlePoleNormSq
  simp only [log_complex_normSq]
  ring

theorem integralDecayRate_enclosure :
    -(1174543941310025108442583231 : ℝ) / 10 ^ 27 < integralDecayRate ∧
      integralDecayRate < -(1174543941310025108442583192 : ℝ) / 10 ^ 27 := by
  have h0 := abs_lt.mp (saddleLog_enclosure 0)
  have h1 := abs_lt.mp (saddleLog_enclosure 1)
  have h2 := abs_lt.mp (saddleLog_enclosure 2)
  have h3 := abs_lt.mp (saddleLog_enclosure 3)
  have h4 := abs_lt.mp (saddleLog_enclosure 4)
  have h5 := abs_lt.mp (saddleLog_enclosure 5)
  norm_num [saddleLogInput, saddleLogRounded] at h0 h1 h2 h3 h4 h5
  obtain ⟨hy, hA, hJ⟩ := saddleModuli_paper_bounds
  have hyL := Real.log_le_log (by norm_num :
    (0 : ℝ) < 4710661776618520503155596 / 10 ^ 24) hy.1.le
  have hyU := Real.log_le_log saddleNormSq_pos hy.2.le
  have hAL := Real.log_le_log (by norm_num :
    (0 : ℝ) < 265339959117980760581398972 / 10 ^ 24) hA.1.le
  have hAU := Real.log_le_log (by linarith [hA.1] : 0 < saddleQuadraticNormSq) hA.2.le
  have hJL := Real.log_le_log (by norm_num :
    (0 : ℝ) < 725697065335997235474816912 / 10 ^ 24) hJ.1.le
  have hJU := Real.log_le_log (by linarith [hJ.1] : 0 < saddlePoleNormSq) hJ.2.le
  rw [integralDecayRate_eq_log_moduli]
  constructor <;> linarith [h0.1, h1.2, h2.1, h3.2, h4.1, h5.2]

theorem integralDecayRate_neg : integralDecayRate < 0 := by
  linarith [integralDecayRate_enclosure.2]

end PiIrrationality
