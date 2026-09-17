import Formalization.OldPointRateFormulas
import Formalization.OldPointLogCertificate
import Formalization.ArctanFinite

/-! The strict old-point rate enclosures and sign certificate (A.33), (6.31). -/

namespace PiIrrationality

theorem oldCoefficientRate_enclosure :
    (33306 : ℝ) / 10 ^ 4 < oldCoefficientRate ∧ oldCoefficientRate < (33308 : ℝ) / 10 ^ 4 := by
  have h0 := abs_lt.mp (oldLog_enclosure 0)
  have h1 := abs_lt.mp (oldLog_enclosure 1)
  have h2 := abs_lt.mp (oldLog_enclosure 2)
  have h3 := abs_lt.mp (oldLog_enclosure 3)
  have h4 := abs_lt.mp (oldLog_enclosure 4)
  have h5 := abs_lt.mp (oldLog_enclosure 5)
  norm_num [oldLogInput, oldLogRounded] at h0 h1 h2 h3 h4 h5
  have hrL : (66339501 : ℝ) / 10 ^ 6 ≤ oldStationaryRoot := by
    have h := oldStationaryRoot_isolation.1
    norm_num [oldRootLower] at h
    linarith
  have hrU : oldStationaryRoot ≤ (66339502 : ℝ) / 10 ^ 6 := by
    have h := oldStationaryRoot_isolation.2
    norm_num [oldRootUpper] at h
    linarith
  have hAL : ((66339501 : ℝ) / 10 ^ 6) ^ 2 + 6 * ((66339501 : ℝ) / 10 ^ 6) + 25 ≤
      oldStationaryRoot ^ 2 + 6 * oldStationaryRoot + 25 := by gcongr
  have hAU : oldStationaryRoot ^ 2 + 6 * oldStationaryRoot + 25 ≤
      ((66339502 : ℝ) / 10 ^ 6) ^ 2 + 6 * ((66339502 : ℝ) / 10 ^ 6) + 25 := by gcongr
  have hrootL := Real.log_le_log (by norm_num : (0 : ℝ) < 66339501 / 10 ^ 6) hrL
  have hrootU := Real.log_le_log oldStationaryRoot_spec.1 hrU
  have hpolyL := Real.log_le_log (by norm_num :
    (0 : ℝ) < (66339501 / 10 ^ 6) ^ 2 + 6 * (66339501 / 10 ^ 6) + 25) hAL
  have hpolyU := Real.log_le_log (by nlinarith [oldStationaryRoot_spec.1] :
    0 < oldStationaryRoot ^ 2 + 6 * oldStationaryRoot + 25) hAU
  have hpoleL := Real.log_le_log (by norm_num : (0 : ℝ) < 66339501 / 10 ^ 6 - 25)
    (sub_le_sub_right hrL 25)
  have hpoleU := Real.log_le_log (by linarith [oldStationaryRoot_coarse.1] :
    0 < oldStationaryRoot - 25) (sub_le_sub_right hrU 25)
  norm_num at hrootL hrootU hpolyL hpolyU hpoleL hpoleU
  rw [oldCoefficientRate_formula]
  constructor <;> linarith [h0.1, h1.2, h2.1, h3.2, h4.1, h5.2]

theorem oldIntegralRate_enclosure :
    -(11750 : ℝ) / 10 ^ 4 < oldIntegralRate ∧ oldIntegralRate < -(11748 : ℝ) / 10 ^ 4 := by
  have h6 := abs_lt.mp (oldLog_enclosure 6)
  have h7 := abs_lt.mp (oldLog_enclosure 7)
  norm_num [oldLogInput, oldLogRounded] at h6 h7
  rw [oldIntegralRate_from_real]
  obtain ⟨hrL, hrU⟩ := oldCoefficientRate_enclosure
  constructor <;> linarith [h6.1, h6.2, h7.1, h7.2]

theorem oldPoint_pi_term_bounds :
    (3022998 : ℝ) / 10 ^ 7 < Real.pi / (6 * Real.sqrt 3) ∧
      Real.pi / (6 * Real.sqrt 3) < (3023000 : ℝ) / 10 ^ 7 := by
  obtain ⟨hL, hU⟩ := machin40_pi_bounds
  obtain ⟨hsL, hsU⟩ := sqrt_three_paper_bounds
  have hs : 0 < 6 * Real.sqrt 3 := by positivity
  constructor
  · apply (lt_div_iff₀ hs).mpr
    linarith
  · apply (div_lt_iff₀ hs).mpr
    linarith

theorem parameterCost_oldPoint_enclosure :
    (5405 : ℝ) / 10 ^ 4 < parameterCost oldPoint ∧
      parameterCost oldPoint < (5407 : ℝ) / 10 ^ 4 := by
  have h6 := abs_lt.mp (oldLog_enclosure 6)
  have h7 := abs_lt.mp (oldLog_enclosure 7)
  norm_num [oldLogInput, oldLogRounded] at h6 h7
  obtain ⟨hpL, hpU⟩ := oldPoint_pi_term_bounds
  rw [parameterCost_oldPoint_log_formula]
  constructor <;> linarith [h6.1, h6.2, h7.1, h7.2]

noncomputable def oldTau : ℝ := -oldIntegralRate - parameterCost oldPoint
noncomputable def oldK : ℝ := (oldCoefficientRate - oldIntegralRate) / oldTau ^ 2

theorem oldTau_enclosure : (6341 : ℝ) / 10 ^ 4 < oldTau ∧ oldTau < (6345 : ℝ) / 10 ^ 4 := by
  unfold oldTau
  obtain ⟨hsL, hsU⟩ := oldIntegralRate_enclosure
  obtain ⟨hcL, hcU⟩ := parameterCost_oldPoint_enclosure
  constructor <;> linarith

theorem oldRateGap_enclosure :
    (45054 : ℝ) / 10 ^ 4 < oldCoefficientRate - oldIntegralRate ∧
      oldCoefficientRate - oldIntegralRate < (45058 : ℝ) / 10 ^ 4 := by
  obtain ⟨hrL, hrU⟩ := oldCoefficientRate_enclosure
  obtain ⟨hsL, hsU⟩ := oldIntegralRate_enclosure
  constructor <;> linarith

theorem oldK_enclosure : 11 < oldK ∧ oldK < 12 := by
  obtain ⟨htL, htU⟩ := oldTau_enclosure
  obtain ⟨hL, hU⟩ := oldRateGap_enclosure
  have ht : 0 < oldTau ^ 2 := sq_pos_of_pos (by linarith)
  unfold oldK
  constructor
  · apply (lt_div_iff₀ ht).mpr
    nlinarith [sq_nonneg (oldTau - 6345 / 10 ^ 4)]
  · apply (div_lt_iff₀ ht).mpr
    nlinarith [sq_nonneg (oldTau - 6341 / 10 ^ 4)]

theorem oldK_decimal_identities :
    (45054 : ℚ) / 10 ^ 4 - 11 * (6345 / 10 ^ 4) ^ 2 = 7690725 / 10 ^ 8 ∧
    12 * ((6341 : ℚ) / 10 ^ 4) ^ 2 - 45058 / 10 ^ 4 = 31919372 / 10 ^ 8 := by
  norm_num

end PiIrrationality
