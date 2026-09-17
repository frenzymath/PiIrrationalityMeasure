import Formalization.OldPointFineLogCertificate
import Formalization.OldPointImprovement
import Formalization.PaperRateNumerics

/-! Strict rational enclosures for the old bound and the gain in (5.24). -/

namespace PiIrrationality

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem machin40_fine_rational_bounds :
    (31415926535897932384626433832795028841971 : ℚ) / 10 ^ 40 <
      16 * arctanPartialRat (1 / 5) 40 - 4 * arctanPartialRat (1 / 239) 40 -
        4 * (1 / 239) ^ 81 / 81 ∧
    16 * arctanPartialRat (1 / 5) 40 - 4 * arctanPartialRat (1 / 239) 40 +
      16 * (1 / 5) ^ 81 / 81 <
        (31415926535897932384626433832795028841972 : ℚ) / 10 ^ 40 := by
  decide +kernel

theorem machin40_pi_fine_bounds :
    (31415926535897932384626433832795028841971 : ℝ) / 10 ^ 40 < Real.pi ∧
      Real.pi < (31415926535897932384626433832795028841972 : ℝ) / 10 ^ 40 := by
  have h5 := arctanPartial_signed_remainder (x := 1 / 5) (by norm_num) (by norm_num) 40
  have h239 := arctanPartial_signed_remainder (x := 1 / 239) (by norm_num) (by norm_num) 40
  norm_num at h5 h239
  have hnum : (31415926535897932384626433832795028841971 : ℝ) / 10 ^ 40 <
      16 * arctanPartial (1 / 5) 40 - 4 * arctanPartial (1 / 239) 40 -
        4 * (1 / 239) ^ 81 / 81 ∧
      16 * arctanPartial (1 / 5) 40 - 4 * arctanPartial (1 / 239) 40 +
        16 * (1 / 5) ^ 81 / 81 <
          (31415926535897932384626433832795028841972 : ℝ) / 10 ^ 40 := by
    have h := machin40_fine_rational_bounds
    have h' := (Rat.cast_lt (K := ℝ)).mpr h.1
    have h'' := (Rat.cast_lt (K := ℝ)).mpr h.2
    push_cast at h' h''
    norm_num only [arctanPartialRat_cast, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h' h''
    constructor
    · convert! h' using 1 <;> norm_num
    · convert! h'' using 1 <;> norm_num
  rw [machin_identity]
  constructor <;> linarith [hnum.1, hnum.2]

theorem sqrt_three_fine_bounds :
    (17320508075688772935274463415058723669428 : ℝ) / 10 ^ 40 < Real.sqrt 3 ∧
      Real.sqrt 3 < (17320508075688772935274463415058723669429 : ℝ) / 10 ^ 40 := by
  constructor
  · apply (Real.lt_sqrt (by norm_num)).mpr
    norm_num
  · apply (Real.sqrt_lt' (by norm_num)).mpr
    norm_num

theorem oldCoefficientRate_fine_enclosure :
    (3330677868988582161957187372888812 : ℝ) / 10 ^ 33 < oldCoefficientRate ∧
      oldCoefficientRate < (3330677868988582161957187372888813 : ℝ) / 10 ^ 33 := by
  have h0 := abs_lt.mp (oldFineLog_enclosure 0)
  have h1 := abs_lt.mp (oldFineLog_enclosure 1)
  have h2 := abs_lt.mp (oldFineLog_enclosure 2)
  have h3 := abs_lt.mp (oldFineLog_enclosure 3)
  have h4 := abs_lt.mp (oldFineLog_enclosure 4)
  have h5 := abs_lt.mp (oldFineLog_enclosure 5)
  norm_num [oldFineLogInput, oldFineLogRounded, oldFineRootLower, oldFineRootUpper] at h0 h1 h2 h3 h4 h5
  have hrL := oldStationaryRoot_fine_isolation.1.le
  have hrU := oldStationaryRoot_fine_isolation.2.le
  have hAL : (oldFineRootLower : ℝ) ^ 2 + 6 * oldFineRootLower + 25 ≤
      oldStationaryRoot ^ 2 + 6 * oldStationaryRoot + 25 := by
    gcongr
    norm_num [oldFineRootLower]
  have hAU : oldStationaryRoot ^ 2 + 6 * oldStationaryRoot + 25 ≤
      (oldFineRootUpper : ℝ) ^ 2 + 6 * oldFineRootUpper + 25 := by
    gcongr
    exact oldStationaryRoot_spec.1.le
  have hrootL := Real.log_le_log (by norm_num [oldFineRootLower] :
    (0 : ℝ) < oldFineRootLower) hrL
  have hrootU := Real.log_le_log oldStationaryRoot_spec.1 hrU
  have hpolyL := Real.log_le_log (by norm_num [oldFineRootLower] :
    (0 : ℝ) < (oldFineRootLower : ℝ) ^ 2 + 6 * oldFineRootLower + 25) hAL
  have hpolyU := Real.log_le_log (by nlinarith [oldStationaryRoot_spec.1] :
    0 < oldStationaryRoot ^ 2 + 6 * oldStationaryRoot + 25) hAU
  have hpoleL := Real.log_le_log (by norm_num [oldFineRootLower] :
    (0 : ℝ) < (oldFineRootLower : ℝ) - 25) (sub_le_sub_right hrL 25)
  have hpoleU := Real.log_le_log (by linarith [oldStationaryRoot_coarse.1] :
    0 < oldStationaryRoot - 25) (sub_le_sub_right hrU 25)
  norm_num [oldFineRootLower, oldFineRootUpper] at hrootL hrootU hpolyL hpolyU hpoleL hpoleU
  rw [oldCoefficientRate_formula]
  constructor <;> linarith [h0.1, h1.2, h2.1, h3.2, h4.1, h5.2]

theorem oldIntegralRate_fine_enclosure :
    -(1174924307988427962550368122718405 : ℝ) / 10 ^ 33 < oldIntegralRate ∧
      oldIntegralRate < -(1174924307988427962550368122718404 : ℝ) / 10 ^ 33 := by
  have h6 := abs_lt.mp (oldLog_enclosure 6)
  have h7 := abs_lt.mp (oldLog_enclosure 7)
  norm_num [oldLogInput, oldLogRounded] at h6 h7
  rw [oldIntegralRate_from_real]
  obtain ⟨hrL, hrU⟩ := oldCoefficientRate_fine_enclosure
  constructor <;> linarith [h6.1, h6.2, h7.1, h7.2]

theorem oldPoint_pi_term_fine_bounds :
    (30229989403903630843234637627369262204 : ℝ) / 10 ^ 38 < Real.pi / (6 * Real.sqrt 3) ∧
      Real.pi / (6 * Real.sqrt 3) <
        (30229989403903630843234637627369262205 : ℝ) / 10 ^ 38 := by
  obtain ⟨hL, hU⟩ := machin40_pi_fine_bounds
  obtain ⟨hsL, hsU⟩ := sqrt_three_fine_bounds
  have hs : 0 < 6 * Real.sqrt 3 := by positivity
  constructor
  · apply (lt_div_iff₀ hs).mpr
    linarith
  · apply (div_lt_iff₀ hs).mpr
    linarith

theorem parameterCost_oldPoint_fine_enclosure :
    (540618812788433906472761393333638 : ℝ) / 10 ^ 33 < parameterCost oldPoint ∧
      parameterCost oldPoint < (540618812788433906472761393333639 : ℝ) / 10 ^ 33 := by
  have h6 := abs_lt.mp (oldLog_enclosure 6)
  have h7 := abs_lt.mp (oldLog_enclosure 7)
  norm_num [oldLogInput, oldLogRounded] at h6 h7
  obtain ⟨hpL, hpU⟩ := oldPoint_pi_term_fine_bounds
  rw [parameterCost_oldPoint_log_formula]
  constructor <;> linarith [h6.1, h6.2, h7.1, h7.2]

theorem oldParameterAuxiliaryBound_enclosure :
    (7103205334137001727505773422810 : ℝ) / 10 ^ 30 < oldParameterAuxiliaryBound oldPoint ∧
      oldParameterAuxiliaryBound oldPoint < (7103205334137001727505773422811 : ℝ) / 10 ^ 30 := by
  obtain ⟨hrL, hrU⟩ := oldCoefficientRate_fine_enclosure
  obtain ⟨hsL, hsU⟩ := oldIntegralRate_fine_enclosure
  obtain ⟨hcL, hcU⟩ := parameterCost_oldPoint_fine_enclosure
  have ht : 0 < -oldIntegralRate - parameterCost oldPoint := by linarith
  unfold oldParameterAuxiliaryBound AuxiliaryBound
  rw [oldParameterCoefficientRate_at, oldParameterIntegralRate_at]
  constructor
  · have h : ((7103205334137001727505773422810 : ℝ) / 10 ^ 30 - 1) *
        (-oldIntegralRate - parameterCost oldPoint) < oldCoefficientRate + parameterCost oldPoint := by
      linarith
    have hd := (lt_div_iff₀ ht).mpr h
    linarith
  · have h : oldCoefficientRate + parameterCost oldPoint <
        ((7103205334137001727505773422811 : ℝ) / 10 ^ 30 - 1) *
          (-oldIntegralRate - parameterCost oldPoint) := by linarith
    have hd := (div_lt_iff₀ ht).mpr h
    linarith

theorem oldPoint_comparison_gain :
    (1342501780650931772 : ℝ) / 10 ^ 21 <
      oldParameterAuxiliaryBound oldPoint - paperAuxiliaryValue ∧
    oldParameterAuxiliaryBound oldPoint - paperAuxiliaryValue <
      (1342501780650931773 : ℝ) / 10 ^ 21 := by
  obtain ⟨hoL, hoU⟩ := oldParameterAuxiliaryBound_enclosure
  obtain ⟨hnL, hnU⟩ := paperAuxiliaryValue_enclosure
  constructor <;> linarith

theorem oldPoint_comparison_rounding :
    |oldParameterAuxiliaryBound oldPoint - paperAuxiliaryValue -
      (13425017806509318 : ℝ) / 10 ^ 19| < 1 / (2 * 10 ^ 19) ∧
    (1342501780 : ℝ) / 10 ^ 12 < oldParameterAuxiliaryBound oldPoint - paperAuxiliaryValue ∧
    |100 * (oldParameterAuxiliaryBound oldPoint - paperAuxiliaryValue) /
      oldParameterAuxiliaryBound oldPoint - (1890 : ℝ) / 10 ^ 5| < 1 / (2 * 10 ^ 5) := by
  obtain ⟨hL, hU⟩ := oldPoint_comparison_gain
  obtain ⟨hoL, hoU⟩ := oldParameterAuxiliaryBound_enclosure
  have ho : 0 < oldParameterAuxiliaryBound oldPoint := by linarith
  refine ⟨abs_lt.mpr ⟨by linarith, by linarith⟩, by linarith, ?_⟩
  apply abs_lt.mpr
  constructor
  · have h : ((1890 : ℝ) / 10 ^ 5 - 1 / (2 * 10 ^ 5)) *
        oldParameterAuxiliaryBound oldPoint <
          100 * (oldParameterAuxiliaryBound oldPoint - paperAuxiliaryValue) := by linarith
    have hd := (lt_div_iff₀ ho).mpr h
    linarith
  · have h : 100 * (oldParameterAuxiliaryBound oldPoint - paperAuxiliaryValue) <
        ((1890 : ℝ) / 10 ^ 5 + 1 / (2 * 10 ^ 5)) * oldParameterAuxiliaryBound oldPoint := by
      linarith
    have hd := (div_lt_iff₀ ho).mpr h
    linarith

end PiIrrationality
