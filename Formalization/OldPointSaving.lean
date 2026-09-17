import Formalization.DigammaThirds
import Formalization.OldPointPartition
import Formalization.GeneralSavingIntegrability

/-! Exact evaluation of the actual old saving integral and normalization cost, (A.31)--(A.32). -/

namespace PiIrrationality

open MeasureTheory Set

theorem savingOmega_oldPoint_eq_digamma :
    savingOmega 1 2 3 = realDigamma (2 / 3) - realDigamma (1 / 2) := by
  have hchi : ∀ u ∈ Ico (0 : ℝ) 1, savingChi (1 * u) (2 * u) (3 * u) =
      (Ico (1 / 2 : ℝ) (2 / 3)).indicator (fun _ => (1 : ℝ)) u := by
    intro u hu
    have he := oldPoint_accepted_set (e := 0) (by norm_num) (by norm_num)
    norm_num only [zero_div, sub_zero, Ico_self, union_empty] at he
    have hi : translatedSavingChi 1 2 3 (0, 0) u = 1 ↔ u ∈ Ico (1 / 2 : ℝ) (2 / 3) := by
      have h := Set.ext_iff.mp he u
      simpa only [mem_ofPred_eq, hu, true_and] using h
    by_cases hm : u ∈ Ico (1 / 2 : ℝ) (2 / 3)
    · rw [indicator_of_mem hm]
      simpa [translatedSavingChi] using hi.mpr hm
    · rw [indicator_of_notMem hm]
      have hne := fun h => hm (hi.mp h)
      unfold translatedSavingChi at hne
      unfold savingChi at hne ⊢
      simp only [add_zero] at hne
      split_ifs at * <;> simp_all
  have hs : savingOmega 1 2 3 = ∑ j ∈ ({0} : Finset ℕ),
      ∑' k : ℕ, periodicSummandReal (1 / 2) (2 / 3) k := by
    apply periodic_saving_integral_eq_series
      (fun u => savingChi (1 * u) (2 * u) (3 * u)) {0}
      (fun _ => 1 / 2) (fun _ => 2 / 3)
    · intro k u
      simpa only [Int.cast_ofNat, Int.cast_one] using savingChi_integer_periodic 1 2 3 k u
    · exact savingDensity_integrableOn_nonneg (by norm_num) (by norm_num) (by norm_num)
    · intro j hj
      norm_num
    · simp
    · simpa only [Finset.mem_singleton, iUnion_iUnion_eq_left] using hchi
  simpa only [Finset.sum_singleton,
    periodicSummandReal_tsum_eq_digamma (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 2 / 3)] using hs

theorem savingOmega_oldPoint :
    savingOmega 1 2 3 = Real.pi / (2 * Real.sqrt 3) - Real.log (3 * Real.sqrt 3 / 4) := by
  rw [savingOmega_oldPoint_eq_digamma, realDigamma_two_thirds, realDigamma_half]
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  rw [Real.log_div (mul_ne_zero (by norm_num) hs) (by norm_num),
    Real.log_mul (by norm_num) hs, Real.log_sqrt (by norm_num)]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] at h
    exact h
  rw [h4]
  ring

theorem savingPhi_oldPoint :
    savingPhi oldPoint =
      (Real.pi / (2 * Real.sqrt 3) - Real.log (3 * Real.sqrt 3 / 4)) / 3 := by
  have h := savingOmega_eq_scaled_phi (1 / 3) (2 / 3) (by norm_num : (0 : ℝ) < 3)
  norm_num only at h
  rw [savingOmega_oldPoint] at h
  change _ = 3 * savingPhi oldPoint at h
  linarith

theorem parameterCost_oldPoint :
    parameterCost oldPoint = (4 - (5 / 2) * Real.log 2 -
      (Real.pi / (2 * Real.sqrt 3) - Real.log (3 * Real.sqrt 3 / 4))) / 3 := by
  rw [parameterCost, savingPhi_oldPoint]
  dsimp [parameterSmoothCost, oldPoint]
  ring

end PiIrrationality
