import Formalization.SavingPhiDominance
import Formalization.ParameterCost

/-! Linear-error dominance of the actual arithmetic cost in Section 6.8. -/

namespace PiIrrationality

theorem parameterSmoothCost_add_sub (p h : ℝ × ℝ) :
    parameterSmoothCost (p + h) - parameterSmoothCost p =
      2 * h.1 + (4 - 5 * Real.log 2) * h.2 := by
  dsimp [parameterSmoothCost]
  ring

theorem parameterSmoothCost_abs_sub_le (p h : ℝ × ℝ) :
    |parameterSmoothCost (p + h) - parameterSmoothCost p| ≤
      (6 + 5 * |Real.log 2|) * parameterNormOne h := by
  rw [parameterSmoothCost_add_sub]
  have hc : |4 - 5 * Real.log 2| ≤ 4 + 5 * |Real.log 2| := by
    simpa [abs_mul] using abs_sub (4 : ℝ) (5 * Real.log 2)
  have ht := abs_add_le (2 * h.1) ((4 - 5 * Real.log 2) * h.2)
  rw [abs_mul, abs_mul] at ht
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at ht
  have hs := mul_le_mul_of_nonneg_right hc (abs_nonneg h.2)
  dsimp [parameterNormOne]
  nlinarith [abs_nonneg h.1, abs_nonneg h.2, abs_nonneg (Real.log 2),
    mul_nonneg (abs_nonneg (Real.log 2)) (abs_nonneg h.1)]

theorem parameterCost_candidate_increase_dominates {M : ℝ} (hM : 0 ≤ M) :
    ∃ r : ℝ, 0 < r ∧ ∀ h : ℝ × ℝ,
      0 < parameterNormOne h → parameterNormOne h < r →
      M * parameterNormOne h < parameterCost (candidate + h) - parameterCost candidate := by
  obtain ⟨r, hr, hdec⟩ := savingPhi_candidate_decrease_dominates
    (M := M + (6 + 5 * |Real.log 2|)) (by positivity)
  refine ⟨r, hr, ?_⟩
  intro h hd hdr
  have hs := (abs_le.mp (parameterSmoothCost_abs_sub_le candidate h)).1
  have hp := hdec h hd hdr
  dsimp [parameterCost]
  nlinarith only [hs, hp]

theorem parameterNormOne_le_two_norm (h : ℝ × ℝ) : parameterNormOne h ≤ 2 * ‖h‖ := by
  have hx : |h.1| ≤ ‖h‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le h
  have hy : |h.2| ≤ ‖h‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le h
  dsimp [parameterNormOne]
  linarith

theorem parameterCost_strictLocalMinimizer : StrictLocalMinimizer parameterCost Admissible candidate := by
  obtain ⟨r, hr, hinc⟩ := parameterCost_candidate_increase_dominates (M := 0) (by norm_num)
  refine ⟨r / 2, by positivity, ?_⟩
  intro p _ hp hdist
  have hd : 0 < parameterNormOne (p - candidate) :=
    (norm_pos_iff.mpr (sub_ne_zero.mpr hp)).trans_le (norm_le_parameterNormOne _)
  have hsmall : parameterNormOne (p - candidate) < r :=
    (parameterNormOne_le_two_norm _).trans_lt (by linarith)
  have hi := hinc (p - candidate) hd hsmall
  have he : candidate + (p - candidate) = p := by abel
  rw [he, zero_mul] at hi
  linarith

end PiIrrationality
