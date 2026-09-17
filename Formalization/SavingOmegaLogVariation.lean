import Formalization.SavingPeriodMainTerm
import Formalization.SavingPeriodTail

/-! Uniform logarithmic variation of the actual Omega integral. -/

namespace PiIrrationality

theorem savingOmega_candidate_log_variation :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ h : ℝ × ℝ,
      0 < parameterNormOne h → parameterNormOne h ≤ r →
      |savingOmega (1857 + h.1) (3714 + h.2) 5570 - savingOmega 1857 3714 5570 -
        candidateSectorVariation h * Real.log (1 / parameterNormOne h)| ≤
          C * parameterNormOne h := by
  obtain ⟨r, C, hr, hr1, hC, hmain⟩ := savingPeriodDifference_truncated_log
  let B := (22288 : ℝ) ^ 2 * savingTranslationConstant 1857 3714 5570
  have hB : 0 ≤ B := mul_nonneg (sq_nonneg _) (savingTranslationConstant_nonneg _ _ _)
  refine ⟨r, C + B + 2 / r, hr, by positivity, ?_⟩
  intro h hd hdr
  let K := ⌊r / parameterNormOne h⌋₊
  have hsum := hmain h hd hdr
  have hfirst := savingPeriodDifference_zero_bound (hdr.trans hr1)
  have htail := savingOmega_candidate_period_remainder (hdr.trans hr1) K
  have htailBound : 2 / ((K : ℝ) + 1) ≤ (2 / r) * parameterNormOne h := by
    calc
      _ ≤ 2 / (r / parameterNormOne h) :=
        div_le_div_of_nonneg_left (by norm_num) (div_pos hr hd)
          (Nat.lt_floor_add_one (r / parameterNormOne h)).le
      _ = _ := by field_simp
  have htail' := htail.trans htailBound
  have he : savingOmega (1857 + h.1) (3714 + h.2) 5570 - savingOmega 1857 3714 5570 -
      candidateSectorVariation h * Real.log (1 / parameterNormOne h) =
      (savingOmega (1857 + h.1) (3714 + h.2) 5570 - savingOmega 1857 3714 5570 -
        savingPeriodDifference 1857 3714 5570 h 0 -
        ∑ k ∈ Finset.Icc 1 K, savingPeriodDifference 1857 3714 5570 h k) +
      savingPeriodDifference 1857 3714 5570 h 0 +
      ((∑ k ∈ Finset.Icc 1 K, savingPeriodDifference 1857 3714 5570 h k) -
        candidateSectorVariation h * Real.log (1 / parameterNormOne h)) := by ring
  rw [he]
  calc
    _ ≤ (|savingOmega (1857 + h.1) (3714 + h.2) 5570 - savingOmega 1857 3714 5570 -
        savingPeriodDifference 1857 3714 5570 h 0 -
        ∑ k ∈ Finset.Icc 1 K, savingPeriodDifference 1857 3714 5570 h k| +
      |savingPeriodDifference 1857 3714 5570 h 0|) +
      |(∑ k ∈ Finset.Icc 1 K, savingPeriodDifference 1857 3714 5570 h k) -
        candidateSectorVariation h * Real.log (1 / parameterNormOne h)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ((2 / r) * parameterNormOne h + B * parameterNormOne h) + C * parameterNormOne h :=
      add_le_add (add_le_add htail' hfirst) hsum
    _ = _ := by ring

end PiIrrationality
