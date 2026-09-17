import Formalization.SavingMeasureLocalFormula
import Formalization.SavingTranslationBounds
import Formalization.SavingPhiLogVariation

/-! The paper-facing interfaces for Lemmas 6.1 and 6.2. -/

namespace PiIrrationality

open MeasureTheory Set

/-! The one-period measure in (6.13) has the uniform radial affine formula (6.14). -/
theorem lemma_6_1_radial_polyhedral :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : ℝ × ℝ, parameterNormOne v = 1 →
      ∀ s : ℝ, 0 ≤ s → s ≤ ρ →
        translatedSavingMeasure 1857 3714 5570 (s • v) -
          translatedSavingMeasure 1857 3714 5570 0 = s * candidateSectorVariation v :=
  translatedSavingMeasure_directional_formula

/-! The constant-translation estimate (6.15), with an explicit admissible radius. -/
theorem lemma_6_1_constant_translation :
    ∀ z z' : ℝ × ℝ, parameterNormOne z ≤ 1 → parameterNormOne z' ≤ 1 →
      |translatedSavingMeasure 1857 3714 5570 z' -
        translatedSavingMeasure 1857 3714 5570 z| ≤
        savingTranslationConstant 1857 3714 5570 * parameterNormOne (z' - z) := by
  intro z z' hz hz'
  exact translatedSavingMeasure_abs_sub_le (a := 1857) (b := 3714) (c := 5570)
    z z' (by norm_num) (by norm_num) (by norm_num) hz hz'

/-! The affine-translation estimate (6.16), uniformly on the same radius. -/
theorem lemma_6_1_affine_translation :
    ∀ z w : ℝ × ℝ, parameterNormOne z ≤ 1 → parameterNormOne w ≤ 1 →
      (∫ u in (0 : ℝ)..1,
        |translatedSavingChi 1857 3714 5570 (z + u • w) u -
          translatedSavingChi 1857 3714 5570 z u|) ≤
        savingTranslationConstant 1857 3714 5570 * parameterNormOne w := by
  intro z w hz hw
  exact translatedSavingChi_integral_affine_translation (a := 1857) (b := 3714) (c := 5570) z w
    (by norm_num) (by norm_num) (by norm_num) hz hw

/-! The uniform directional logarithmic expansion (6.20). -/
theorem lemma_6_2_directional_log_variation :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ v : ℝ × ℝ,
      parameterNormOne v = 1 → ∀ ε : ℝ, 0 < ε → ε ≤ r →
      |savingPhi (candidate + ε • v) - savingPhi candidate -
        ε * candidateSectorVariation v * Real.log (1 / ε)| ≤ C * ε :=
  savingPhi_candidate_directional_log_variation

/-! The equivalent norm form (6.21). -/
theorem lemma_6_2_norm_log_variation :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ h : ℝ × ℝ,
      0 < parameterNormOne h → parameterNormOne h ≤ r →
      |savingPhi (candidate + h) - savingPhi candidate -
        candidateSectorVariation h * Real.log (1 / parameterNormOne h)| ≤
          C * parameterNormOne h :=
  savingPhi_candidate_log_variation

end PiIrrationality
