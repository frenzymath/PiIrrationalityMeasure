import Formalization.SavingPeriodDifference
import Formalization.SavingMeasureLocalFormula
import Formalization.SavingVariationBound
import Formalization.PeriodErrorSum

/-! The uniform truncated logarithmic main term in (6.26). -/

namespace PiIrrationality

theorem savingPeriodDifference_candidate_main_error :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ (h : ℝ × ℝ) (k : ℝ),
      0 < k → parameterNormOne h ≤ r → k * parameterNormOne h ≤ r →
      |savingPeriodDifference 1857 3714 5570 h k - candidateSectorVariation h / k| ≤
        3 * savingTranslationConstant 1857 3714 5570 * parameterNormOne h / k ^ 2 := by
  obtain ⟨rho, hrho, hmodel⟩ := translatedSavingMeasure_local_formula
  let r := min rho 1 / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrho' : r < rho := by
    have h := min_le_left rho 1
    dsimp [r]
    linarith
  have hr1 : r ≤ 1 := by
    have h := min_le_right rho 1
    dsimp [r]
    linarith
  refine ⟨r, hr, hr1, ?_⟩
  intro h k hk hh hkh
  have hn : parameterNormOne (k • h) = k * parameterNormOne h := by
    rw [parameterNormOne_smul, abs_of_pos hk]
  have he := savingPeriodDifference_error h (a := 1857) (b := 3714) (c := 5570)
    (by norm_num) (by norm_num) (by norm_num) hk (hh.trans hr1)
    (by rw [hn]; exact hkh.trans hr1)
  rw [hmodel (k • h) (by rw [hn]; exact hkh.trans_lt hrho'),
    add_sub_cancel_left, candidateSectorVariation_smul h hk.le] at he
  have hc : k * candidateSectorVariation h / k ^ 2 = candidateSectorVariation h / k := by
    field_simp
  simpa only [hc] using he

theorem savingPeriodDifference_truncated_log :
    ∃ r C : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 ≤ C ∧ ∀ h : ℝ × ℝ,
      0 < parameterNormOne h → parameterNormOne h ≤ r →
      |(∑ k ∈ Finset.Icc 1 ⌊r / parameterNormOne h⌋₊,
          savingPeriodDifference 1857 3714 5570 h k) -
        candidateSectorVariation h * Real.log (1 / parameterNormOne h)| ≤
          C * parameterNormOne h := by
  obtain ⟨r, hr, hr1, herr⟩ := savingPeriodDifference_candidate_main_error
  let L := savingTranslationConstant 1857 3714 5570
  have hL : 0 ≤ L := savingTranslationConstant_nonneg _ _ _
  refine ⟨r, 6 * L + 1 + |Real.log r|, hr, hr1, by positivity, ?_⟩
  intro h hd hdr
  let K := ⌊r / parameterNormOne h⌋₊
  have hsum : |(∑ k ∈ Finset.Icc 1 K, savingPeriodDifference 1857 3714 5570 h k) -
      candidateSectorVariation h * (harmonic K : ℝ)| ≤
        2 * (3 * L * parameterNormOne h) := by
    apply sum_Icc_inverse_square_error K (by positivity)
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkK : k ≤ K := (Finset.mem_Icc.mp hk).2
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    apply herr h k hk0 hdr
    have hk_le : (k : ℝ) ≤ r / parameterNormOne h :=
      (Nat.cast_le.mpr hkK).trans (Nat.floor_le (by positivity))
    exact (le_div_iff₀ hd).mp hk_le
  have hlog := harmonic_floor_weighted_log_scale hr hd hdr (candidateSectorVariation_abs_le h)
  have ht := (abs_sub_le
    (∑ k ∈ Finset.Icc 1 K, savingPeriodDifference 1857 3714 5570 h k)
    (candidateSectorVariation h * (harmonic K : ℝ))
    (candidateSectorVariation h * Real.log (1 / parameterNormOne h))).trans
      (add_le_add hsum hlog)
  dsimp only [K] at ht
  nlinarith only [ht]

end PiIrrationality
