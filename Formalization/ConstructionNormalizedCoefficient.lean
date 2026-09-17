import Formalization.ConstructionReducedLcm
import Formalization.ConstructionPrincipalLaurent
import Formalization.ConstructionRationalLinearForm

/-! The actual normalization multiplier (6.62) and its nonzero integer pi coefficient. -/

namespace PiIrrationality

noncomputable def constructionNormalizationMultiplier (a b c n : ℕ) : ℚ :=
  (2 : ℚ) ^ (4 - (constructionTwoSaving b c : ℤ) * n) * constructionReducedLcm a b c n

noncomputable def constructionNormalizedPiCoeff (a b c n : ℕ) : ℚ :=
  constructionNormalizationMultiplier a b c n * constructionRationalV a b c n

theorem construction_reduced_constantCoeff_two_factor {a b c n : ℕ}
    (hbc : c < 2 * b) (habc : c ≤ a + b) (he : Even c) (hn : 0 < n) :
    ∃ z : ℤ, constructionLaurentCoeff a b c n 0 / (constructionPhi a b c n : ℚ) =
      (2 : ℚ) ^ (constructionTwoSaving b c * n - 1) * (z : ℚ) := by
  obtain ⟨q, hq⟩ := (construction_reduced_laurent_integrality hbc habc hn).2.2
  obtain ⟨w, hw⟩ := construction_principal_laurent_integer_factors hbc habc he hn 0 (by omega)
  simp only [Nat.cast_zero, Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.reduceDiv] at hw
  let k := constructionTwoSaving b c * n - 1
  let x : ℚ := constructionLaurentCoeff a b c n 0 / (constructionPhi a b c n : ℚ) / 2 ^ k
  have hp : (constructionPhi a b c n : ℚ) ≠ 0 := by
    exact_mod_cast (constructionPhi_pos a b c n).ne'
  have ht : (2 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  obtain ⟨z, hz⟩ := construction_integer_of_Phi_and_ten_power a b c n x
    (by
      refine ⟨(5 : ℤ) ^ (2 * (a + b - c) * n) * w, ?_⟩
      dsimp [x]
      rw [hw]
      change (constructionPhi a b c n : ℚ) *
        (2 ^ k * 5 ^ (2 * (a + b - c) * n) * (w : ℚ) / constructionPhi a b c n / 2 ^ k) = _
      push_cast
      field_simp)
    (by
      refine ⟨k, (5 : ℤ) ^ k * q, ?_⟩
      dsimp [x]
      rw [hq, show (10 : ℚ) = 2 * 5 by norm_num, mul_pow]
      push_cast
      field_simp)
  refine ⟨z, ?_⟩
  change constructionLaurentCoeff a b c n 0 / (constructionPhi a b c n : ℚ) / 2 ^ k =
    (z : ℚ) at hz
  exact (div_eq_iff ht).mp hz |>.trans (mul_comm _ _)

theorem constructionNormalizedPiCoeff_formula (a b c n : ℕ) :
    constructionNormalizedPiCoeff a b c n =
      -(2 : ℚ) ^ (3 - (constructionTwoSaving b c : ℤ) * n) *
        constructionReducedLcm a b c n * constructionLaurentCoeff a b c n 0 := by
  unfold constructionNormalizedPiCoeff constructionNormalizationMultiplier constructionRationalV
  rw [show 4 - (constructionTwoSaving b c : ℤ) * n =
    (3 - (constructionTwoSaving b c : ℤ) * n) + 1 by omega,
    zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one]
  ring

theorem constructionNormalizedPiCoeff_integral {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n) :
    ∃ V : ℤ, constructionNormalizedPiCoeff a b c n = (V : ℚ) := by
  have hm := construction_admissible_inequalities hc hp
  obtain ⟨z, hz⟩ := construction_reduced_constantCoeff_two_factor hm.2.1 hm.1.le he hn
  have hH : 0 < constructionTwoSaving b c * n :=
    Nat.mul_pos (constructionTwoSaving_bounds hc he hp).1 hn
  refine ⟨-4 * (lcmRange (constructionDegree a b c * n) : ℤ) * z, ?_⟩
  rw [constructionNormalizedPiCoeff_formula, constructionReducedLcm]
  calc
    _ = -(2 : ℚ) ^ (3 - (constructionTwoSaving b c : ℤ) * n) *
        (lcmRange (constructionDegree a b c * n) : ℚ) *
        (constructionLaurentCoeff a b c n 0 / (constructionPhi a b c n : ℚ)) := by ring
    _ = -(2 : ℚ) ^ (3 - (constructionTwoSaving b c : ℤ) * n +
        (constructionTwoSaving b c * n - 1 : ℕ)) *
        (lcmRange (constructionDegree a b c * n) : ℚ) * (z : ℚ) := by
      rw [hz, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
      ring
    _ = _ := by
      have heq : 3 - (constructionTwoSaving b c : ℤ) * n +
          (constructionTwoSaving b c * n - 1 : ℕ) = 2 := by omega
      rw [heq]
      push_cast
      norm_num

theorem constructionNormalizationMultiplier_pos (a b c n : ℕ) :
    0 < constructionNormalizationMultiplier a b c n :=
  mul_pos (zpow_pos (by norm_num) _) (constructionReducedLcm_pos a b c n)

theorem constructionNormalizedPiCoeff_neg {a b c : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (n : ℕ) :
    constructionNormalizedPiCoeff a b c n < 0 :=
  mul_neg_of_pos_of_neg (constructionNormalizationMultiplier_pos a b c n)
    (constructionRationalV_neg hc he hp n)

theorem construction_normalized_pi_integer {a b c : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (n : ℕ) (hn : 0 < n) :
    ∃ V : ℤ, V < 0 ∧
      constructionNormalizationMultiplier a b c n * constructionRationalV a b c n = (V : ℚ) := by
  obtain ⟨V, hV⟩ := constructionNormalizedPiCoeff_integral hc he hp hn
  refine ⟨V, ?_, hV⟩
  have hneg := constructionNormalizedPiCoeff_neg hc he hp n
  rw [hV] at hneg
  exact_mod_cast hneg

end PiIrrationality
