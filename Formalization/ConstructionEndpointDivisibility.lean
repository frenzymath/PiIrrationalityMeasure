import Formalization.ConstructionEndpointFormula
import Formalization.ConstructionPrincipalLaurent
import Formalization.GeneralEndpointArithmetic

/-! The general endpoint coefficient divisibility (2.24). -/

namespace PiIrrationality

def constructionEndpointTwoExponent (b c n k : ℕ) : ℤ :=
  -((constructionTwoSaving b c : ℤ) * n) + (((3 * k + 1) / 2 : ℕ) : ℤ) + 3

noncomputable def constructionNormalizedEndpointCoeff (a b c n k : ℕ) : ℂ :=
  (2 : ℂ) ^ constructionEndpointTwoExponent b c n k *
    (constructionEndpointCoeff a b c n k : ℂ)

theorem construction_endpoint_scaled_bracket {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n)
    (j : ℕ) (hj : j ≤ c * n) (k : ℕ) :
    ∃ z : GI, (5 : ℂ) ^ (k + 1) * 2 ^ constructionEndpointTwoExponent b c n k *
      (constructionLaurentCoeff a b c n (j : ℤ) : ℂ) *
        ((-1 : ℂ) ^ k / (4 - 2 * Complex.I) ^ (j + k + 1) +
          1 / (6 + 2 * Complex.I) ^ (j + k + 1)) = (z : ℂ) := by
  have hm := construction_admissible_inequalities hc hp
  obtain ⟨w, hw⟩ := construction_principal_laurent_integer_factors hm.2.1 hm.1.le he hn j hj
  have hH := Nat.mul_pos (constructionTwoSaving_bounds hc he hp).1 hn
  simpa only [constructionEndpointTwoExponent, Nat.cast_mul] using
    endpoint_bracket_integral_of_factor (constructionTwoSaving b c * n)
      (2 * (a + b - c) * n) j k hH _ w hw

theorem constructionNormalizedEndpointCoeff_five_power {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n)
    (k : ℕ) (hk : k < b * n) :
    ∃ z : GI, (5 : ℂ) ^ (k + 1) * constructionNormalizedEndpointCoeff a b c n k =
      (z : ℂ) := by
  choose z hz using fun j : Fin (c * n + 1) =>
    construction_endpoint_scaled_bracket hc he hp hn j.val (Nat.le_of_lt_succ j.isLt) k
  refine ⟨-∑ j : Fin (c * n + 1), ((j.val + k).choose k : GI) * z j, ?_⟩
  unfold constructionNormalizedEndpointCoeff
  rw [constructionEndpointCoeff_formula hc hp hn k hk]
  calc
    _ = -∑ j : Fin (c * n + 1), ((j.val + k).choose k : ℂ) *
        (5 ^ (k + 1) * 2 ^ constructionEndpointTwoExponent b c n k *
          (constructionLaurentCoeff a b c n (j.val : ℤ) : ℂ) *
            ((-1 : ℂ) ^ k / (4 - 2 * Complex.I) ^ (j.val + k + 1) +
              1 / (6 + 2 * Complex.I) ^ (j.val + k + 1))) := by
      rw [← mul_assoc, mul_neg, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp_rw [hz]
      simp only [map_neg, map_sum, map_mul, map_natCast]

theorem constructionNormalizedEndpointCoeff_two_power (a b c n k : ℕ) :
    ∃ z : GI, (2 : ℂ) ^ (constructionTwoSaving b c * n) *
      constructionNormalizedEndpointCoeff a b c n k = (z : ℂ) := by
  refine ⟨(2 : GI) ^ ((3 * k + 1) / 2 + 3) * constructionEndpointCoeff a b c n k, ?_⟩
  unfold constructionNormalizedEndpointCoeff
  rw [← mul_assoc, ← zpow_natCast (2 : ℂ) (constructionTwoSaving b c * n),
    ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0)]
  have he : ((constructionTwoSaving b c * n : ℕ) : ℤ) +
      constructionEndpointTwoExponent b c n k = ((((3 * k + 1) / 2 + 3 : ℕ)) : ℤ) := by
    unfold constructionEndpointTwoExponent
    omega
  rw [he, zpow_natCast]
  simp only [map_mul, map_pow, map_ofNat]

theorem constructionNormalizedEndpointCoeff_integral {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n) (k : ℕ) :
    ∃ z : GI, constructionNormalizedEndpointCoeff a b c n k = (z : ℂ) := by
  by_cases hk : k < b * n
  · apply gaussian_integer_of_coprime_multipliers (constructionNormalizedEndpointCoeff a b c n k)
      (2 ^ (constructionTwoSaving b c * n)) (5 ^ (k + 1))
      (((by norm_num : Nat.Coprime 2 5).pow_left _).pow_right _)
    · simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        constructionNormalizedEndpointCoeff_two_power a b c n k
    · simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        constructionNormalizedEndpointCoeff_five_power hc he hp hn k hk
  · have hH := (constructionTwoSaving_bounds hc he hp).2
    have hHn : 2 * (constructionTwoSaving b c * n) < 3 * (b * n) := by
      have := Nat.mul_lt_mul_of_pos_right hH hn
      simpa only [Nat.mul_assoc] using this
    have hexp : 0 ≤ constructionEndpointTwoExponent b c n k := by
      unfold constructionEndpointTwoExponent
      omega
    refine ⟨(2 : GI) ^ (constructionEndpointTwoExponent b c n k).toNat *
      constructionEndpointCoeff a b c n k, ?_⟩
    unfold constructionNormalizedEndpointCoeff
    rw [← Int.toNat_of_nonneg hexp, zpow_natCast]
    simp only [map_mul, map_pow, map_ofNat, Int.toNat_natCast]

end PiIrrationality
