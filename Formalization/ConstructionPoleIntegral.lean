import Formalization.ConstructionNormalizedCoefficient
import Formalization.PoleArithmetic

/-! General nonlogarithmic pole clearing, including the actual rational integrals (2.33). -/

namespace PiIrrationality

theorem construction_principal_scaled_factors {a b c n : ℕ}
    (hbc : c < 2 * b) (habc : c ≤ a + b) (he : Even c) (hn : 0 < n)
    (j : ℕ) (hj : j ≤ c * n) :
    ∃ z : ℤ, (10 : ℚ) ^ (-(j : ℤ)) * constructionLaurentCoeff a b c n (j : ℤ) =
      (2 : ℚ) ^ (constructionTwoSaving b c * n - 1 + (j + 1) / 2) *
        5 ^ (2 * (a + b - c) * n) * (z : ℚ) := by
  obtain ⟨z, hz⟩ := construction_principal_laurent_integer_factors hbc habc he hn j hj
  refine ⟨z, ?_⟩
  rw [hz, zpow_neg, zpow_natCast]
  have hexp : constructionTwoSaving b c * n - 1 + (3 * j + 1) / 2 =
      (constructionTwoSaving b c * n - 1 + (j + 1) / 2) + j := by omega
  rw [hexp, pow_add, pow_add, show (10 : ℚ) = 2 * 5 by norm_num, mul_pow]
  field_simp
  rw [pow_add]
  ring

noncomputable def constructionPoleClearedCoeff (a b c n j : ℕ) : ℚ :=
  constructionReducedLcm a b c n *
    ((10 : ℚ) ^ (-(j : ℤ)) * constructionLaurentCoeff a b c n (j : ℤ)) / j

theorem constructionPoleClearedCoeff_two_factor {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n)
    (j : ℕ) (hj0 : 0 < j) (hj : j ≤ c * n) :
    ∃ z : ℤ, constructionPoleClearedCoeff a b c n j =
      (2 : ℚ) ^ (constructionTwoSaving b c * n - 1 + (j + 1) / 2) * (z : ℚ) := by
  have hm := construction_admissible_inequalities hc hp
  have hD := (construction_integer_margins hc hp).2.2.2.2.2.2
  have hjD : j ≤ constructionDegree a b c * n := hj.trans (Nat.mul_le_mul_right n hD.le)
  obtain ⟨q, hq⟩ := (construction_reduced_laurent_integrality hm.2.1 hm.1.le hn).2.1
    (j : ℤ) (by simpa using hjD) (by exact_mod_cast hj0.ne')
  change constructionPoleClearedCoeff a b c n j = (q : ℚ) at hq
  obtain ⟨w, hw⟩ := construction_principal_scaled_factors hm.2.1 hm.1.le he hn j hj
  obtain ⟨L, hL⟩ := dvd_lcmRange (constructionDegree a b c * n) j hj0 hjD
  have hLQ : (lcmRange (constructionDegree a b c * n) : ℚ) = (j : ℚ) * (L : ℚ) := by
    exact_mod_cast hL
  let k := constructionTwoSaving b c * n - 1 + (j + 1) / 2
  let x := constructionPoleClearedCoeff a b c n j / (2 : ℚ) ^ k
  have hPhi : (constructionPhi a b c n : ℚ) ≠ 0 := by
    exact_mod_cast (constructionPhi_pos a b c n).ne'
  have hjQ : (j : ℚ) ≠ 0 := by exact_mod_cast hj0.ne'
  have ht : (2 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  obtain ⟨z, hz⟩ := construction_integer_of_Phi_and_ten_power a b c n x
    (by
      refine ⟨(L : ℤ) * (5 : ℤ) ^ (2 * (a + b - c) * n) * w, ?_⟩
      dsimp [x, constructionPoleClearedCoeff, constructionReducedLcm]
      rw [hw, hLQ]
      change (constructionPhi a b c n : ℚ) *
        ((j * L / constructionPhi a b c n *
          (2 ^ k * 5 ^ (2 * (a + b - c) * n) * (w : ℚ)) / j) / 2 ^ k) = _
      push_cast
      field_simp)
    (by
      refine ⟨k, (5 : ℤ) ^ k * q, ?_⟩
      dsimp [x]
      rw [hq, show (10 : ℚ) = 2 * 5 by norm_num, mul_pow]
      push_cast
      field_simp)
  exact ⟨z, (div_eq_iff ht).mp hz |>.trans (mul_comm _ _)⟩

theorem construction_normalized_pole_factor {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n)
    (j : ℕ) (hj0 : 0 < j) (hj : j ≤ c * n) :
    ∃ z : ℤ, (2 : ℚ) ^ (1 - (constructionTwoSaving b c : ℤ) * n) *
      constructionPoleClearedCoeff a b c n j = (2 : ℚ) ^ ((j + 1) / 2) * (z : ℚ) := by
  obtain ⟨z, hz⟩ := constructionPoleClearedCoeff_two_factor hc he hp hn j hj0 hj
  have hH : 0 < constructionTwoSaving b c * n :=
    Nat.mul_pos (constructionTwoSaving_bounds hc he hp).1 hn
  refine ⟨z, ?_⟩
  rw [hz, ← mul_assoc, ← zpow_natCast (2 : ℚ),
    ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  rw [show 1 - (constructionTwoSaving b c : ℤ) * n +
      (constructionTwoSaving b c * n - 1 + (j + 1) / 2 : ℕ) =
      (((j + 1) / 2 : ℕ) : ℤ) by omega, zpow_natCast]

theorem construction_normalized_pole_integral {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n)
    (j : ℕ) (hj0 : 0 < j) (hj : j ≤ c * n) :
    ∃ z : ℤ, (2 : ℚ) ^ (1 - (constructionTwoSaving b c : ℤ) * n) *
      constructionReducedLcm a b c n * constructionLaurentCoeff a b c n (j : ℤ) *
        poleIntegralRat j = (z : ℚ) := by
  obtain ⟨q, hq⟩ := construction_normalized_pole_factor hc he hp hn j hj0 hj
  obtain ⟨w, hw⟩ := pole_endpoint_bracket_is_integer j
  refine ⟨q * w, ?_⟩
  apply Rat.cast_injective (α := ℂ)
  push_cast
  rw [← polePair_integral_rat j hj0, polePair_integral_scaled j hj0]
  have hqC := congrArg (fun x : ℚ => (x : ℂ)) hq
  unfold constructionPoleClearedCoeff at hqC
  push_cast at hqC
  calc
    _ = ((2 : ℂ) ^ (1 - (constructionTwoSaving b c : ℤ) * n) *
        ((constructionReducedLcm a b c n : ℂ) *
          (10 ^ (-(j : ℤ)) * (constructionLaurentCoeff a b c n (j : ℤ) : ℂ)) / j)) *
      Complex.I * ((2 + Complex.I) ^ j - (2 - Complex.I) ^ j -
        ((2 + Complex.I) / (1 + Complex.I)) ^ j +
        ((2 - Complex.I) / (1 - Complex.I)) ^ j) := by ring
    _ = _ := by
      rw [hqC]
      rw [show (2 : ℂ) ^ ((j + 1) / 2) * q * Complex.I =
        q * (Complex.I * 2 ^ ((j + 1) / 2)) by ring, mul_assoc, hw]

theorem construction_normalized_nonlog_integral {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n) :
    ∃ z : ℤ, (2 : ℚ) ^ (1 - (constructionTwoSaving b c : ℤ) * n) *
      constructionReducedLcm a b c n *
        (∑ j ∈ Finset.Icc 1 (c * n), constructionLaurentCoeff a b c n (j : ℤ) *
          poleIntegralRat j) = (z : ℚ) := by
  classical
  let z (j : ℕ) := if hj : j ∈ Finset.Icc 1 (c * n) then
    (construction_normalized_pole_integral hc he hp hn j
      (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2).choose else 0
  refine ⟨∑ j ∈ Finset.Icc 1 (c * n), z j, ?_⟩
  rw [Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only [z]
  rw [dif_pos hj]
  simpa only [mul_assoc] using (construction_normalized_pole_integral hc he hp hn j
    (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2).choose_spec

end PiIrrationality
