import Formalization.ComplexLaurent

/-! The complete six-factor Laurent expansion (2.9)--(2.10). -/

namespace PiIrrationality.GaussianExpansion

open Complex

def NumeratorBounds (a b n : ℕ) (m : Fin 6 → ℕ) : Prop :=
  m 1 ≤ 2 * a * n ∧ m 2 ≤ b * n ∧ m 3 ≤ b * n ∧
    m 4 ≤ b * n ∧ m 5 ≤ b * n

instance (a b n : ℕ) (m : Fin 6 → ℕ) : Decidable (NumeratorBounds a b n m) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def indices (a b c n : ℕ) (j : ℤ) : Finset (Fin 6 → ℕ) :=
  (Finset.Nat.antidiagonalTuple 6 (c * (n : ℤ) - j).toNat).filter
    (NumeratorBounds a b n)

theorem indices_top (a b c n : ℕ) : indices a b c n (c * (n : ℤ)) = {0} := by
  simp [indices, Finset.Nat.antidiagonalTuple_zero_right, NumeratorBounds]

theorem mem_indices (a b c n : ℕ) (j : ℤ) (hj : j ≤ c * (n : ℤ))
    (m : Fin 6 → ℕ) :
    m ∈ indices a b c n j ↔
      (∑ i, (m i : ℤ)) = c * (n : ℤ) - j ∧ NumeratorBounds a b n m := by
  simp only [indices, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
  have hn : 0 ≤ c * (n : ℤ) - j := sub_nonneg.mpr hj
  constructor
  · rintro ⟨hs, hb⟩
    refine ⟨?_, hb⟩
    rw [← Nat.cast_sum, hs, Int.toNat_of_nonneg hn]
  · rintro ⟨hs, hb⟩
    refine ⟨?_, hb⟩
    exact_mod_cast hs.trans (Int.toNat_of_nonneg hn).symm

def weight (a b c n : ℕ) (m : Fin 6 → ℕ) : ℕ :=
  (c * n + m 0).choose (m 0) * (2 * a * n).choose (m 1) *
    (b * n).choose (m 2) * (b * n).choose (m 3) *
    (b * n).choose (m 4) * (b * n).choose (m 5)

noncomputable def rawSummand (a b c n : ℕ) (m : Fin 6 → ℕ) : ℂ :=
  5 * (weight a b c n m : ℂ) * 10 ^ (-(c * (n : ℤ)) - 1 - m 0) *
    (-5) ^ (2 * a * n - m 1) * (-4 + 2 * I) ^ (b * n - m 2) *
    (-4 - 2 * I) ^ (b * n - m 3) * (-6 + 2 * I) ^ (b * n - m 4) *
    (-6 - 2 * I) ^ (b * n - m 5)

noncomputable def factors (a b c n : ℕ) : Fin 6 → ℂ → ℂ :=
  ![fun t => 1 / (5 - t) ^ (c * n + 1),
    fun t => (t + 0) ^ (2 * a * n),
    fun t => (t + (1 + 2 * I)) ^ (b * n),
    fun t => (t + (1 - 2 * I)) ^ (b * n),
    fun t => (t + (-1 + 2 * I)) ^ (b * n),
    fun t => (t + (-1 - 2 * I)) ^ (b * n)]

theorem regularized_eq_factors (a b c n : ℕ) :
    EvenPole.complexRegularized (constructionNumeratorY a b n) (c * n + 1) =
      fun t => 5 * ∏ i, factors a b c n i t := by
  funext t
  rw [EvenPole.complexRegularized, EvenPole.numerator_aeval,
    constructionNumeratorY_aeval]
  have hq : t ^ 4 + 6 * t ^ 2 + 25 =
      (t + (1 + 2 * I)) * (t + (1 - 2 * I)) *
        (t + (-1 + 2 * I)) * (t + (-1 - 2 * I)) := by
    ring_nf
    norm_num
    ring
  rw [hq]
  simp only [factors, Fin.prod_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one, mul_pow, add_zero]
  ring

theorem factors_contDiffAt (a b c n k : ℕ) (i : Fin 6) :
    ContDiffAt ℂ k (factors a b c n i) (-5) := by
  fin_cases i <;> dsimp [factors]
  all_goals fun_prop (disch := norm_num)

theorem factors_derivative (a b c n : ℕ) (m : Fin 6 → ℕ) :
    5 * (∏ i, normalizedComplexDeriv (m i) (factors a b c n i) (-5)) =
      rawSummand a b c n m := by
  simp only [factors, Fin.prod_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one,
    normalizedComplexDeriv_add_power, normalizedComplexDeriv_inv_sub]
  have he : -(c * (n : ℤ)) - 1 - m 0 = -((c * n + m 0 + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  simp only [rawSummand, weight, he, zpow_neg, zpow_natCast, Nat.cast_mul]
  norm_num only [neg_add_cancel, add_zero, sub_neg_eq_add]
  have h2 : (-5 : ℂ) + (1 + 2 * I) = -4 + 2 * I := by ring
  have h3 : (-5 : ℂ) + (1 - 2 * I) = -4 - 2 * I := by ring
  have h4 : (-5 : ℂ) + (-1 + 2 * I) = -6 + 2 * I := by ring
  have h5 : (-5 : ℂ) + (-1 - 2 * I) = -6 - 2 * I := by ring
  rw [h2, h3, h4, h5]
  norm_num only [Fin.succ, Fin.reduceFinMk]
  ring_nf
  rfl

theorem weight_zero_of_unbounded (a b c n : ℕ) (m : Fin 6 → ℕ)
    (hm : ¬ NumeratorBounds a b n m) : weight a b c n m = 0 := by
  simp only [NumeratorBounds, not_and_or, not_le] at hm
  rcases hm with h | h | h | h | h <;>
    simp [weight, Nat.choose_eq_zero_of_lt h]

theorem raw_expansion (a b c n : ℕ) (j : ℤ) (hj : j ≤ c * (n : ℤ)) :
    (constructionLaurentCoeff a b c n j : ℂ) =
      ∑ m ∈ indices a b c n j, rawSummand a b c n m := by
  rw [constructionLaurentCoeff_complex a b c n j hj, regularized_eq_factors,
    normalizedComplexDeriv_const_mul, normalizedComplexDeriv_fin_prod _ _ _ _
      (factors_contDiffAt a b c n _), Finset.mul_sum]
  simp_rw [factors_derivative]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro m hm hnot
  have hb : ¬ NumeratorBounds a b n m := by
    simpa only [indices, Finset.mem_filter, hm, true_and] using hnot
  simp [rawSummand, weight_zero_of_unbounded a b c n m hb]

end PiIrrationality.GaussianExpansion
