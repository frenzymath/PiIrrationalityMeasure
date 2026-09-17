import Formalization.ConstructionPolynomialLaurent
import Formalization.ConstructionReducedLcm
import Formalization.PolynomialReducedCoefficients

/-! Reduced denominator clearing for the actual negative-Laurent polynomial representation. -/

namespace PiIrrationality

theorem construction_polynomial_negative_laurent_integral {a b c n : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) (hn : 0 < n)
    (q : ℕ) (hq : q < constructionDegree a b c * n - 1) :
    ∃ z : ℤ, (10 : ℚ) ^ (q + 1) * constructionReducedLcm a b c n *
      constructionLaurentCoeff a b c n (-((q + 1 : ℕ) : ℤ)) / (q + 1) = (z : ℚ) := by
  have hm := construction_admissible_inequalities hc hp
  obtain ⟨z, hz⟩ := (construction_reduced_laurent_integrality hm.2.1 hm.1.le hn).2.1
    (-((q + 1 : ℕ) : ℤ)) (by rw [Int.natAbs_neg, Int.natAbs_natCast]; omega)
    (by omega)
  simp only [neg_neg, zpow_natCast, Int.cast_neg, Int.cast_natCast] at hz
  refine ⟨-z, ?_⟩
  rw [Int.cast_neg, ← hz]
  simp only [div_neg, neg_neg]
  push_cast
  ring

theorem construction_polynomial_zero_laurent_integral {a b c n : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) (hn : 0 < n)
    (q : ℕ) (hq : q < constructionDegree a b c * n - 1) :
    ∃ z : ℤ, constructionReducedLcm a b c n *
      constructionLaurentCoeff a b c n 0 / (q + 1) = (z : ℚ) := by
  have hm := construction_admissible_inequalities hc hp
  obtain ⟨z, hz⟩ := (construction_reduced_laurent_integrality hm.2.1 hm.1.le hn).2.2
  obtain ⟨l, hl⟩ := dvd_lcmRange (constructionDegree a b c * n) (q + 1) (by omega) (by omega)
  have hlQ : (lcmRange (constructionDegree a b c * n) : ℚ) = (q + 1 : ℚ) * (l : ℚ) := by
    exact_mod_cast hl
  have hqQ : (q + 1 : ℚ) ≠ 0 := by positivity
  refine ⟨(l : ℤ) * z, ?_⟩
  unfold constructionReducedLcm
  rw [hlQ]
  calc
    _ = (l : ℚ) * (constructionLaurentCoeff a b c n 0 / (constructionPhi a b c n : ℚ)) := by
      field_simp
    _ = _ := by rw [hz]; push_cast; rfl

theorem construction_polynomial_correction_integral {a b c n : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) (hn : 0 < n)
    (q : ℕ) (hq : q < constructionDegree a b c * n - 1) (j : ℕ) (hj : j ≤ c * n) :
    ∃ z : ℤ, (10 : ℚ) ^ (q + 1) * constructionReducedLcm a b c n *
      (((j + q).choose q : ℚ) * constructionLaurentCoeff a b c n (j : ℤ) /
        10 ^ (j + q + 1)) / (q + 1) = (z : ℚ) := by
  by_cases hj0 : j = 0
  · subst j
    obtain ⟨z, hz⟩ := construction_polynomial_zero_laurent_integral hc hp hn q hq
    refine ⟨z, ?_⟩
    rw [← hz]
    norm_num only [zero_add, Nat.choose_self, Nat.cast_one, Nat.cast_zero, one_mul]
    field_simp
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hm := construction_admissible_inequalities hc hp
    have hD := (construction_integer_margins hc hp).2.2.2.2.2.2
    have hjD : j ≤ constructionDegree a b c * n := hj.trans (Nat.mul_le_mul_right n hD.le)
    obtain ⟨z, hz⟩ := (construction_reduced_laurent_integrality hm.2.1 hm.1.le hn).2.1
      (j : ℤ) (by simpa using hjD) (by exact_mod_cast hj0)
    refine ⟨((j + q).choose (q + 1) : ℤ) * z, ?_⟩
    have hqQ : (q + 1 : ℚ) ≠ 0 := by positivity
    have hjQ : (j : ℚ) ≠ 0 := by exact_mod_cast hj0
    calc
      _ = (((j + q).choose q : ℚ) / (q + 1)) *
          (constructionReducedLcm a b c n *
            ((10 : ℚ) ^ (-(j : ℤ)) * constructionLaurentCoeff a b c n (j : ℤ))) := by
        rw [show j + q + 1 = j + (q + 1) by omega, pow_add, zpow_neg, zpow_natCast]
        field_simp
        ring
      _ = ((j + q).choose (q + 1) : ℚ) *
          (constructionReducedLcm a b c n *
            ((10 : ℚ) ^ (-(j : ℤ)) * constructionLaurentCoeff a b c n (j : ℤ)) / j) := by
        rw [choose_div_succ_eq_choose_div j q hjpos]
        ring
      _ = _ := by
        rw [show ((j : ℤ) : ℚ) = (j : ℚ) by simp] at hz
        rw [hz]
        push_cast
        rfl

noncomputable def constructionPoleAntiderivativeCoeff (a b c n q : ℕ) : ℚ :=
  (10 : ℚ) ^ (q + 1) * constructionReducedLcm a b c n *
    (constructionPoleShiftCoeff a b c n q : ℚ) / (q + 1)

theorem constructionPoleAntiderivativeCoeff_integral {a b c n : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) (hn : 0 < n)
    (q : ℕ) (hq : q < constructionDegree a b c * n - 1) :
    ∃ z : ℤ, constructionPoleAntiderivativeCoeff a b c n q = (z : ℚ) := by
  obtain ⟨z0, hz0⟩ := construction_polynomial_negative_laurent_integral hc hp hn q hq
  choose z hz using fun j : Fin (c * n + 1) =>
    construction_polynomial_correction_integral hc hp hn q hq j.val
      (Nat.le_of_lt_succ j.isLt)
  refine ⟨z0 - ∑ j : Fin (c * n + 1), z j, ?_⟩
  unfold constructionPoleAntiderivativeCoeff
  rw [constructionPoleShiftCoeff_laurent_formula, mul_sub, sub_div,
    Finset.mul_sum, Finset.sum_div, hz0]
  simp_rw [hz]
  push_cast
  rfl

end PiIrrationality
