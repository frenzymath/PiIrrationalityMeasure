import Formalization.ConstructionScaledLaurent
import Formalization.PrincipalLaurent

/-! The principal Laurent estimates (2.5) for arbitrary admissible even-denominator triples. -/

namespace PiIrrationality

theorem constructionScaledNumerator_hasTwoWeight (a b n : ℕ) :
    HasTwoWeight (b * n) (constructionScaledNumerator a b n) := by
  have h := (hasTwoWeight_zero
    ((2 * Polynomial.X - 1) ^ (2 * a * n) *
      (5 * Polynomial.X ^ 2 - 4 * Polynomial.X + 1) ^ (b * n))).mul
      (lastQuadratic_hasTwoWeight.pow (b * n))
  simpa only [Nat.mul_one, zero_add, constructionScaledNumerator] using h

theorem constructionScaledCoreInt_two_dvd (a b c n k : ℕ) :
    (2 : ℤ) ^ (b * n - k / 2) ∣ constructionScaledCoreInt a b c n k := by
  unfold constructionScaledCoreInt
  apply Finset.dvd_sum
  intro i hi
  have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have he : b * n - k / 2 ≤ b * n - i / 2 := by omega
  have hd := (pow_dvd_pow (2 : ℤ) he).trans
    (constructionScaledNumerator_hasTwoWeight a b n i)
  have hcoeff : (Polynomial.hasseDeriv i (constructionScaledNumerator a b n)).eval 0 =
      (constructionScaledNumerator a b n).coeff i := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    simp [Polynomial.hasseDeriv_coeff]
  rw [hcoeff]
  exact dvd_mul_of_dvd_left hd _

theorem construction_principal_exponent {b c n j : ℕ}
    (hbc : c < 2 * b) (he : Even c) (hn : 0 < n) (hj : j ≤ c * n) :
    j + ((4 * b - 2 * c) * n - 1) + (b * n - (c * n - j) / 2) =
      constructionTwoSaving b c * n - 1 + (3 * j + 1) / 2 := by
  have hdiv : c / 2 * 2 = c := Nat.div_mul_cancel he.two_dvd
  have hdivn : c * n = 2 * ((c / 2) * n) := by
    calc
      c * n = (c / 2 * 2) * n := by rw [hdiv]
      _ = _ := by ring
  have hbn : (c / 2) * n < b * n :=
    Nat.mul_lt_mul_of_pos_right (by omega) hn
  have hA : (4 * b - 2 * c) * n = 4 * (b * n) - 2 * (c * n) := by
    simp only [Nat.sub_mul, Nat.mul_assoc]
  have hH : constructionTwoSaving b c * n = 5 * (b * n) - 5 * ((c / 2) * n) := by
    simp only [constructionTwoSaving, Nat.sub_mul, Nat.mul_assoc]
  omega

theorem construction_principal_laurent_integer_factors {a b c n : ℕ}
    (hbc : c < 2 * b) (habc : c ≤ a + b) (he : Even c) (hn : 0 < n)
    (j : ℕ) (hj : j ≤ c * n) :
    ∃ z : ℤ, constructionLaurentCoeff a b c n (j : ℤ) =
      (2 : ℚ) ^ (constructionTwoSaving b c * n - 1 + (3 * j + 1) / 2) *
        5 ^ (2 * (a + b - c) * n + j) * (z : ℚ) := by
  let k := c * n - j
  have hkorder : (c * (n : ℤ) - (j : ℤ)).toNat = k := by
    dsimp [k]
    omega
  have hj' : (j : ℤ) ≤ c * (n : ℤ) := by exact_mod_cast hj
  obtain ⟨z, hz⟩ := constructionScaledCoreInt_two_dvd a b c n k
  refine ⟨z, ?_⟩
  have hscaled := constructionScaledCoeffInt_eq_actual hbc habc hn (j : ℤ) hj'
  rw [hkorder] at hscaled
  have hcoef : constructionLaurentCoeff a b c n (j : ℤ) =
      (10 : ℚ) ^ j * (constructionScaledCoeffInt a b c n k : ℚ) := by
    rw [hscaled, zpow_neg, zpow_natCast]
    field_simp
  rw [hcoef]
  unfold constructionScaledCoeffInt
  rw [hz]
  push_cast
  rw [show (10 : ℚ) = 2 * 5 by norm_num, mul_pow]
  calc
    _ = (2 : ℚ) ^ (j + ((4 * b - 2 * c) * n - 1) + (b * n - k / 2)) *
        5 ^ (2 * (a + b - c) * n + j) * (z : ℚ) := by
      simp only [pow_add]
      ring
    _ = _ := by rw [construction_principal_exponent hbc he hn hj]

theorem construction_principal_laurent_valuations {a b c n : ℕ}
    (hbc : c < 2 * b) (habc : c ≤ a + b) (he : Even c) (hn : 0 < n)
    (j : ℕ) (hj : j ≤ c * n) :
    ((((constructionTwoSaving b c * n : ℕ) : ℤ) + 3 * (j : ℤ) / 2 - 1 : ℤ) :
        WithTop ℤ) ≤ padicValRatTop 2 (constructionLaurentCoeff a b c n (j : ℤ)) ∧
      (((2 * (a + b - c) * n + j : ℕ) : ℤ) : WithTop ℤ) ≤
        padicValRatTop 5 (constructionLaurentCoeff a b c n (j : ℤ)) := by
  let : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨z, hz⟩ := construction_principal_laurent_integer_factors hbc habc he hn j hj
  have h2 := padicValRatTop_ge_of_integer_power_factor 2
    (constructionTwoSaving b c * n - 1 + (3 * j + 1) / 2)
    (constructionLaurentCoeff a b c n (j : ℤ))
    ⟨(5 : ℤ) ^ (2 * (a + b - c) * n + j) * z, by push_cast; rw [hz]; ring⟩
  have h5 := padicValRatTop_ge_of_integer_power_factor 5 (2 * (a + b - c) * n + j)
    (constructionLaurentCoeff a b c n (j : ℤ))
    ⟨(2 : ℤ) ^ (constructionTwoSaving b c * n - 1 + (3 * j + 1) / 2) * z,
      by push_cast; rw [hz]; ring⟩
  have hle : ((constructionTwoSaving b c * n : ℕ) : ℤ) + 3 * (j : ℤ) / 2 - 1 ≤
      ((constructionTwoSaving b c * n - 1 + (3 * j + 1) / 2 : ℕ) : ℤ) := by omega
  exact ⟨(WithTop.coe_le_coe.mpr hle).trans h2, h5⟩

end PiIrrationality
