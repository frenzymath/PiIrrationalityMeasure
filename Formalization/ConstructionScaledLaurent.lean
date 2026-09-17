import Formalization.ConstructionLaurent
import Formalization.ConstructionArithmetic
import Formalization.ScaledLaurent

/-! Complete Laurent integrality and the two valuation bounds (2.7) for general triples. -/

namespace PiIrrationality

noncomputable def constructionScaledNumerator (a b n : ℕ) : Polynomial ℤ :=
  (2 * Polynomial.X - 1) ^ (2 * a * n) *
    (5 * Polynomial.X ^ 2 - 4 * Polynomial.X + 1) ^ (b * n) *
    (5 * Polynomial.X ^ 2 - 6 * Polynomial.X + 2) ^ (b * n)

noncomputable def constructionScaledCoreInt (a b c n k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (k + 1),
    (Polynomial.hasseDeriv i (constructionScaledNumerator a b n)).eval 0 *
      ((c * n + (k - i)).choose (k - i) : ℤ)

noncomputable def constructionScaledCoeffInt (a b c n k : ℕ) : ℤ :=
  2 ^ ((4 * b - 2 * c) * n - 1) * 5 ^ (2 * (a + b - c) * n) *
    constructionScaledCoreInt a b c n k

theorem constructionScaledNumerator_aeval (a b n : ℕ) (x : ℝ) :
    Polynomial.aeval x (constructionScaledNumerator a b n) =
      (2 * x - 1) ^ (2 * a * n) *
        (5 * x ^ 2 - 4 * x + 1) ^ (b * n) *
        (5 * x ^ 2 - 6 * x + 2) ^ (b * n) := by
  simp [constructionScaledNumerator, map_ofNat]

theorem constructionScaledCoreInt_eq_deriv (a b c n k : ℕ) :
    normalizedDeriv k
      (fun x : ℝ => Polynomial.aeval x (constructionScaledNumerator a b n) *
        (1 - x) ^ (-(c * n + 1 : ℕ) : ℤ)) 0 =
      (constructionScaledCoreInt a b c n k : ℝ) := by
  have hpoly : ContDiffAt ℝ k
      (fun x : ℝ => Polynomial.aeval x (constructionScaledNumerator a b n)) 0 :=
    ((constructionScaledNumerator a b n).contDiff_aeval k).contDiffAt
  have hinv : ContDiffAt ℝ k
      (fun x : ℝ => (1 - x) ^ (-(c * n + 1 : ℕ) : ℤ)) 0 := by
    simp only [zpow_neg, zpow_natCast]
    exact ((contDiffAt_const.sub contDiffAt_id).pow _).inv (by norm_num)
  rw [normalizedDeriv_mul hpoly hinv]
  simp only [constructionScaledCoreInt, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro i hi
  rw [normalizedDeriv_one_sub_inv]
  have h := normalizedDeriv_int_polynomial i (constructionScaledNumerator a b n) 0
  norm_num only [Int.cast_zero] at h
  rw [h]

theorem construction_scaled_constant {a b c n : ℕ} (hbc : c < 2 * b)
    (habc : c ≤ a + b) (hn : 0 < n) :
    (5 : ℝ) * 5 ^ (2 * a * n) * 20 ^ (2 * (b * n)) /
        10 ^ (c * n + 1) =
      10 ^ (c * n) * (2 ^ ((4 * b - 2 * c) * n - 1) *
        5 ^ (2 * (a + b - c) * n)) := by
  have hbn : c * n < 2 * (b * n) := by nlinarith
  have habn : c * n ≤ a * n + b * n := by nlinarith
  have hd : (4 * b - 2 * c) * n = 4 * (b * n) - 2 * (c * n) := by
    rw [Nat.sub_mul]
    simp only [Nat.mul_assoc]
  have he : 2 * (a + b - c) * n = 2 * (a * n + b * n - c * n) := by
    rw [Nat.mul_assoc, Nat.sub_mul, Nat.add_mul]
  have h2 : 4 * (b * n) = (c * n + 1) + c * n + ((4 * b - 2 * c) * n - 1) := by
    omega
  have h5 : 1 + 2 * a * n + 2 * (b * n) =
      (c * n + 1) + c * n + 2 * (a + b - c) * n := by
    rw [he, Nat.mul_assoc]
    omega
  apply (div_eq_iff (by positivity : (10 : ℝ) ^ (c * n + 1) ≠ 0)).2
  calc
    (5 : ℝ) * 5 ^ (2 * a * n) * 20 ^ (2 * (b * n)) =
        2 ^ (4 * (b * n)) * 5 ^ (1 + 2 * a * n + 2 * (b * n)) := by
      rw [show (20 : ℝ) = 2 ^ 2 * 5 by norm_num, mul_pow, ← pow_mul]
      simp only [pow_add, pow_one]
      ring
    _ = _ := by
      rw [h2, h5]
      simp only [pow_add, show (10 : ℝ) = 2 * 5 by norm_num, mul_pow]
      ring

theorem construction_regularized_scaled_variable {a b c n : ℕ}
    (hbc : c < 2 * b) (habc : c ≤ a + b) (hn : 0 < n) (x : ℝ) :
    constructionRegularized a b c n (-5 + 10 * x) =
      (10 : ℝ) ^ (c * n) *
        (2 ^ ((4 * b - 2 * c) * n - 1) * 5 ^ (2 * (a + b - c) * n)) *
        Polynomial.aeval x (constructionScaledNumerator a b n) *
        (1 - x) ^ (-(c * n + 1 : ℕ) : ℤ) := by
  rw [constructionRegularized_formula, constructionScaledNumerator_aeval]
  rw [show (-5 : ℝ) + 10 * x = 5 * (2 * x - 1) by ring]
  have hq : (5 * (2 * x - 1)) ^ 4 + 6 * (5 * (2 * x - 1)) ^ 2 + 25 =
      (20 * (5 * x ^ 2 - 4 * x + 1)) * (20 * (5 * x ^ 2 - 6 * x + 2)) := by ring
  rw [hq, show (5 : ℝ) - 5 * (2 * x - 1) = 10 * (1 - x) by ring]
  simp only [mul_pow, div_eq_mul_inv, mul_inv, zpow_neg, zpow_natCast]
  have hc := construction_scaled_constant hbc habc hn
  rw [show 2 * (b * n) = b * n + b * n by omega, pow_add] at hc
  simp only [div_eq_mul_inv] at hc
  calc
    _ = (5 * 5 ^ (2 * a * n) *
        (20 ^ (b * n) * 20 ^ (b * n)) * (10 ^ (c * n + 1))⁻¹) *
        ((2 * x - 1) ^ (2 * a * n) *
          (5 * x ^ 2 - 4 * x + 1) ^ (b * n) *
          (5 * x ^ 2 - 6 * x + 2) ^ (b * n)) *
        ((1 - x) ^ (c * n + 1))⁻¹ := by ring
    _ = _ := by rw [hc]

theorem constructionScaledCoeffInt_eq_actual {a b c n : ℕ}
    (hbc : c < 2 * b) (habc : c ≤ a + b) (hn : 0 < n)
    (j : ℤ) (hj : j ≤ c * (n : ℤ)) :
    (constructionScaledCoeffInt a b c n (c * (n : ℤ) - j).toNat : ℚ) =
      (10 : ℚ) ^ (-j) * constructionLaurentCoeff a b c n j := by
  let k := (c * (n : ℤ) - j).toNat
  have hk : (k : ℤ) = c * (n : ℤ) - j := Int.toNat_of_nonneg (by omega)
  apply Rat.cast_injective (α := ℝ)
  push_cast
  rw [constructionLaurentCoeff_cast _ _ _ _ _ hj]
  have hf : (fun x : ℝ => constructionRegularized a b c n (-5 + 10 * x)) =
      fun x : ℝ => ((10 : ℝ) ^ (c * n) *
        (2 ^ ((4 * b - 2 * c) * n - 1) * 5 ^ (2 * (a + b - c) * n))) *
        (Polynomial.aeval x (constructionScaledNumerator a b n) *
          (1 - x) ^ (-(c * n + 1 : ℕ) : ℤ)) := by
    funext x
    rw [construction_regularized_scaled_variable hbc habc hn]
    ring
  have hd := normalizedDeriv_affine k (constructionRegularized a b c n) 10 (-5)
  rw [hf, normalizedDeriv_const_mul, constructionScaledCoreInt_eq_deriv] at hd
  have h10 : (10 : ℝ) ^ (-j) = (10 : ℝ) ^ k / (10 : ℝ) ^ (c * n) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (by norm_num : (10 : ℝ) ≠ 0)]
    congr 1
    push_cast
    omega
  rw [h10, div_mul_eq_mul_div, ← hd]
  simp only [constructionScaledCoeffInt, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  field_simp
  rfl

theorem construction_scaled_laurent_integer_factors {a b c n : ℕ}
    (hbc : c < 2 * b) (habc : c ≤ a + b) (hn : 0 < n) (j : ℤ) :
    ∃ z : ℤ, (10 : ℚ) ^ (-j) * constructionLaurentCoeff a b c n j =
      (2 : ℚ) ^ ((4 * b - 2 * c) * n - 1) *
        5 ^ (2 * (a + b - c) * n) * (z : ℚ) := by
  by_cases hj : j ≤ c * (n : ℤ)
  · refine ⟨constructionScaledCoreInt a b c n (c * (n : ℤ) - j).toNat, ?_⟩
    rw [← constructionScaledCoeffInt_eq_actual hbc habc hn j hj]
    simp [constructionScaledCoeffInt]
  · refine ⟨0, ?_⟩
    rw [constructionLaurentCoeff_zero_of_outside _ _ _ _ _ (lt_of_not_ge hj)]
    simp

theorem construction_scaled_laurent_integral {a b c n : ℕ}
    (hbc : c < 2 * b) (habc : c ≤ a + b) (hn : 0 < n) (j : ℤ) :
    ∃ z : ℤ, (10 : ℚ) ^ (-j) * constructionLaurentCoeff a b c n j = (z : ℚ) := by
  obtain ⟨z, hz⟩ := construction_scaled_laurent_integer_factors hbc habc hn j
  refine ⟨2 ^ ((4 * b - 2 * c) * n - 1) * 5 ^ (2 * (a + b - c) * n) * z, ?_⟩
  push_cast
  exact hz

theorem construction_scaled_laurent_valuations {a b c n : ℕ}
    (hbc : c < 2 * b) (habc : c ≤ a + b) (hn : 0 < n) (j : ℤ) :
    ((((4 * b - 2 * c) * n : ℕ) : ℤ) - 1 : WithTop ℤ) ≤
        padicValRatTop 2 ((10 : ℚ) ^ (-j) * constructionLaurentCoeff a b c n j) ∧
      (((2 * (a + b - c) * n : ℕ) : ℤ) : WithTop ℤ) ≤
        padicValRatTop 5 ((10 : ℚ) ^ (-j) * constructionLaurentCoeff a b c n j) := by
  let : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨z, hz⟩ := construction_scaled_laurent_integer_factors hbc habc hn j
  have h2 := padicValRatTop_ge_of_integer_power_factor 2 ((4 * b - 2 * c) * n - 1)
    ((10 : ℚ) ^ (-j) * constructionLaurentCoeff a b c n j)
    ⟨(5 : ℤ) ^ (2 * (a + b - c) * n) * z, by push_cast; rw [hz]; ring⟩
  have h5 := padicValRatTop_ge_of_integer_power_factor 5 (2 * (a + b - c) * n)
    ((10 : ℚ) ^ (-j) * constructionLaurentCoeff a b c n j)
    ⟨(2 : ℤ) ^ ((4 * b - 2 * c) * n - 1) * z, by push_cast; rw [hz]; ring⟩
  have hpos : 0 < (4 * b - 2 * c) * n := Nat.mul_pos (by omega) hn
  have he : (((4 * b - 2 * c) * n - 1 : ℕ) : ℤ) =
      (((4 * b - 2 * c) * n : ℕ) : ℤ) - 1 := by omega
  rw [he] at h2
  exact ⟨by exact_mod_cast h2, h5⟩

end PiIrrationality
