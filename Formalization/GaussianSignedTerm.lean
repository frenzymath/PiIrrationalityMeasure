import Formalization.GaussianExpansion

/-! The signed Gaussian factorization of each summand in (2.11). -/

namespace PiIrrationality.GaussianExpansion

open Complex

noncomputable def signedSummand (a b c n : ℕ) (j : ℤ) (m : Fin 6 → ℕ) : ℂ :=
  (-1) ^ (m 1 + m 2 + m 3 + m 4 + m 5) * (weight a b c n m : ℂ) *
    2 ^ ((5 * (b : ℤ) - 2 * c) * n - 1 + j + m 1) *
    5 ^ (2 * ((a : ℤ) + b - c) * n + j) *
    (1 - I) ^ (-(m 4 : ℤ)) * (1 + I) ^ (-(m 5 : ℤ)) *
    (2 + I) ^ (m 2 + m 5) * (2 - I) ^ (m 3 + m 4)

private theorem pow_sub_as_zpow (x : ℂ) (hx : x ≠ 0) (N k : ℕ) (hk : k ≤ N) :
    x ^ (N - k) = x ^ N * x ^ (-(k : ℤ)) := by
  rw [← zpow_natCast, Nat.cast_sub hk, sub_eq_add_neg, zpow_add₀ hx, zpow_natCast]

private theorem inverse_four_plus (k : ℕ) :
    (-4 + 2 * I) ^ (-(k : ℤ)) =
      (-1 : ℂ) ^ k * 2 ^ (-(k : ℤ)) * 5 ^ (-(k : ℤ)) * (2 + I) ^ k := by
  have h : (-4 + 2 * I : ℂ)⁻¹ = -1 * 2⁻¹ * 5⁻¹ * (2 + I) := by
    norm_num [Complex.ext_iff, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
  simp only [zpow_neg, zpow_natCast, ← inv_pow, h, mul_pow]

private theorem inverse_four_minus (k : ℕ) :
    (-4 - 2 * I) ^ (-(k : ℤ)) =
      (-1 : ℂ) ^ k * 2 ^ (-(k : ℤ)) * 5 ^ (-(k : ℤ)) * (2 - I) ^ k := by
  have h : (-4 - 2 * I : ℂ)⁻¹ = -1 * 2⁻¹ * 5⁻¹ * (2 - I) := by
    norm_num [Complex.ext_iff, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
  simp only [zpow_neg, zpow_natCast, ← inv_pow, h, mul_pow]

private theorem inverse_six_plus (k : ℕ) :
    (-6 + 2 * I) ^ (-(k : ℤ)) =
      (-1 : ℂ) ^ k * 2 ^ (-(k : ℤ)) * 5 ^ (-(k : ℤ)) *
        (1 - I) ^ (-(k : ℤ)) * (2 - I) ^ k := by
  have h : (-6 + 2 * I : ℂ)⁻¹ = -1 * 2⁻¹ * 5⁻¹ * (1 - I)⁻¹ * (2 - I) := by
    norm_num [Complex.ext_iff, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
  simp only [zpow_neg, zpow_natCast, ← inv_pow, h, mul_pow]

private theorem inverse_six_minus (k : ℕ) :
    (-6 - 2 * I) ^ (-(k : ℤ)) =
      (-1 : ℂ) ^ k * 2 ^ (-(k : ℤ)) * 5 ^ (-(k : ℤ)) *
        (1 + I) ^ (-(k : ℤ)) * (2 + I) ^ k := by
  have h : (-6 - 2 * I : ℂ)⁻¹ = -1 * 2⁻¹ * 5⁻¹ * (1 + I)⁻¹ * (2 + I) := by
    norm_num [Complex.ext_iff, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
  simp only [zpow_neg, zpow_natCast, ← inv_pow, h, mul_pow]

private theorem inverse_five (k : ℕ) :
    (-5 : ℂ) ^ (-(k : ℤ)) = (-1 : ℂ) ^ k * 5 ^ (-(k : ℤ)) := by
  rw [show (-5 : ℂ) = -1 * 5 by norm_num, mul_zpow]
  simp [← inv_pow]

private theorem numerator_base (A B : ℕ) :
    (-5 : ℂ) ^ (2 * A) * (-4 + 2 * I) ^ B * (-4 - 2 * I) ^ B *
      (-6 + 2 * I) ^ B * (-6 - 2 * I) ^ B =
      2 ^ (5 * B) * 5 ^ (2 * A + 2 * B) := by
  have h : (-4 + 2 * I : ℂ) * (-4 - 2 * I) *
      (-6 + 2 * I) * (-6 - 2 * I) = 800 := by
    norm_num [Complex.ext_iff]
  calc
    _ = (-5 : ℂ) ^ (2 * A) *
        ((-4 + 2 * I) * (-4 - 2 * I) * (-6 + 2 * I) * (-6 - 2 * I)) ^ B := by
      simp only [mul_pow]
      ring
    _ = 5 ^ (2 * A) * (2 ^ 5 * 5 ^ 2 : ℂ) ^ B := by
      rw [h, pow_mul, pow_mul]
      norm_num
    _ = _ := by
      simp only [mul_pow, pow_mul, pow_add]
      ring

private theorem raw_split (a b c n : ℕ) (m : Fin 6 → ℕ)
    (hm : NumeratorBounds a b n m) :
    rawSummand a b c n m =
      (weight a b c n m : ℂ) * 5 * 10 ^ (-(c * (n : ℤ)) - 1) *
        2 ^ (5 * (b * n)) * 5 ^ (2 * (a * n) + 2 * (b * n)) *
        10 ^ (-(m 0 : ℤ)) * (-5) ^ (-(m 1 : ℤ)) *
        (-4 + 2 * I) ^ (-(m 2 : ℤ)) * (-4 - 2 * I) ^ (-(m 3 : ℤ)) *
        (-6 + 2 * I) ^ (-(m 4 : ℤ)) * (-6 - 2 * I) ^ (-(m 5 : ℤ)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hm
  have h4p : (-4 + 2 * I : ℂ) ≠ 0 := by norm_num [Complex.ext_iff]
  have h4m : (-4 - 2 * I : ℂ) ≠ 0 := by norm_num [Complex.ext_iff]
  have h6p : (-6 + 2 * I : ℂ) ≠ 0 := by norm_num [Complex.ext_iff]
  have h6m : (-6 - 2 * I : ℂ) ≠ 0 := by norm_num [Complex.ext_iff]
  unfold rawSummand
  rw [pow_sub_as_zpow (-5) (by norm_num) _ _ h1,
    pow_sub_as_zpow _ h4p _ _ h2, pow_sub_as_zpow _ h4m _ _ h3,
    pow_sub_as_zpow _ h6p _ _ h4, pow_sub_as_zpow _ h6m _ _ h5,
    sub_eq_add_neg (-(c * (n : ℤ)) - 1) (m 0),
    zpow_add₀ (by norm_num : (10 : ℂ) ≠ 0)]
  calc
    _ = (weight a b c n m : ℂ) * 5 * 10 ^ (-(c * (n : ℤ)) - 1) *
        ((-5) ^ (2 * (a * n)) * (-4 + 2 * I) ^ (b * n) *
          (-4 - 2 * I) ^ (b * n) * (-6 + 2 * I) ^ (b * n) *
          (-6 - 2 * I) ^ (b * n)) *
        10 ^ (-(m 0 : ℤ)) * (-5) ^ (-(m 1 : ℤ)) *
        (-4 + 2 * I) ^ (-(m 2 : ℤ)) * (-4 - 2 * I) ^ (-(m 3 : ℤ)) *
        (-6 + 2 * I) ^ (-(m 4 : ℤ)) * (-6 - 2 * I) ^ (-(m 5 : ℤ)) := by
      simp only [Nat.mul_assoc]
      ring
    _ = _ := by rw [numerator_base]; ring

theorem rawSummand_eq_signedSummand (a b c n : ℕ) (j : ℤ)
    (m : Fin 6 → ℕ) (hm : m ∈ indices a b c n j) (hj : j ≤ c * (n : ℤ)) :
    rawSummand a b c n m = signedSummand a b c n j m := by
  obtain ⟨hs, hb⟩ := (mem_indices a b c n j hj m).mp hm
  have hsum : (m 0 : ℤ) + m 1 + m 2 + m 3 + m 4 + m 5 = c * (n : ℤ) - j := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change (m 0 : ℤ) + (m 1 + (m 2 + (m 3 + (m 4 + m 5)))) = _ at hs
    simpa only [add_assoc] using hs
  have he2 : (5 * (b : ℤ) - 2 * c) * n - 1 + j + m 1 =
      (5 * (b * n) : ℕ) + (-(c * (n : ℤ)) - 1) - m 0 - m 2 - m 3 - m 4 - m 5 := by
    push_cast
    linear_combination hsum
  have he5 : 2 * ((a : ℤ) + b - c) * n + j =
      (2 * (a * n) + 2 * (b * n) : ℕ) + 1 + (-(c * (n : ℤ)) - 1) -
        m 0 - m 1 - m 2 - m 3 - m 4 - m 5 := by
    push_cast
    linear_combination hsum
  rw [raw_split a b c n m hb, inverse_five, inverse_four_plus, inverse_four_minus,
    inverse_six_plus, inverse_six_minus]
  unfold signedSummand
  rw [he2, he5]
  simp only [show (10 : ℂ) = 2 * 5 by norm_num, mul_zpow, sub_eq_add_neg,
    zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0),
    zpow_add₀ (by norm_num : (5 : ℂ) ≠ 0), zpow_natCast, zpow_one, pow_add]
  ring

theorem signed_expansion (a b c n : ℕ) (j : ℤ) (hj : j ≤ c * (n : ℤ)) :
    (constructionLaurentCoeff a b c n j : ℂ) =
      ∑ m ∈ indices a b c n j, signedSummand a b c n j m := by
  rw [raw_expansion a b c n j hj]
  exact Finset.sum_congr rfl (fun m hm => rawSummand_eq_signedSummand a b c n j m hm hj)

end PiIrrationality.GaussianExpansion
