import Formalization.ConstructionEndpointDivisibility
import Formalization.ConstructionReducedLcm

/-! General polynomial integral clearing by the original LCM, equation (2.28). -/

namespace PiIrrationality

open Polynomial

noncomputable def constructionOriginalNormalizedPolynomialIntegral (a b c n : ℕ) : ℂ :=
  (2 : ℂ) ^ (1 - (constructionTwoSaving b c : ℤ) * n) * (lcmRange (constructionDegree a b c * n) : ℂ) *
    (-(∫ s : ℝ in (-2)..2, aeval (verticalSegment s) (constructionPolynomialPart a b c n)))

noncomputable def constructionOriginalNormalizedEndpointTerm (a b c n k : ℕ) : ℂ :=
  (2 : ℂ) ^ (1 - (constructionTwoSaving b c : ℤ) * n) * (lcmRange (constructionDegree a b c * n) : ℂ) *
    Complex.I * (constructionEndpointCoeff a b c n k : ℂ) * (4 * Complex.I) ^ (k + 1) / (k + 1 : ℂ)

theorem construction_polynomial_two_power_balance (a b c n k : ℕ) :
    (2 : ℂ) ^ (1 - (constructionTwoSaving b c : ℤ) * n) * 4 ^ (k + 1) =
      2 ^ (2 * k - (3 * k + 1) / 2) * 2 ^ constructionEndpointTwoExponent b c n k := by
  rw [show (4 : ℂ) = 2 ^ 2 by norm_num, ← pow_mul,
    ← zpow_natCast (2 : ℂ) (2 * (k + 1)),
    ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0),
    ← zpow_natCast (2 : ℂ) (2 * k - (3 * k + 1) / 2),
    ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0)]
  congr 1
  unfold constructionEndpointTwoExponent
  omega

theorem constructionOriginalNormalizedEndpointTerm_is_gaussian_integer
    {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n) (k : ℕ) (hk : k < constructionDegree a b c * n - 1) :
    ∃ z : GI, constructionOriginalNormalizedEndpointTerm a b c n k = (z : ℂ) := by
  obtain ⟨q, hq⟩ := dvd_lcmRange (constructionDegree a b c * n) (k + 1) (by omega) (by omega)
  obtain ⟨G, hG⟩ := constructionNormalizedEndpointCoeff_integral hc he hp hn k
  have hqC : (lcmRange (constructionDegree a b c * n) : ℂ) = (k + 1 : ℂ) * (q : ℂ) := by
    exact_mod_cast hq
  have hkC : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  refine ⟨(2 : GI) ^ (2 * k - (3 * k + 1) / 2) * G * giI ^ (k + 2) * q, ?_⟩
  unfold constructionOriginalNormalizedEndpointTerm
  rw [hqC, mul_pow]
  calc
    _ = ((2 : ℂ) ^ (1 - (constructionTwoSaving b c : ℤ) * n) * 4 ^ (k + 1)) *
        (constructionEndpointCoeff a b c n k : ℂ) * Complex.I ^ (k + 2) * (q : ℂ) := by
      field_simp
      simp only [pow_succ]
      ring
    _ = (2 : ℂ) ^ (2 * k - (3 * k + 1) / 2) *
        constructionNormalizedEndpointCoeff a b c n k * Complex.I ^ (k + 2) * (q : ℂ) := by
      rw [construction_polynomial_two_power_balance a b c n k]
      unfold constructionNormalizedEndpointCoeff
      ring
    _ = _ := by
      rw [hG]
      simp only [map_mul, map_pow, map_ofNat, map_natCast, giI_toComplex]

theorem constructionOriginalNormalizedPolynomialIntegral_eq_sum {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n) :
    constructionOriginalNormalizedPolynomialIntegral a b c n =
      ∑ k ∈ Finset.range (constructionDegree a b c * n - 1), constructionOriginalNormalizedEndpointTerm a b c n k := by
  unfold constructionOriginalNormalizedPolynomialIntegral
  rw [constructionPolynomial_endpoint_integral hc hp hn, ← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold constructionOriginalNormalizedEndpointTerm
  ring

theorem constructionOriginalNormalizedPolynomialIntegral_is_gaussian_integer {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n) :
    ∃ z : GI, constructionOriginalNormalizedPolynomialIntegral a b c n = (z : ℂ) := by
  classical
  let z (k : ℕ) : GI := if hk : k < constructionDegree a b c * n - 1 then
    (constructionOriginalNormalizedEndpointTerm_is_gaussian_integer hc he hp hn k hk).choose else 0
  refine ⟨∑ k ∈ Finset.range (constructionDegree a b c * n - 1), z k, ?_⟩
  rw [constructionOriginalNormalizedPolynomialIntegral_eq_sum hc he hp hn, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  dsimp only [z]
  rw [dif_pos hk']
  exact (constructionOriginalNormalizedEndpointTerm_is_gaussian_integer hc he hp hn k hk').choose_spec

theorem constructionOriginalNormalizedPolynomialIntegral_is_integer {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n) :
    ∃ z : ℤ, constructionOriginalNormalizedPolynomialIntegral a b c n = (z : ℂ) := by
  obtain ⟨G, hG⟩ := constructionOriginalNormalizedPolynomialIntegral_is_gaussian_integer hc he hp hn
  have hrat : constructionOriginalNormalizedPolynomialIntegral a b c n =
      ((2 : ℚ) ^ (1 - (constructionTwoSaving b c : ℤ) * n) * (lcmRange (constructionDegree a b c * n) : ℚ) *
        verticalPolynomialIntegralRat (constructionPolynomialPart a b c n) : ℚ) := by
    rw [constructionOriginalNormalizedPolynomialIntegral, verticalPolynomial_integral_rat]
    push_cast
    rfl
  have him : G.im = 0 := by
    have h := congrArg Complex.im (hG.symm.trans hrat)
    have hzero : (G : ℂ).im = 0 := by simpa only [Complex.ratCast_im] using h
    have hInt : ((G.im : ℤ) : ℝ) = 0 := by
      rw [GaussianInt.intCast_im]
      exact hzero
    exact_mod_cast hInt
  refine ⟨G.re, ?_⟩
  rw [hG, GaussianInt.toComplex_def, him]
  simp

noncomputable def constructionNormalizedPolynomialIntegral (a b c n : ℕ) : ℂ :=
  (2 : ℂ) ^ (1 - (constructionTwoSaving b c : ℤ) * n) * (constructionReducedLcm a b c n : ℂ) *
    (-(∫ s : ℝ in (-2)..2, aeval (verticalSegment s) (constructionPolynomialPart a b c n)))

theorem constructionNormalizedPolynomialIntegral_mul_Phi (a b c n : ℕ) :
    (constructionPhi a b c n : ℂ) * constructionNormalizedPolynomialIntegral a b c n = constructionOriginalNormalizedPolynomialIntegral a b c n := by
  have hq : constructionReducedLcm a b c n * (constructionPhi a b c n : ℚ) =
      (lcmRange (constructionDegree a b c * n) : ℚ) := by
    rw [constructionReducedLcm, div_mul_cancel₀ _
      (by exact_mod_cast (constructionPhi_pos a b c n).ne')]
  have h := congrArg (fun x : ℚ => (x : ℂ)) hq
  push_cast at h
  unfold constructionNormalizedPolynomialIntegral constructionOriginalNormalizedPolynomialIntegral
  calc
    _ = (2 : ℂ) ^ (1 - (constructionTwoSaving b c : ℤ) * n) * ((constructionReducedLcm a b c n : ℂ) * (constructionPhi a b c n : ℂ)) *
      (-(∫ s : ℝ in (-2)..2, aeval (verticalSegment s) (constructionPolynomialPart a b c n))) := by ring
    _ = _ := by rw [h]

theorem constructionNormalizedPolynomialIntegral_Phi_multiple_integral {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n) :
    ∃ z : ℤ, (constructionPhi a b c n : ℂ) * constructionNormalizedPolynomialIntegral a b c n = (z : ℂ) := by
  rw [constructionNormalizedPolynomialIntegral_mul_Phi]
  exact constructionOriginalNormalizedPolynomialIntegral_is_integer hc he hp hn

end PiIrrationality
