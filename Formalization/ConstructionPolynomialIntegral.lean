import Formalization.ConstructionPolynomialCoefficients
import Formalization.ConstructionPolynomialClearing
import Formalization.PolynomialTenClearing

/-! The second polynomial clearing and coprime intersection for general triples, (2.31)--(2.32). -/

namespace PiIrrationality

open Polynomial

theorem construction_reduced_polynomial_monomial_integral
    {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n) (q : ℕ) (hq : q < constructionDegree a b c * n - 1) :
    ∃ G : GI, (10 : ℂ) ^ (constructionDegree a b c * n - 1) * (constructionReducedLcm a b c n : ℂ) *
      (constructionPoleShiftCoeff a b c n q : ℂ) * (-(∫ s : ℝ in (-2)..2, (verticalSegment s + 5) ^ q)) =
        (G : ℂ) := by
  obtain ⟨z, hz⟩ := constructionPoleAntiderivativeCoeff_integral hc hp hn q hq
  have hzC := congrArg (fun x : ℚ => (x : ℂ)) hz
  unfold constructionPoleAntiderivativeCoeff at hzC
  push_cast at hzC
  have hqC : (q + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero q
  have hpow : (10 : ℂ) ^ (constructionDegree a b c * n - 1) =
      10 ^ (constructionDegree a b c * n - 1 - (q + 1)) * 10 ^ (q + 1) := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  refine ⟨(10 : GI) ^ (constructionDegree a b c * n - 1 - (q + 1)) * (z : GI) * poleIntegralEndpointFactor q, ?_⟩
  rw [poleMonomial_integral, hpow]
  calc
    _ = (10 : ℂ) ^ (constructionDegree a b c * n - 1 - (q + 1)) *
        (10 ^ (q + 1) * (constructionReducedLcm a b c n : ℂ) * (constructionPoleShiftCoeff a b c n q : ℂ) / (q + 1)) *
          (poleIntegralEndpointFactor q : ℂ) := by ring
    _ = _ := by rw [hzC]; simp only [map_mul, map_pow, map_ofNat, map_intCast]

theorem construction_ten_power_polynomial_gaussian {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n) :
    ∃ G : GI, (10 : ℂ) ^ (constructionDegree a b c * n - 1) * (constructionReducedLcm a b c n : ℂ) *
      (-(∫ s : ℝ in (-2)..2, aeval (verticalSegment s) (constructionPolynomialPart a b c n))) = (G : ℂ) := by
  classical
  let G (q : ℕ) : GI := if hq : q < constructionDegree a b c * n - 1 then
    (construction_reduced_polynomial_monomial_integral hc he hp hn q hq).choose else 0
  refine ⟨∑ q ∈ Finset.range (constructionDegree a b c * n - 1), G q, ?_⟩
  simp_rw [constructionPolynomial_pole_expansion hc hp hn]
  rw [intervalIntegral.integral_finsetSum]
  · rw [← Finset.sum_neg_distrib, Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [intervalIntegral.integral_const_mul]
    have hq' := Finset.mem_range.mp hq
    have h := (construction_reduced_polynomial_monomial_integral hc he hp hn q hq').choose_spec
    dsimp only [G]
    rw [dif_pos hq']
    rw [← h]
    ring
  · intro q _
    exact (continuous_const.mul
      ((verticalSegment_continuous.add continuous_const).pow q)).intervalIntegrable _ _

theorem construction_ten_power_polynomial_integral {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n) :
    ∃ z : ℤ, (10 : ℚ) ^ (constructionDegree a b c * n - 1) * constructionReducedLcm a b c n *
      verticalPolynomialIntegralRat (constructionPolynomialPart a b c n) = (z : ℚ) := by
  apply rational_gaussian_integer_is_integer
  obtain ⟨G, hG⟩ := construction_ten_power_polynomial_gaussian hc he hp hn
  refine ⟨G, ?_⟩
  rw [verticalPolynomial_integral_rat] at hG
  push_cast
  exact hG

theorem constructionNormalizedPolynomialIntegral_integral {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n) :
    ∃ z : ℤ, constructionNormalizedPolynomialIntegral a b c n = (z : ℂ) := by
  let x : ℚ := (2 : ℚ) ^ (1 - (constructionTwoSaving b c : ℤ) * n) * constructionReducedLcm a b c n *
    verticalPolynomialIntegralRat (constructionPolynomialPart a b c n)
  have hx : constructionNormalizedPolynomialIntegral a b c n = (x : ℂ) := by
    rw [constructionNormalizedPolynomialIntegral, verticalPolynomial_integral_rat]
    dsimp only [x]
    push_cast
    rfl
  have hconstructionPhi : ∃ z : ℤ, (constructionPhi a b c n : ℚ) * x = (z : ℚ) := by
    obtain ⟨z, hz⟩ := constructionNormalizedPolynomialIntegral_Phi_multiple_integral hc he hp hn
    refine ⟨z, ?_⟩
    apply Rat.cast_injective (α := ℂ)
    push_cast
    rw [← hx]
    exact hz
  have hten : ∃ K : ℕ, ∃ z : ℤ, (10 : ℚ) ^ K * x = (z : ℚ) := by
    obtain ⟨z, hz⟩ := construction_ten_power_polynomial_integral hc he hp hn
    have h2 : (10 : ℚ) ^ (constructionTwoSaving b c * n) * 2 ^ (1 - (constructionTwoSaving b c : ℤ) * n) =
        2 * 5 ^ (constructionTwoSaving b c * n) := by
      rw [show (10 : ℚ) = 2 * 5 by norm_num, mul_pow]
      calc
        _ = ((2 : ℚ) ^ (constructionTwoSaving b c * n) * 2 ^ (1 - (constructionTwoSaving b c : ℤ) * n)) * 5 ^ (constructionTwoSaving b c * n) := by ring
        _ = _ := by
          rw [← zpow_natCast (2 : ℚ) (constructionTwoSaving b c * n),
            ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
          rw [show ((constructionTwoSaving b c * n : ℕ) : ℤ) + (1 - (constructionTwoSaving b c : ℤ) * n) = 1 by omega, zpow_one]
    refine ⟨constructionTwoSaving b c * n + (constructionDegree a b c * n - 1), 2 * (5 : ℤ) ^ (constructionTwoSaving b c * n) * z, ?_⟩
    dsimp only [x]
    rw [pow_add]
    calc
      _ = ((10 : ℚ) ^ (constructionTwoSaving b c * n) * 2 ^ (1 - (constructionTwoSaving b c : ℤ) * n)) *
          (10 ^ (constructionDegree a b c * n - 1) * constructionReducedLcm a b c n *
            verticalPolynomialIntegralRat (constructionPolynomialPart a b c n)) := by ring
      _ = _ := by rw [h2, hz]; push_cast; rfl
  obtain ⟨z, hz⟩ := construction_integer_of_Phi_and_ten_power a b c n x hconstructionPhi hten
  refine ⟨z, ?_⟩
  rw [hx, hz]
  push_cast
  rfl



end PiIrrationality
