import Formalization.ConstructionLaurent
import Formalization.ConstructionArithmetic
import Formalization.EndpointPolynomial
import Formalization.ComplexDerivative

/-! Actual polynomial degrees and endpoint and pole Taylor coordinates for general triples. -/

namespace PiIrrationality

open Polynomial

theorem constructionNumeratorY_natDegree (a b n : ℕ) :
    (constructionNumeratorY a b n).natDegree = a * n + 2 * (b * n) := by
  have hquad : (X ^ 2 + C (6 : ℤ) * X + C 25).natDegree = 2 := by
    compute_degree <;> norm_num
  have hquad0 : (X ^ 2 + C (6 : ℤ) * X + C 25) ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hquad
    omega
  rw [constructionNumeratorY, mul_assoc, natDegree_C_mul (by norm_num : (5 : ℤ) ≠ 0),
    natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hquad0),
    natDegree_X_pow, natDegree_pow, hquad]
  omega

theorem constructionPolynomialPart_natDegree {a b c : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) (n : ℕ) :
    (constructionPolynomialPart a b c n).natDegree = constructionDegree a b c * n - 2 := by
  have hh := (construction_admissible_inequalities hc hp).2.2.2
  rw [constructionPolynomialPart, EvenPole.part, natDegree_comp, natDegree_X_pow,
    EvenPole.partY, natDegree_divByMonic _ (EvenPole.denominatorY_monic _),
    EvenPole.signedNumeratorY, natDegree_C_mul (pow_ne_zero _ (by norm_num)),
    constructionNumeratorY_natDegree, EvenPole.denominatorY, natDegree_pow,
    natDegree_X_sub_C, mul_one]
  have hd : constructionDegree a b c * n =
      2 * (a * n) + 4 * (b * n) - 2 * (c * n) := by
    simp only [constructionDegree, Nat.sub_mul, Nat.add_mul, Nat.mul_assoc]
  rw [hd]
  omega

noncomputable def constructionEndpointPolynomial (a b c n : ℕ) : Polynomial GI :=
  taylor lowerEndpointGI ((constructionPolynomialPart a b c n).map (Int.castRingHom GI))

noncomputable def constructionEndpointCoeff (a b c n k : ℕ) : GI :=
  (constructionEndpointPolynomial a b c n).coeff k

noncomputable def constructionPoleShiftPolynomial (a b c n : ℕ) : Polynomial ℤ :=
  taylor (-5) (constructionPolynomialPart a b c n)

noncomputable def constructionPoleShiftCoeff (a b c n k : ℕ) : ℤ :=
  (constructionPoleShiftPolynomial a b c n).coeff k

theorem constructionEndpointPolynomial_natDegree {a b c : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) (n : ℕ) :
    (constructionEndpointPolynomial a b c n).natDegree = constructionDegree a b c * n - 2 := by
  rw [constructionEndpointPolynomial, natDegree_taylor,
    natDegree_map_eq_of_injective (f := Int.castRingHom GI) Int.cast_injective,
    constructionPolynomialPart_natDegree hc hp]

theorem constructionEndpointPolynomial_eval (a b c n : ℕ) (t : ℂ) :
    (constructionEndpointPolynomial a b c n).eval₂ GaussianInt.toComplex
      (t - (lowerEndpointGI : ℂ)) = aeval t (constructionPolynomialPart a b c n) := by
  unfold constructionEndpointPolynomial
  rw [taylor_apply, eval₂_comp]
  simp only [eval₂_add, eval₂_X, eval₂_C, sub_add_cancel]
  rw [eval₂_map]
  have hmap : GaussianInt.toComplex.comp (Int.castRingHom GI) = algebraMap ℤ ℂ :=
    Subsingleton.elim _ _
  rw [hmap]
  rfl

theorem constructionPolynomial_endpoint_expansion {a b c n : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) (hn : 0 < n) (t : ℂ) :
    aeval t (constructionPolynomialPart a b c n) =
      ∑ k ∈ Finset.range (constructionDegree a b c * n - 1),
        (constructionEndpointCoeff a b c n k : ℂ) * (t - (-1 - 2 * Complex.I)) ^ k := by
  have hD := (construction_integer_margins hc hp).2.2.2.2.2.2
  have hDn : 2 ≤ constructionDegree a b c * n := by
    have := Nat.mul_le_mul_left (constructionDegree a b c) hn
    omega
  rw [← constructionEndpointPolynomial_eval, eval₂_eq_sum_range,
    constructionEndpointPolynomial_natDegree hc hp,
    show constructionDegree a b c * n - 2 + 1 = constructionDegree a b c * n - 1 by omega,
    lowerEndpointGI_cast]
  rfl

theorem constructionPolynomial_endpoint_integral {a b c n : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) (hn : 0 < n) :
    -(∫ s : ℝ in (-2)..2, aeval (verticalSegment s) (constructionPolynomialPart a b c n)) =
      Complex.I * ∑ k ∈ Finset.range (constructionDegree a b c * n - 1),
        (constructionEndpointCoeff a b c n k : ℂ) * (4 * Complex.I) ^ (k + 1) / (k + 1 : ℂ) := by
  simp_rw [constructionPolynomial_endpoint_expansion hc hp hn]
  rw [intervalIntegral.integral_finsetSum]
  · rw [← Finset.sum_neg_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_const_mul, neg_mul_eq_mul_neg, endpointMonomial_integral]
    ring
  · intro k _
    exact (continuous_const.mul
      ((verticalSegment_continuous.sub continuous_const).pow k)).intervalIntegrable _ _

theorem constructionEndpointCoeff_deriv {a b c n : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) (hn : 0 < n)
    (k : ℕ) (hk : k < constructionDegree a b c * n - 1) :
    normalizedComplexDeriv k (fun t : ℂ => aeval t (constructionPolynomialPart a b c n))
      (-1 - 2 * Complex.I) = (constructionEndpointCoeff a b c n k : ℂ) := by
  have hfun := funext (constructionPolynomial_endpoint_expansion hc hp hn)
  rw [hfun, normalizedComplexDeriv_sum _ _ _ _ (by intros; fun_prop)]
  simp_rw [normalizedComplexDeriv_const_mul, normalizedComplexDeriv_shift_power]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hik
    simp [Ne.symm hik]
  · intro h
    exact (h (Finset.mem_range.mpr hk)).elim

theorem constructionPolynomial_pole_expansion {a b c n : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) (hn : 0 < n) (t : ℂ) :
    aeval t (constructionPolynomialPart a b c n) =
      ∑ q ∈ Finset.range (constructionDegree a b c * n - 1),
        (constructionPoleShiftCoeff a b c n q : ℂ) * (t + 5) ^ q := by
  have heval : aeval (t + 5) (constructionPoleShiftPolynomial a b c n) =
      aeval t (constructionPolynomialPart a b c n) := by
    simp [constructionPoleShiftPolynomial, taylor_apply, aeval_comp, map_ofNat]
  have hD := (construction_integer_margins hc hp).2.2.2.2.2.2
  have hDn : 2 ≤ constructionDegree a b c * n := by
    have := Nat.mul_le_mul_left (constructionDegree a b c) hn
    omega
  rw [← heval, aeval_def, eval₂_eq_sum_range, constructionPoleShiftPolynomial,
    natDegree_taylor, constructionPolynomialPart_natDegree hc hp,
    show constructionDegree a b c * n - 2 + 1 = constructionDegree a b c * n - 1 by omega]
  rfl

end PiIrrationality
