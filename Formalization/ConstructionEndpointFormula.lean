import Formalization.ConstructionPolynomialData
import Formalization.EndpointFormula

/-! The endpoint zero of the actual general density gives formula (2.25). -/

namespace PiIrrationality

open Polynomial

noncomputable def constructionEndpointRegularFactor (a b c n : ℕ) (t : ℂ) : ℂ :=
  5 * t ^ (2 * a * n) * (t - (-1 + 2 * Complex.I)) ^ (b * n) *
    ((t - 1) ^ 2 + 4) ^ (b * n) / (25 - t ^ 2) ^ (c * n + 1)

theorem constructionDensity_endpoint_factor (a b c n : ℕ) (t : ℂ) :
    constructionDensity a b c n t = (t - (-1 - 2 * Complex.I)) ^ (b * n) *
      constructionEndpointRegularFactor a b c n t := by
  have hquad : (t - (-1 - 2 * Complex.I)) * (t - (-1 + 2 * Complex.I)) =
      (t + 1) ^ 2 + 4 := by linear_combination -4 * Complex.I_sq
  have hquartic : t ^ 4 + 6 * t ^ 2 + 25 =
      ((t - (-1 - 2 * Complex.I)) * (t - (-1 + 2 * Complex.I))) *
        ((t - 1) ^ 2 + 4) := by rw [hquad]; ring
  unfold constructionDensity constructionEndpointRegularFactor
  rw [hquartic, mul_pow, mul_pow]
  ring

theorem constructionDensity_endpoint_deriv_zero (a b c n k : ℕ) (hk : k < b * n) :
    normalizedComplexDeriv k (constructionDensity a b c n) (-1 - 2 * Complex.I) = 0 := by
  have hf : ContDiffAt ℂ k (constructionEndpointRegularFactor a b c n)
      (-1 - 2 * Complex.I) := by
    unfold constructionEndpointRegularFactor
    fun_prop (disch := exact pow_ne_zero _ endpoint_denominator_ne_zero)
  have hfun := funext (constructionDensity_endpoint_factor a b c n)
  unfold normalizedComplexDeriv
  rw [hfun, iteratedDeriv_shift_power_mul_zero k _ hk _ _ hf, zero_div]

theorem constructionEndpointCoeff_formula {a b c n : ℕ} (hc : 0 < c)
    (ha : Admissible (constructionParameter a b c)) (hn : 0 < n)
    (k : ℕ) (hk : k < b * n) :
    (constructionEndpointCoeff a b c n k : ℂ) =
      -∑ j : Fin (c * n + 1), ((j.val + k).choose k : ℂ) *
        (constructionLaurentCoeff a b c n (j.val : ℤ) : ℂ) *
          ((-1 : ℂ) ^ k / (4 - 2 * Complex.I) ^ (j.val + k + 1) +
            1 / (6 + 2 * Complex.I) ^ (j.val + k + 1)) := by
  let t0 : ℂ := -1 - 2 * Complex.I
  let f (j : Fin (c * n + 1)) (t : ℂ) :=
    (constructionLaurentCoeff a b c n (j.val : ℤ) : ℂ) *
      (1 / (5 + t) ^ (j.val + 1) + 1 / (5 - t) ^ (j.val + 1))
  have hl (j : ℕ) : ContDiffAt ℂ k (fun t : ℂ => 1 / (5 + t) ^ (j + 1)) t0 := by
    dsimp [t0]
    fun_prop (disch := exact pow_ne_zero _ endpoint_left_pole_ne_zero)
  have hr (j : ℕ) : ContDiffAt ℂ k (fun t : ℂ => 1 / (5 - t) ^ (j + 1)) t0 := by
    dsimp [t0]
    fun_prop (disch := exact pow_ne_zero _ endpoint_right_pole_ne_zero)
  have hf (j : Fin (c * n + 1)) : ContDiffAt ℂ k (f j) t0 :=
    contDiffAt_const.mul ((hl j.val).add (hr j.val))
  have hs : ContDiffAt ℂ k (fun t : ℂ => ∑ j, f j t) t0 :=
    ContDiffAt.sum (fun j _ => hf j)
  have hp : ContDiffAt ℂ k (fun t : ℂ => aeval t (constructionPolynomialPart a b c n)) t0 :=
    ((constructionPolynomialPart a b c n).contDiff_aeval k).contDiffAt
  have heq : constructionDensity a b c n =ᶠ[nhds t0]
      (fun t : ℂ => aeval t (constructionPolynomialPart a b c n) + ∑ j, f j t) := by
    have hm5 : t0 ≠ -5 := by
      intro h
      have := congrArg Complex.re h
      norm_num [t0] at this
    have hp5 : t0 ≠ 5 := by
      intro h
      have := congrArg Complex.re h
      norm_num [t0] at this
    filter_upwards [eventually_ne_nhds hm5, eventually_ne_nhds hp5] with t hm hp'
    exact construction_partialFractions a b c n t
      (by simpa [add_eq_zero_iff_eq_neg] using hm) (sub_ne_zero.mpr hp')
  have hD := (construction_integer_margins hc ha).2.2.2.2.2.1
  have hbnD : b * n < constructionDegree a b c * n := Nat.mul_lt_mul_of_pos_right hD hn
  have hd := congrArg (fun z : ℂ => z / (k.factorial : ℂ)) (heq.iteratedDeriv_eq k)
  change normalizedComplexDeriv k (constructionDensity a b c n) t0 =
    normalizedComplexDeriv k (fun t => aeval t (constructionPolynomialPart a b c n) +
      ∑ j, f j t) t0 at hd
  rw [normalizedComplexDeriv_add k _ _ _ hp hs,
    normalizedComplexDeriv_sum _ _ _ _ (fun j _ => hf j)] at hd
  rw [constructionDensity_endpoint_deriv_zero a b c n k hk,
    constructionEndpointCoeff_deriv hc ha hn k (by omega)] at hd
  have hterm (j : Fin (c * n + 1)) : normalizedComplexDeriv k (f j) t0 =
      ((j.val + k).choose k : ℂ) * (constructionLaurentCoeff a b c n (j.val : ℤ) : ℂ) *
        ((-1 : ℂ) ^ k / (4 - 2 * Complex.I) ^ (j.val + k + 1) +
          1 / (6 + 2 * Complex.I) ^ (j.val + k + 1)) := by
    dsimp only [f]
    rw [normalizedComplexDeriv_const_mul, normalizedComplexDeriv_add k _ _ _ (hl _) (hr _),
      normalizedComplexDeriv_inv_add, normalizedComplexDeriv_inv_sub]
    have hleft : 5 + t0 = 4 - 2 * Complex.I := by dsimp [t0]; ring
    have hright : 5 - t0 = 6 + 2 * Complex.I := by dsimp [t0]; ring
    rw [hleft, hright]
    ring
  simp_rw [hterm] at hd
  linear_combination -hd

end PiIrrationality
