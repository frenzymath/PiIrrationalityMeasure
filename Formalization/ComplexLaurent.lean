import Formalization.ComplexLeibniz
import Formalization.ConstructionLaurent

/-! The rational Laurent coefficients agree with complex normalized derivatives. -/

namespace PiIrrationality

theorem normalizedComplexDeriv_rat_aeval (k : ℕ) (P : Polynomial ℚ) (x : ℚ) :
    normalizedComplexDeriv k (fun t : ℂ => Polynomial.aeval t P) (x : ℂ) =
      (((Polynomial.derivative^[k]) P).eval x / (k.factorial : ℚ) : ℚ) := by
  have hd : iteratedDeriv k (fun t : ℂ => Polynomial.aeval t P) =
      fun t : ℂ => Polynomial.aeval t ((Polynomial.derivative^[k]) P) := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [iteratedDeriv_succ, ih]
        funext t
        simp only [Polynomial.deriv_aeval, Function.iterate_succ_apply']
  unfold normalizedComplexDeriv
  rw [hd]
  have he := Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval
    (A := ℂ) x ((Polynomial.derivative^[k]) P)
  change Polynomial.aeval (x : ℂ) ((Polynomial.derivative^[k]) P) =
    ((((Polynomial.derivative^[k]) P).eval x : ℚ) : ℂ) at he
  dsimp only
  rw [he]
  push_cast
  rfl

theorem normalizedDeriv_rat_aeval_complex (k : ℕ) (P : Polynomial ℚ) (x : ℚ) :
    (normalizedDeriv k (fun t : ℝ => Polynomial.aeval t P) (x : ℝ) : ℂ) =
      normalizedComplexDeriv k (fun t : ℂ => Polynomial.aeval t P) (x : ℂ) := by
  rw [normalizedDeriv_rat_aeval, normalizedComplexDeriv_rat_aeval]
  norm_cast

theorem normalizedDeriv_inv_linear_complex (M k : ℕ) (x : ℝ) :
    (normalizedDeriv k (fun t : ℝ => (5 - t) ^ (-M : ℤ)) x : ℂ) =
      normalizedComplexDeriv k (fun t : ℂ => (5 - t) ^ (-M : ℤ)) (x : ℂ) := by
  rw [normalized_inv_linear_deriv]
  unfold normalizedComplexDeriv
  rw [iteratedDeriv_comp_const_sub k (fun z : ℂ => z ^ (-M : ℤ)) 5]
  simp only [smul_eq_mul, iteratedDeriv_eq_iterate, iter_deriv_zpow]
  push_cast
  ring

namespace EvenPole

noncomputable def complexRegularized (F : Polynomial ℤ) (m : ℕ) (z : ℂ) : ℂ :=
  Polynomial.aeval z (numerator F) / (5 - z) ^ m

theorem localCoeff_complex (F : Polynomial ℤ) (m k : ℕ) :
    (localCoeff F m k : ℂ) =
      normalizedComplexDeriv k (complexRegularized F m) (-5) := by
  have hreal := localCoeff_cast F m k
  have hcast := congrArg (fun y : ℝ => (y : ℂ)) hreal
  simp only [Complex.ofReal_ratCast] at hcast
  rw [hcast]
  have hr : regularized F m = fun t : ℝ =>
      Polynomial.aeval t (numerator F) * (5 - t) ^ (-m : ℤ) := by
    ext t
    simp only [regularized, zpow_neg, zpow_natCast, div_eq_mul_inv]
  have hc : complexRegularized F m = fun t : ℂ =>
      Polynomial.aeval t (numerator F) * (5 - t) ^ (-m : ℤ) := by
    ext t
    simp only [complexRegularized, zpow_neg, zpow_natCast, div_eq_mul_inv]
  rw [hr, hc, normalizedDeriv_mul ((numerator F).contDiff_aeval k).contDiffAt
      (by simp only [zpow_neg, zpow_natCast]; fun_prop (disch := norm_num)),
    normalizedComplexDeriv_mul ((numerator F).contDiff_aeval k).contDiffAt
      (by simp only [zpow_neg, zpow_natCast]; fun_prop (disch := norm_num))]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  have hp := normalizedDeriv_rat_aeval_complex i (numerator F) (-5)
  norm_num only [Rat.cast_neg, Rat.cast_ofNat] at hp
  rw [hp, normalizedDeriv_inv_linear_complex]
  norm_num

end EvenPole

theorem constructionLaurentCoeff_complex (a b c n : ℕ) (j : ℤ)
    (hj : j ≤ c * (n : ℤ)) :
    (constructionLaurentCoeff a b c n j : ℂ) =
      normalizedComplexDeriv (c * (n : ℤ) - j).toNat
        (EvenPole.complexRegularized (constructionNumeratorY a b n) (c * n + 1))
        (-5) := by
  rw [constructionLaurentCoeff, EvenPole.laurentCoeff,
    if_pos (by push_cast; omega), EvenPole.localCoeff_complex]
  congr 1
  push_cast
  ring

end PiIrrationality
