import Formalization.ConstructionPolynomialData
import Formalization.ConstructionScaledLaurent
import Formalization.PolynomialLaurent

/-! The actual negative Laurent coefficient representation (2.29) for general triples. -/

namespace PiIrrationality

open Polynomial

theorem construction_otherPole_lowIndex_eq_sum (a b c n : ℕ) (t : ℝ) (ht : t ≠ 5) :
    (∑ i : Fin (c * n + 1),
      (((-1 : ℚ) ^ (i.val + (c * n + 1)) *
          constructionLaurentCoeff a b c n (c * (n : ℤ) - i.val) : ℚ) : ℝ) * (t - 5) ^ i.val) /
        (t - 5) ^ (c * n + 1) =
      ∑ j : Fin (c * n + 1), (constructionLaurentCoeff a b c n (j.val : ℤ) : ℝ) *
        (1 / (5 - t) ^ (j.val + 1)) := by
  rw [Finset.sum_div]
  have hterm (i : Fin (c * n + 1)) :
      ((((-1 : ℚ) ^ (i.val + (c * n + 1)) *
          constructionLaurentCoeff a b c n (c * (n : ℤ) - i.val) : ℚ) : ℝ) * (t - 5) ^ i.val) /
        (t - 5) ^ (c * n + 1) =
      (constructionLaurentCoeff a b c n (c * (n : ℤ) - i.val) : ℝ) /
        (5 - t) ^ (c * n + 1 - i.val) := by
    have hsign : (-1 : ℝ) ^ (i.val + (c * n + 1)) =
        (-1 : ℝ) ^ (c * n + 1 - i.val) := by
      rw [show i.val + (c * n + 1) = (c * n + 1 - i.val) + 2 * i.val by
        have := i.isLt; omega, pow_add, pow_mul]
      norm_num
    push_cast
    rw [show 5 - t = -(t - 5) by ring, div_neg_power, ← hsign]
    have hpow : (t - 5) ^ (c * n + 1) =
        (t - 5) ^ (c * n + 1 - i.val) * (t - 5) ^ i.val := by
      rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt i.isLt)]
    rw [hpow]
    have hne := sub_ne_zero.mpr ht
    field_simp
  simp_rw [hterm]
  rw [← Equiv.sum_comp Fin.revPerm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.revPerm_apply]
  have hindex : c * (n : ℤ) - (j.rev.val : ℤ) = (j.val : ℤ) := by
    simp only [Fin.val_rev]
    have := j.isLt
    omega
  have hpower : c * n + 1 - j.rev.val = j.val + 1 := by
    rw [Fin.val_rev]
    have := j.isLt
    omega
  rw [hindex, hpower]
  ring

theorem construction_regularized_remainder_identity (a b c n : ℕ) (t : ℝ) (ht : t ≠ 5) :
    constructionRegularized a b c n t =
      (∑ i : Fin (c * n + 1),
        (constructionLaurentCoeff a b c n (c * (n : ℤ) - i.val) : ℝ) * (t + 5) ^ i.val) +
      (t + 5) ^ (c * n + 1) *
        (aeval t (constructionPolynomialPart a b c n) +
          ∑ j : Fin (c * n + 1), (constructionLaurentCoeff a b c n (j.val : ℤ) : ℝ) *
            (1 / (5 - t) ^ (j.val + 1))) := by
  have hlocal (i : Fin (c * n + 1)) :
      EvenPole.localCoeff (constructionNumeratorY a b n) (c * n + 1) i.val =
        constructionLaurentCoeff a b c n (c * (n : ℤ) - i.val) := by
    unfold constructionLaurentCoeff EvenPole.laurentCoeff
    rw [if_pos (by have := i.isLt; push_cast; omega)]
    congr 1
    have := i.isLt
    push_cast
    omega
  have h := EvenPole.regularized_eq_of_decomposition
    (EvenPole.actual_decomposition (constructionNumeratorY a b n) (by omega : 0 < c * n + 1))
    t ht
  simp_rw [hlocal] at h
  rw [construction_otherPole_lowIndex_eq_sum a b c n t ht] at h
  exact h

theorem constructionPoleShiftCoeff_deriv (a b c n q : ℕ) :
    normalizedDeriv q (fun t : ℝ => aeval t (constructionPolynomialPart a b c n)) (-5) =
      (constructionPoleShiftCoeff a b c n q : ℝ) := by
  rw [constructionPoleShiftCoeff, constructionPoleShiftPolynomial, taylor_coeff]
  simpa only [Int.cast_neg, Int.cast_ofNat] using
    normalizedDeriv_int_polynomial q (constructionPolynomialPart a b c n) (-5)

theorem constructionPoleShiftCoeff_laurent_formula (a b c n q : ℕ) :
    (constructionPoleShiftCoeff a b c n q : ℚ) = constructionLaurentCoeff a b c n (-((q + 1 : ℕ) : ℤ)) -
      ∑ j : Fin (c * n + 1), ((j.val + q).choose q : ℚ) *
        constructionLaurentCoeff a b c n (j.val : ℤ) / 10 ^ (j.val + q + 1) := by
  let m := c * n + 1
  let A (t : ℝ) := ∑ i : Fin m,
    (constructionLaurentCoeff a b c n (c * (n : ℤ) - i.val) : ℝ) * (t + 5) ^ i.val
  let S (t : ℝ) := ∑ j : Fin m, (constructionLaurentCoeff a b c n (j.val : ℤ) : ℝ) *
    (1 / (5 - t) ^ (j.val + 1))
  let f (t : ℝ) := aeval t (constructionPolynomialPart a b c n) + S t
  have hP : ContDiffAt ℝ (m + q) (fun t : ℝ => aeval t (constructionPolynomialPart a b c n)) (-5) :=
    ((constructionPolynomialPart a b c n).contDiff_aeval (m + q)).contDiffAt
  have hS : ContDiffAt ℝ (m + q) S (-5) := by
    dsimp [S]
    fun_prop (disch := norm_num)
  have hf : ContDiffAt ℝ (m + q) f (-5) := hP.add hS
  have hA : ContDiffAt ℝ (m + q) A (-5) := by dsimp [A]; fun_prop
  have hg : ContDiffAt ℝ (m + q) (fun t : ℝ => (t + 5) ^ m * f t) (-5) :=
    (by fun_prop : ContDiffAt ℝ (m + q) (fun t : ℝ => (t + 5) ^ m) (-5)).mul hf
  have heq : constructionRegularized a b c n =ᶠ[nhds (-5 : ℝ)]
      (fun t => A t + (t + 5) ^ m * f t) := by
    filter_upwards [eventually_ne_nhds (by norm_num : (-5 : ℝ) ≠ 5)] with t ht
    exact construction_regularized_remainder_identity a b c n t ht
  have hd := congrArg (fun x : ℝ => x / ((m + q).factorial : ℝ))
    (heq.iteratedDeriv_eq (m + q))
  change normalizedDeriv (m + q) (constructionRegularized a b c n) (-5) =
    normalizedDeriv (m + q) (fun t => A t + (t + 5) ^ m * f t) (-5) at hd
  have hsplit : normalizedDeriv (m + q) (fun t => A t + (t + 5) ^ m * f t) (-5) =
      normalizedDeriv (m + q) A (-5) + normalizedDeriv q f (-5) := by
    unfold normalizedDeriv
    rw [iteratedDeriv_fun_add hA hg, add_div]
    exact congrArg (fun z : ℝ => iteratedDeriv (m + q) A (-5) / (m + q).factorial + z)
      (normalizedDeriv_shift_power_mul m q f hf)
  have hAzero : normalizedDeriv (m + q) A (-5) = 0 := by
    unfold normalizedDeriv
    dsimp only [A]
    rw [iteratedDeriv_fun_sum (by intros; fun_prop), Finset.sum_div]
    change (∑ i : Fin m, normalizedDeriv (m + q)
      (fun t : ℝ => (constructionLaurentCoeff a b c n (c * (n : ℤ) - i.val) : ℝ) *
        (t + 5) ^ i.val) (-5)) = 0
    simp_rw [normalizedDeriv_const_mul, normalizedDeriv_shift_power]
    apply Finset.sum_eq_zero
    intro i _
    have := i.isLt
    simp [show i.val ≠ m + q by omega]
  have hD : normalizedDeriv q f (-5) = (constructionPoleShiftCoeff a b c n q : ℝ) +
      ∑ j : Fin m, ((j.val + q).choose q : ℝ) *
        (constructionLaurentCoeff a b c n (j.val : ℤ) : ℝ) / 10 ^ (j.val + q + 1) := by
    have hPq : ContDiffAt ℝ q (fun t : ℝ => aeval t (constructionPolynomialPart a b c n)) (-5) :=
      hP.of_le (by exact_mod_cast (show q ≤ m + q by omega))
    have hSq : ContDiffAt ℝ q S (-5) :=
      hS.of_le (by exact_mod_cast (show q ≤ m + q by omega))
    have hsplit' : normalizedDeriv q f (-5) =
        normalizedDeriv q (fun t : ℝ => aeval t (constructionPolynomialPart a b c n)) (-5) +
          normalizedDeriv q S (-5) := by
      unfold normalizedDeriv
      dsimp only [f]
      rw [iteratedDeriv_fun_add hPq hSq, add_div]
    rw [hsplit', constructionPoleShiftCoeff_deriv]
    congr 1
    unfold normalizedDeriv
    dsimp only [S]
    rw [iteratedDeriv_fun_sum (by intros; fun_prop (disch := norm_num)), Finset.sum_div]
    change (∑ j : Fin m, normalizedDeriv q
      (fun t : ℝ => (constructionLaurentCoeff a b c n (j.val : ℤ) : ℝ) *
        (1 / (5 - t) ^ (j.val + 1))) (-5)) = _
    simp_rw [normalizedDeriv_const_mul, normalizedDeriv_inv_linear_choose]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsplit, hAzero, zero_add, hD] at hd
  have hc := constructionLaurentCoeff_cast a b c n (-((q + 1 : ℕ) : ℤ))
    (by have := mul_nonneg (Int.natCast_nonneg c) (Int.natCast_nonneg n); push_cast; omega)
  have horder : (c * (n : ℤ) - (-((q + 1 : ℕ) : ℤ))).toNat = m + q := by
    dsimp [m]
    push_cast
    omega
  rw [horder] at hc
  push_cast at hc
  apply Rat.cast_injective (α := ℝ)
  push_cast
  rw [hc]
  dsimp only [m] at hd
  linear_combination -hd

end PiIrrationality
