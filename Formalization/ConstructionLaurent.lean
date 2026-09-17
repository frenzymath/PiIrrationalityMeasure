import Formalization.EvenPoleResidue
import Formalization.ConstructionCoefficientGrowth

/-! The actual complete Laurent coefficients and polynomial part for arbitrary triples. -/

namespace PiIrrationality

open Polynomial

noncomputable def constructionNumeratorY (a b n : ℕ) : Polynomial ℤ :=
  C 5 * X ^ (a * n) * (X ^ 2 + C 6 * X + C 25) ^ (b * n)

noncomputable def constructionRegularized (a b c n : ℕ) : ℝ → ℝ :=
  EvenPole.regularized (constructionNumeratorY a b n) (c * n + 1)

noncomputable def constructionLaurentCoeff (a b c n : ℕ) (j : ℤ) : ℚ :=
  EvenPole.laurentCoeff (constructionNumeratorY a b n) (c * n + 1) j

noncomputable def constructionPolynomialPart (a b c n : ℕ) : Polynomial ℤ :=
  EvenPole.part (constructionNumeratorY a b n) (c * n + 1)

theorem constructionNumeratorY_aeval {K : Type*} [CommRing K] [Algebra ℤ K]
    (a b n : ℕ) (t : K) :
    aeval (t ^ 2) (constructionNumeratorY a b n) =
      5 * t ^ (2 * a * n) * (t ^ 4 + 6 * t ^ 2 + 25) ^ (b * n) := by
  simp only [constructionNumeratorY, map_mul, map_add, map_pow, aeval_C, aeval_X,
    map_ofNat, ← pow_mul, Nat.reduceMul, Nat.mul_assoc]

theorem constructionEvenPole_density {K : Type*} [Field K] [Algebra ℚ K]
    (a b c n : ℕ) (t : K) :
    EvenPole.density (constructionNumeratorY a b n) (c * n + 1) t =
      5 * t ^ (2 * a * n) * (t ^ 4 + 6 * t ^ 2 + 25) ^ (b * n) /
        (25 - t ^ 2) ^ (c * n + 1) := by
  rw [EvenPole.density, EvenPole.numerator_aeval, constructionNumeratorY_aeval]

theorem constructionRegularized_formula (a b c n : ℕ) (t : ℝ) :
    constructionRegularized a b c n t =
      5 * t ^ (2 * a * n) * (t ^ 4 + 6 * t ^ 2 + 25) ^ (b * n) /
        (5 - t) ^ (c * n + 1) := by
  rw [constructionRegularized, EvenPole.regularized, EvenPole.numerator_aeval,
    constructionNumeratorY_aeval]

theorem constructionLaurentCoeff_cast (a b c n : ℕ) (j : ℤ) (hj : j ≤ c * (n : ℤ)) :
    (constructionLaurentCoeff a b c n j : ℝ) =
      normalizedDeriv (c * (n : ℤ) - j).toNat (constructionRegularized a b c n) (-5) := by
  rw [constructionLaurentCoeff, EvenPole.laurentCoeff_cast _ (by omega) (by push_cast; omega)]
  congr 1
  push_cast
  ring

theorem constructionLaurentCoeff_zero_of_outside (a b c n : ℕ) (j : ℤ)
    (hj : c * (n : ℤ) < j) : constructionLaurentCoeff a b c n j = 0 := by
  unfold constructionLaurentCoeff EvenPole.laurentCoeff
  rw [if_neg (by push_cast; omega)]

theorem constructionLaurentCoeff_candidate (n : ℕ) (j : ℤ) :
    constructionLaurentCoeff 1857 3714 5570 n j = laurentCoeffRat n j := by
  apply Rat.cast_injective (α := ℝ)
  rw [laurentCoeffRat_cast]
  by_cases hj : j ≤ 5570 * (n : ℤ)
  · rw [constructionLaurentCoeff_cast _ _ _ _ _ hj, laurentCoeff_eq_normalizedDeriv n j hj]
    congr 1
    ext t
    exact constructionRegularized_formula 1857 3714 5570 n t
  · rw [constructionLaurentCoeff_zero_of_outside _ _ _ _ _ (lt_of_not_ge hj),
      laurentCoeff_zero_of_outside n j (lt_of_not_ge hj)]
    norm_num

theorem construction_partialFractions {K : Type*} [Field K] [Algebra ℚ K]
    (a b c n : ℕ) (t : K) (hp : t + 5 ≠ 0) (hm : t - 5 ≠ 0) :
    5 * t ^ (2 * a * n) * (t ^ 4 + 6 * t ^ 2 + 25) ^ (b * n) /
        (25 - t ^ 2) ^ (c * n + 1) =
      aeval t (constructionPolynomialPart a b c n) +
        ∑ j : Fin (c * n + 1), (constructionLaurentCoeff a b c n j.val : K) *
          (1 / (5 + t) ^ (j.val + 1) + 1 / (5 - t) ^ (j.val + 1)) := by
  rw [← constructionEvenPole_density]
  exact EvenPole.partialFractions (constructionNumeratorY a b n) (by omega) t hp hm

local instance : CharZero (LaurentSeries ℚ) := algebraRat.charZero _
noncomputable local instance : Algebra ℚ (LaurentSeries ℚ) := HahnSeries.powerSeriesAlgebra ℤ ℚ

noncomputable def constructionMobiusDensity (a b c n : ℕ) : LaurentSeries ℚ :=
  (5 * mobiusLaurent ^ (2 * a * n) *
    (mobiusLaurent ^ 4 + 6 * mobiusLaurent ^ 2 + 25) ^ (b * n) /
      (25 - mobiusLaurent ^ 2) ^ (c * n + 1)) * laurentDerivation ℚ mobiusLaurent

theorem constructionMobiusDensity_residue (a b c n : ℕ) :
    laurentResidue (constructionMobiusDensity a b c n) = constructionLaurentCoeff a b c n 0 := by
  unfold constructionMobiusDensity
  rw [← constructionEvenPole_density]
  exact EvenPole.mobius_residue (constructionNumeratorY a b n) (by omega)

end PiIrrationality
