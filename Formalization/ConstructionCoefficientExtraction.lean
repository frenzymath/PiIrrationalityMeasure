import Formalization.ConstructionLaurent
import Formalization.ConstructionMobiusAlgebra

/-! Exact extraction (6.66) and growth of the actual general Laurent coefficient. -/

namespace PiIrrationality

open HahnSeries PowerSeries Filter
open scoped Topology

local instance : CharZero (LaurentSeries ℚ) := algebraRat.charZero _

private theorem general_density_power_factor {K : Type*} [Field K]
    (a b c n : ℕ) (t q A dt : K) (hA : A ≠ 0) :
    (5 * t ^ (2 * a * n) * q ^ (b * n) / A ^ (c * n + 1)) * dt =
      (5 * dt / A) * (t ^ (2 * a) * q ^ b / A ^ c) ^ n := by
  rw [pow_succ A (c * n)]
  simp only [pow_mul, mul_pow, div_pow]
  field_simp

theorem constructionMobiusDensity_series (a b c n : ℕ) (hc : Even c)
    (hab : c ≤ a + b) (hbc : 2 * c ≤ 4 * b) :
    constructionMobiusDensity a b c n =
      single (-((c * n + 1 : ℕ) : ℤ)) (constructionCoefficientScale a b c ^ n / 2) *
        ((constructionSeries a b c ^ n : PowerSeries ℚ) : LaurentSeries ℚ) := by
  rw [constructionMobiusDensity,
    general_density_power_factor a b c n _ _ _ _ mobiusLaurent_denominator_ne_zero,
    mobiusLaurent_prefactor, constructionMobius_base_formula a b c hc hab hbc,
    laurent_single_div_X_pow, PowerSeries.coe_pow]
  push_cast
  simp only [mul_pow, div_pow, ← pow_mul]
  rw [pow_succ (single 1 (1 : ℚ) : LaurentSeries ℚ) (c * n)]
  field_simp [laurentX_ne_zero]

theorem constructionLaurentCoeff_zero_eq_series (a b c n : ℕ) (hc : Even c)
    (hab : c ≤ a + b) (hbc : 2 * c ≤ 4 * b) :
    constructionLaurentCoeff a b c n 0 = constructionCoefficientScale a b c ^ n / 2 *
      coeff (c * n) (constructionSeries a b c ^ n) := by
  have h := constructionMobiusDensity_residue a b c n
  rw [constructionMobiusDensity_series a b c n hc hab hbc] at h
  change (single _ _ * ((constructionSeries a b c ^ n : PowerSeries ℚ) :
    LaurentSeries ℚ)).coeff (-1) = _ at h
  rw [coeff_single_mul] at h
  have hi : -1 - (-((c * n + 1 : ℕ) : ℤ)) = ((c * n : ℕ) : ℤ) := by omega
  rw [hi, LaurentSeries.coeff_coe_powerSeries] at h
  exact h.symm

theorem constructionLaurentCoeff_zero_pos {a b c : ℕ} (hc : 0 < c) (hce : Even c)
    (hp : Admissible (constructionParameter a b c)) (n : ℕ) :
    0 < constructionLaurentCoeff a b c n 0 := by
  have hh := construction_admissible_inequalities hc hp
  rw [constructionLaurentCoeff_zero_eq_series a b c n hce hh.1.le (by omega)]
  exact mul_pos (div_pos (pow_pos (constructionCoefficientScale_pos a b c) n) (by norm_num))
    (PositivePower.series_diagonal_coeff_pos (2 * a) b (constructionDegree_pos hc hp) c n)

theorem construction_pi_coeff_extraction {a b c : ℕ} (hc : 0 < c) (hce : Even c)
    (hp : Admissible (constructionParameter a b c)) (n : ℕ) :
    |-constructionLaurentCoeff a b c n 0 / 2| = constructionCoefficientExpression a b c n := by
  have hh := construction_admissible_inequalities hc hp
  rw [abs_div, abs_neg, abs_of_pos (constructionLaurentCoeff_zero_pos hc hce hp n),
    constructionLaurentCoeff_zero_eq_series a b c n hce hh.1.le (by omega)]
  norm_num only [abs_of_pos (by norm_num : (0 : ℚ) < 2)]
  unfold constructionCoefficientExpression
  ring

theorem construction_pi_coeff_growth_near_candidate : ∀ᶠ p in 𝓝 candidate,
    ∀ a b c : ℕ, 0 < c → Even c → constructionParameter a b c = p →
      (∀ n : ℕ, constructionLaurentCoeff a b c n 0 ≠ 0) ∧
      Tendsto (fun n : ℕ => Real.log |(↑(-constructionLaurentCoeff a b c n 0 / 2) : ℝ)| /
        ((c : ℝ) * n)) atTop (𝓝 (parameterCoefficientRate p)) := by
  filter_upwards [construction_coefficient_saddle_near_candidate,
    constructionCoefficient_growth_near_candidate] with p hp hg
  intro a b c hc hce he
  have ha : Admissible (constructionParameter a b c) := he ▸ (hp a b c hc he).1
  refine ⟨fun n => (constructionLaurentCoeff_zero_pos hc hce ha n).ne', ?_⟩
  have h := (hg a b c hc he).2
  have hEq (n : ℕ) : |(↑(-constructionLaurentCoeff a b c n 0 / 2) : ℝ)| =
      (constructionCoefficientExpression a b c n : ℝ) := by
    exact_mod_cast construction_pi_coeff_extraction hc hce ha n
  simpa only [hEq] using h

end PiIrrationality
