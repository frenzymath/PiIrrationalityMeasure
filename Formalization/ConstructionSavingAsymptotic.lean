import Formalization.ConstructionGridIntervals
import Formalization.ConstructionDenominatorGrowth
import Formalization.ParameterSavingSeries

/-! Unconditional prime-saving and normalization rates for admissible integer triples. -/

namespace PiIrrationality

open Filter MeasureTheory Set
open scoped Topology

theorem construction_periodic_series_eq_savingOmega {a b c : ℕ}
    (hq : 0 ≤ (a : ℝ) + 2 * b - c) (E : PeriodicPrimeIntervals)
    (hregion : E.region = constructionSavingSet a b c) :
    E.series = savingOmega a b c := by
  symm
  apply periodic_saving_integral_eq_series
    (fun u => savingChi ((a : ℝ) * u) ((b : ℝ) * u) ((c : ℝ) * u))
    E.indices E.left E.right
  · intro k u
    simpa only [Int.cast_natCast] using savingChi_integer_periodic a b c k u
  · exact savingDensity_integrableOn (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) hq
  · exact E.bounds
  · exact E.disjoint
  · intro u hu
    change savingChi _ _ _ = E.region.indicator (fun _ => (1 : ℝ)) u
    rw [hregion]
    have hm : u ∈ constructionSavingSet a b c ↔ constructionSavingCondition a b c u := by
      simp only [constructionSavingSet, mem_setOf_eq, hu.1, hu.2, true_and]
    classical
    simp only [savingChi, Set.indicator, hm, constructionSavingCondition]

theorem constructionPhi_log_limit {a b c : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) :
    Tendsto (fun n : ℕ => Real.log (constructionPhi a b c n : ℝ) / (n : ℝ))
      atTop (𝓝 ((c : ℝ) * savingPhi (constructionParameter a b c))) := by
  obtain ⟨E, hregion⟩ := constructionSavingSet_exists_periodic_intervals hc hp
  have hseries := construction_periodic_series_eq_savingOmega
    (construction_grid_positive hc hp).2.2.le E hregion
  rw [constructionSavingOmega_eq_phi a b c hc] at hseries
  rw [← hseries]
  exact constructionPhi_log_limit_of_periodic_intervals hc hp E hregion
    (construction_periodic_intervals_left_bound hc hp E hregion)

theorem constructionReducedLcm_log_limit {a b c : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) :
    Tendsto (fun n : ℕ => Real.log (constructionReducedLcm a b c n : ℝ) / (n : ℝ))
      atTop (𝓝 ((constructionDegree a b c : ℝ) -
        (c : ℝ) * savingPhi (constructionParameter a b c))) := by
  obtain ⟨E, hregion⟩ := constructionSavingSet_exists_periodic_intervals hc hp
  have hseries := construction_periodic_series_eq_savingOmega
    (construction_grid_positive hc hp).2.2.le E hregion
  rw [constructionSavingOmega_eq_phi a b c hc] at hseries
  rw [← hseries]
  exact constructionReducedLcm_log_limit_of_periodic_intervals hc hp E hregion
    (construction_periodic_intervals_left_bound hc hp E hregion)

theorem constructionNormalizationMultiplier_log_limit {a b c : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) :
    Tendsto
      (fun n : ℕ => Real.log (constructionNormalizationMultiplier a b c n : ℝ) / (n : ℝ))
      atTop (𝓝 ((constructionDegree a b c : ℝ) -
        (constructionTwoSaving b c : ℝ) * Real.log 2 -
        (c : ℝ) * savingPhi (constructionParameter a b c))) := by
  obtain ⟨E, hregion⟩ := constructionSavingSet_exists_periodic_intervals hc hp
  have hseries := construction_periodic_series_eq_savingOmega
    (construction_grid_positive hc hp).2.2.le E hregion
  rw [constructionSavingOmega_eq_phi a b c hc] at hseries
  rw [← hseries]
  exact constructionNormalizationMultiplier_log_limit_of_periodic_intervals hc he hp E hregion
    (construction_periodic_intervals_left_bound hc hp E hregion)

theorem constructionNormalizationRate_eq_parameterCost {a b c : ℕ}
    (hc : 0 < c) (he : Even c) (hp : Admissible (constructionParameter a b c)) :
    ((constructionDegree a b c : ℝ) - (constructionTwoSaving b c : ℝ) * Real.log 2 -
      (c : ℝ) * savingPhi (constructionParameter a b c)) / (c : ℝ) =
      parameterCost (constructionParameter a b c) := by
  have hm := construction_admissible_inequalities hc hp
  have hdeg := constructionDegree_cast (by omega : 2 * c ≤ 2 * a + 4 * b)
  have htwo := constructionTwoSaving_cast hc he hp
  rw [hdeg, htwo]
  unfold parameterCost parameterSmoothCost
  dsimp [constructionParameter]
  push_cast
  field_simp

theorem constructionNormalizationCost_limit {a b c : ℕ}
    (hc : 0 < c) (he : Even c) (hp : Admissible (constructionParameter a b c)) :
    Tendsto (fun n : ℕ => Real.log (constructionNormalizationMultiplier a b c n : ℝ) /
      ((c : ℝ) * n)) atTop (𝓝 (parameterCost (constructionParameter a b c))) := by
  have h := (constructionNormalizationMultiplier_log_limit hc he hp).div_const (c : ℝ)
  rw [constructionNormalizationRate_eq_parameterCost hc he hp] at h
  simpa only [div_div, mul_comm] using h

end PiIrrationality
