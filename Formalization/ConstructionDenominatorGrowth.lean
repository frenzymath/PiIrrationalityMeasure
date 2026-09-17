import Formalization.ConstructionPrimeProduct
import Formalization.DenominatorGrowth
import Formalization.ConstructionNormalizedCoefficient

/-! General reduced-LCM and normalization growth under a finite saving partition. -/

namespace PiIrrationality

open Filter
open scoped Topology

theorem constructionReducedLcm_log_formula (a b c n : ℕ) :
    Real.log (constructionReducedLcm a b c n : ℝ) =
      Real.log (lcmRange (constructionDegree a b c * n) : ℝ) -
        Real.log (constructionPhi a b c n : ℝ) := by
  have hL : (lcmRange (constructionDegree a b c * n) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.lcmUpto_ne_zero _)
  have hPhi : (constructionPhi a b c n : ℝ) ≠ 0 := by
    exact_mod_cast (constructionPhi_pos a b c n).ne'
  simp only [constructionReducedLcm, Rat.cast_div, Rat.cast_natCast]
  exact Real.log_div hL hPhi

theorem constructionReducedLcm_log_limit_of_periodic_intervals
    {a b c : ℕ} (hc : 0 < c) (hp : Admissible (constructionParameter a b c))
    (E : PeriodicPrimeIntervals)
    (hregion : E.region = constructionSavingSet a b c)
    (hleft : ∀ j ∈ E.indices,
      1 / (constructionDegree a b c : ℝ) < E.left j) :
    Tendsto (fun n : ℕ => Real.log (constructionReducedLcm a b c n : ℝ) / (n : ℝ))
      atTop (𝓝 ((constructionDegree a b c : ℝ) - E.series)) := by
  have hdeg := constructionDegree_pos hc hp
  have hlcm := lcmRange_log_mul_limit (constructionDegree a b c) hdeg
  have hphi := constructionPhi_log_limit_of_periodic_intervals hc hp E hregion hleft
  have hsub := hlcm.sub hphi
  apply hsub.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [constructionReducedLcm_log_formula]
  simp only [sub_div]

theorem constructionNormalizationMultiplier_log_formula (a b c n : ℕ) :
    Real.log (constructionNormalizationMultiplier a b c n : ℝ) =
      (4 - (constructionTwoSaving b c : ℝ) * (n : ℝ)) * Real.log 2 +
        Real.log (constructionReducedLcm a b c n : ℝ) := by
  have hpow : (0 : ℝ) < 2 := by norm_num
  have hred := constructionReducedLcm_pos a b c n
  unfold constructionNormalizationMultiplier
  simp only [Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat]
  have hred' : (constructionReducedLcm a b c n : ℝ) ≠ 0 := by exact_mod_cast hred.ne'
  rw [Real.log_mul (zpow_pos hpow _).ne' hred', Real.log_zpow]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]

theorem constructionNormalizationMultiplier_log_limit_of_periodic_intervals
    {a b c : ℕ} (hc : 0 < c) (he : Even c)
    (hp : Admissible (constructionParameter a b c))
    (E : PeriodicPrimeIntervals)
    (hregion : E.region = constructionSavingSet a b c)
    (hleft : ∀ j ∈ E.indices,
      1 / (constructionDegree a b c : ℝ) < E.left j) :
    Tendsto
      (fun n : ℕ => Real.log (constructionNormalizationMultiplier a b c n : ℝ) / (n : ℝ))
      atTop (𝓝 ((constructionDegree a b c : ℝ) -
        (constructionTwoSaving b c : ℝ) * Real.log 2 - E.series)) := by
  have hred := constructionReducedLcm_log_limit_of_periodic_intervals hc hp E hregion hleft
  have htwo := constructionTwoSaving_cast hc he hp
  have hz : Tendsto (fun n : ℕ => (4 : ℝ) * Real.log 2 / (n : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hmain : Tendsto
      (fun n : ℕ => (4 : ℝ) * Real.log 2 / (n : ℝ) -
        (constructionTwoSaving b c : ℝ) * Real.log 2 +
        Real.log (constructionReducedLcm a b c n : ℝ) / (n : ℝ)) atTop
      (𝓝 ((constructionDegree a b c : ℝ) -
        (constructionTwoSaving b c : ℝ) * Real.log 2 - E.series)) := by
    have h := (hz.sub_const ((constructionTwoSaving b c : ℝ) * Real.log 2)).add hred
    rw [show (0 : ℝ) - (constructionTwoSaving b c : ℝ) * Real.log 2 +
        ((constructionDegree a b c : ℝ) - E.series) =
        (constructionDegree a b c : ℝ) -
          (constructionTwoSaving b c : ℝ) * Real.log 2 - E.series by ring] at h
    exact h
  apply hmain.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [constructionNormalizationMultiplier_log_formula]
  field_simp

end PiIrrationality
