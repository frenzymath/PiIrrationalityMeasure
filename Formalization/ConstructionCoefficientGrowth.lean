import Formalization.ConstructionCoefficientSaddle

/-! The general coefficient asymptotic and the normalized exponent in (6.66)--(6.67). -/

namespace PiIrrationality

open Filter Asymptotics PowerSeries
open scoped Topology

theorem constructionCoefficientExpression_candidate (n : ℕ) :
    constructionCoefficientExpression 1857 3714 5570 n = |-laurentCoeffRat n 0 / 2| := by
  rw [paper_pi_coeff_extraction, constructionCoefficientExpression, constructionSeries_candidate]
  have hs : constructionCoefficientScale 1857 3714 5570 = 25 * (2 : ℚ) ^ 3716 := by
    change (5 : ℚ) ^ 2 * 2 ^ 3716 = 25 * 2 ^ 3716
    norm_num only [show (5 : ℚ) ^ 2 = 25 by norm_num]
  rw [hs]

theorem constructionCoefficient_exponent {a b c : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (Real.log (constructionCoefficientScale a b c : ℝ) +
      Real.log (constructionSeriesValue a b c x) - c * Real.log x) / c =
        complexPhase ((a : ℝ) / c) ((b : ℝ) / c)
          ((25 * (1 + x) ^ 2 / (1 - x) ^ 2 : ℝ) : ℂ) := by
  have hd : 2 * c ≤ 2 * a + 4 * b := by
    have h := (construction_admissible_inequalities hc hp).2.2.2
    omega
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [constructionCoefficientScale_log hc hp, real_phase_mobius _ _ hx0 hx1,
    constructionSeriesValue, PositivePower.log_realValue _ _ _ hx0.le hx1,
    constructionDegree_cast hd]
  push_cast
  field_simp
  ring

theorem constructionCoefficientExpression_log {a b c : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) (n : ℕ) :
    Real.log (constructionCoefficientExpression a b c n : ℝ) =
      (n : ℝ) * Real.log (constructionCoefficientScale a b c : ℝ) - Real.log 4 +
        Real.log (↑(coeff (c * n) (constructionSeries a b c ^ n)) : ℝ) := by
  have hscale : (0 : ℝ) < constructionCoefficientScale a b c := by
    exact_mod_cast constructionCoefficientScale_pos a b c
  have hcoeff : (0 : ℝ) < (↑(coeff (c * n) (constructionSeries a b c ^ n)) : ℝ) := by
    exact_mod_cast PositivePower.series_diagonal_coeff_pos
      (2 * a) b (constructionDegree_pos hc hp) c n
  simp only [constructionCoefficientExpression, Rat.cast_mul, Rat.cast_div,
    Rat.cast_pow, Rat.cast_ofNat]
  rw [Real.log_mul (by positivity) hcoeff.ne',
    Real.log_div (pow_ne_zero _ hscale.ne') (by norm_num), Real.log_pow]

theorem constructionCoefficientExpression_log_limit {a b c : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hm : PositivePower.mean (2 * a) b (constructionDegree a b c) x = c) :
    Tendsto (fun n : ℕ => Real.log (constructionCoefficientExpression a b c n : ℝ) /
      ((c : ℝ) * n)) atTop
        (𝓝 (complexPhase ((a : ℝ) / c) ((b : ℝ) / c)
          ((25 * (1 + x) ^ 2 / (1 - x) ^ 2 : ℝ) : ℂ))) := by
  have hs := PositivePower.series_diagonal_log_limit
    (2 * a) b (constructionDegree_pos hc hp) hx0 hx1 c hm
  have hz : Tendsto (fun n : ℕ => Real.log 4 / (n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsum := (hz.neg.const_add (Real.log (constructionCoefficientScale a b c : ℝ))).add hs
  have h := hsum.div_const (c : ℝ)
  simp only [neg_zero, add_zero] at h
  have he : (Real.log (constructionCoefficientScale a b c : ℝ) +
      (Real.log (PositivePower.realValue (2 * a) b (constructionDegree a b c) x) -
        c * Real.log x)) / c =
      complexPhase ((a : ℝ) / c) ((b : ℝ) / c)
        ((25 * (1 + x) ^ 2 / (1 - x) ^ 2 : ℝ) : ℂ) := by
    simpa only [constructionSeriesValue, add_sub_assoc] using
      constructionCoefficient_exponent hc hp hx0 hx1
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [constructionCoefficientExpression_log hc hp]
  change (_ + Real.log (↑(coeff (c * n) (constructionSeries a b c ^ n)) : ℝ) / n) / c = _
  field_simp
  ring

theorem constructionCoefficient_asymptotic_near_candidate : ∀ᶠ p in 𝓝 candidate,
    ∀ a b c : ℕ, 0 < c → constructionParameter a b c = p →
      (fun n : ℕ => (↑(coeff (c * n) (constructionSeries a b c ^ n)) : ℝ)) ~[atTop]
        (fun n : ℕ => constructionSeriesValue a b c (parameterCoefficientSaddle p) ^ n /
          parameterCoefficientSaddle p ^ (c * n) /
            Real.sqrt (2 * Real.pi *
              PositivePower.saddleVariance (2 * a) b (constructionDegree a b c)
                (parameterCoefficientSaddle p) * n)) := by
  filter_upwards [construction_coefficient_saddle_near_candidate] with p hp
  intro a b c hc he
  obtain ⟨ha, hz, hm, hv, hu⟩ := hp a b c hc he
  exact PositivePower.series_diagonal_asymptotic
    (2 * a) b (constructionDegree_pos hc (he ▸ ha)) hz.1 hz.2 c hm

theorem constructionCoefficient_growth_near_candidate : ∀ᶠ p in 𝓝 candidate,
    ∀ a b c : ℕ, 0 < c → constructionParameter a b c = p →
      (∀ n : ℕ, 0 < constructionCoefficientExpression a b c n) ∧
      Tendsto (fun n : ℕ => Real.log (constructionCoefficientExpression a b c n : ℝ) /
        ((c : ℝ) * n)) atTop (𝓝 (parameterCoefficientRate p)) := by
  filter_upwards [construction_coefficient_saddle_near_candidate,
    parameterCoefficientSaddle_near_candidate] with p hp hs
  intro a b c hc he
  obtain ⟨ha, hz, hm, hv, hu⟩ := hp a b c hc he
  have hac : Admissible (constructionParameter a b c) := he ▸ ha
  refine ⟨constructionCoefficientExpression_pos hc hac, ?_⟩
  have h := constructionCoefficientExpression_log_limit hc hac hz.1 hz.2 hm
  have hec : (a : ℝ) / c = p.1 ∧ (b : ℝ) / c = p.2 :=
    ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
  rw [hec.1, hec.2, ← hs.2.1] at h
  exact h

end PiIrrationality
