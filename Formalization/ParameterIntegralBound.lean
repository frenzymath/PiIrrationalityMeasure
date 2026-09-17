import Formalization.ConstructionIntegral
import Formalization.ParameterArcMaximum
import Formalization.SmoothContourUniform
import Formalization.EndpointUniformOrder

/-! The actual locally uniform exponential integral estimate (6.52). -/

namespace PiIrrationality

open Filter
open scoped Topology

theorem constructionDensity_lift_bound (a b c n : ℕ) (hc : 0 < c) (hb : 0 < b) (hn : 0 < n)
    {e s : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (he9 : (9 : ℝ) / 10 < e)
    (hmax : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      complexPhase ((a : ℝ) / c) ((b : ℝ) / c) (gammaPath e t) ≤ s)
    (u : ℝ) (hu : u ∈ Set.Ioc (0 : ℝ) 1) :
    ‖constructionDensity a b c n (smoothTauPlus e u) * deriv (smoothTauPlus e) u‖ ≤
      5 * contourWeight e u * Real.exp ((c : ℝ) * n * s) := by
  rcases hu.2.eq_or_lt with he | hu1
  · subst u
    rw [constructionDensity_smoothTauPlus_one a b c n hb hn, zero_mul, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (contourWeight_nonneg _ _)) (Real.exp_pos _).le
  have ht0 : 0 < u ^ 2 := sq_pos_of_pos hu.1
  have ht1 : u ^ 2 < 1 := by nlinarith [hu.1]
  have hy : (smoothTauPlus e u) ^ 2 = gammaPath e (u ^ 2) := by
    rw [smoothTauPlus_eq he0 he1 hu.1.le, tauPlus_sq]
  have hp : 25 - gammaPath e (u ^ 2) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    have h := gammaPath_pole_norm_ge_twenty (e := e) ht0.le ht1.le
    linarith
  have hmod := constructionDensity_modulus a b c n hc hy
    (gammaPath_ne_zero he0 he1 ht0 ht1.le) (gammaPath_quadratic_ne_zero he9 ht0 ht1) hp
  calc
    _ = 5 * contourWeight e u * Real.exp ((c : ℝ) * n *
        complexPhase ((a : ℝ) / c) ((b : ℝ) / c) (gammaPath e (u ^ 2))) := by
      rw [norm_mul, hmod]
      unfold contourWeight
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hmax _ ⟨ht0, ht1⟩) (by positivity)))
      (mul_nonneg (by norm_num) (contourWeight_nonneg _ _))

theorem constructionIntegral_exp_bound (a b c n : ℕ) (hc : 0 < c) (hb : 0 < b) (hn : 0 < n)
    {e s : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (he9 : (9 : ℝ) / 10 < e)
    (hmax : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      complexPhase ((a : ℝ) / c) ((b : ℝ) / c) (gammaPath e t) ≤ s) :
    ‖constructionIntegral a b c n‖ ≤
      (10 * ∫ u in (0 : ℝ)..1, contourWeight e u) * Real.exp ((c : ℝ) * n * s) := by
  have hA := (contourWeight_intervalIntegrable he0 he1).const_mul 5
  have hp := intervalIntegral_norm_bound_with_factor hA
    (fun u => mul_nonneg (by norm_num) (contourWeight_nonneg e u))
    (Real.exp_pos ((c : ℝ) * n * s)).le
    (constructionDensity_lift_bound a b c n hc hb hn he0 he1 he9 hmax)
  have hbm : ∀ u ∈ Set.Ioc (0 : ℝ) 1,
      ‖constructionDensity a b c n (smoothTauMinus e u) * deriv (smoothTauMinus e) u‖ ≤
        5 * contourWeight e u * Real.exp ((c : ℝ) * n * s) := by
    intro u hu
    rw [constructionDensity_lift_conj_norm a b c n he0 he1]
    exact constructionDensity_lift_bound a b c n hc hb hn he0 he1 he9 hmax u hu
  have hm := intervalIntegral_norm_bound_with_factor hA
    (fun u => mul_nonneg (by norm_num) (contourWeight_nonneg e u))
    (Real.exp_pos ((c : ℝ) * n * s)).le hbm
  rw [intervalIntegral.integral_const_mul] at hp hm
  rw [constructionIntegral_deformed a b c n he0 he1, norm_mul, Complex.norm_I, one_mul]
  calc
    _ ≤ ‖∫ u in (0 : ℝ)..1,
          constructionDensity a b c n (smoothTauPlus e u) * deriv (smoothTauPlus e) u‖ +
        ‖∫ u in (0 : ℝ)..1,
          constructionDensity a b c n (smoothTauMinus e u) * deriv (smoothTauMinus e) u‖ := by
      simpa only [norm_neg] using norm_add_le
        (-(∫ u in (0 : ℝ)..1,
          constructionDensity a b c n (smoothTauPlus e u) * deriv (smoothTauPlus e) u))
        (∫ u in (0 : ℝ)..1,
          constructionDensity a b c n (smoothTauMinus e u) * deriv (smoothTauMinus e) u)
    _ ≤ _ := by nlinarith

theorem constructionIntegral_uniform_exp_bound :
    ∃ radius C : ℝ, 0 < radius ∧ 0 < C ∧ ∀ a b c n : ℕ, 0 < c → 0 < n →
      parameterNormOne (constructionParameter a b c - candidate) < radius →
      ‖constructionIntegral a b c n‖ ≤
        C * Real.exp ((c : ℝ) * n * parameterIntegralRate (constructionParameter a b c)) := by
  obtain ⟨C, hC, hAmplitude⟩ := contourAmplitude_uniform_bound
  have hb : ∀ᶠ p : ℝ × ℝ in 𝓝 candidate, 0 < p.2 :=
    continuous_snd.continuousAt.eventually_const_lt (by norm_num [candidate])
  obtain ⟨radius, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    (parameterContour_near_candidate.and (parameterArcPhase_maximum_near_candidate.and hb))
  refine ⟨radius, C, hr, hC, ?_⟩
  intro a b c n hc hn hdist
  let p := constructionParameter a b c
  have hdist' : dist p candidate < radius := by
    rw [dist_eq_norm]
    exact (norm_le_parameterNormOne _).trans_lt hdist
  obtain ⟨hp, hmax, hbp⟩ := hball hdist'
  have hb' : 0 < b := by
    by_contra h
    have hz : b = 0 := Nat.eq_zero_of_not_pos h
    norm_num [p, constructionParameter, hz] at hbp
  have he0 : 0 ≤ parameterSaddleEta p := by linarith [hp.1]
  have he1 : parameterSaddleEta p ≤ 1 := by linarith [hp.2.1]
  have h := constructionIntegral_exp_bound a b c n hc hb' hn he0 he1 hp.1
    (fun t ht => (hmax t ht).1)
  exact h.trans (mul_le_mul_of_nonneg_right (hAmplitude _ he0 he1) (Real.exp_pos _).le)

end PiIrrationality
