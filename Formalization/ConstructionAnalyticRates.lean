import Formalization.ConstructionRationalLinearForm
import Formalization.ParameterIntegralBound

/-! Both analytic rates now concern the actual general integral and its pi coefficient. -/

namespace PiIrrationality

open Filter
open scoped Topology

theorem constructionIntegral_log_limsup {a b c : ℕ} (hc : 0 < c) (hce : Even c)
    (hp : Admissible (constructionParameter a b c)) {C s : ℝ} (hC : 0 < C)
    (hbound : ∀ n : ℕ, 0 < n → ‖constructionIntegral a b c n‖ ≤ C * Real.exp ((c : ℝ) * n * s)) :
    limsup (fun n : ℕ => ((Real.log ‖constructionIntegral a b c n‖ / ((c : ℝ) * n) : ℝ) : EReal))
      atTop ≤ (s : EReal) := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hlog (n : ℕ) (hn : 0 < n) :
      Real.log ‖constructionIntegral a b c n‖ / ((c : ℝ) * n) ≤
        s + Real.log C / ((c : ℝ) * n) := by
    have hj := norm_pos_iff.mpr (constructionIntegral_ne_zero hc hce hp n)
    have h := Real.log_le_log hj (hbound n hn)
    rw [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp] at h
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc
      _ ≤ (Real.log C + (c : ℝ) * n * s) / ((c : ℝ) * n) :=
        div_le_div_of_nonneg_right h (by positivity)
      _ = _ := by field_simp; ring
  have hd : Tendsto (fun n : ℕ => (c : ℝ) * n) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc'
  have h : Tendsto (fun n : ℕ => s + Real.log C / ((c : ℝ) * n)) atTop (𝓝 s) := by
    simpa only [add_zero] using (tendsto_const_nhds.div_atTop hd).const_add s
  have hE := EReal.tendsto_coe.mpr h
  calc
    _ ≤ limsup (fun n : ℕ => ((s + Real.log C / ((c : ℝ) * n) : ℝ) : EReal)) atTop := by
      refine limsup_le_limsup ?_
        (isCoboundedUnder_le_of_le atTop (fun _ => bot_le))
        ⟨⊤, Eventually.of_forall (fun _ => le_top)⟩
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      exact_mod_cast hlog n hn
    _ = _ := hE.limsup_eq

theorem constructionIntegral_limsup_near_candidate : ∀ᶠ p in 𝓝 candidate,
    ∀ a b c : ℕ, 0 < c → Even c → constructionParameter a b c = p →
      limsup (fun n : ℕ => ((Real.log ‖constructionIntegral a b c n‖ / ((c : ℝ) * n) : ℝ) : EReal))
        atTop ≤ (parameterIntegralRate p : EReal) := by
  obtain ⟨r, C, hr, hC, hb⟩ := constructionIntegral_uniform_exp_bound
  have hcont : Continuous (fun p : ℝ × ℝ => parameterNormOne (p - candidate)) := by
    unfold parameterNormOne
    fun_prop
  have hzero : parameterNormOne (candidate - candidate) < r := by
    simpa [parameterNormOne] using hr
  have hnear := hcont.continuousAt.eventually (gt_mem_nhds hzero)
  filter_upwards [hnear, construction_coefficient_saddle_near_candidate] with p hp hs
  intro a b c hc hce he
  have ha : Admissible (constructionParameter a b c) := he ▸ (hs a b c hc he).1
  apply constructionIntegral_log_limsup hc hce ha hC
  intro n hn
  simpa only [he] using hb a b c n hc hn (by simpa only [he] using hp)

theorem construction_analytic_rates_near_candidate : ∀ᶠ p in 𝓝 candidate,
    ∀ a b c : ℕ, 0 < c → Even c → constructionParameter a b c = p →
      Admissible p ∧
      (∀ n : ℕ, constructionIntegral a b c n =
        (constructionRationalU a b c n : ℂ) + (constructionRationalV a b c n : ℂ) * Real.pi) ∧
      (∀ n : ℕ, constructionRationalV a b c n < 0 ∧ constructionIntegral a b c n ≠ 0) ∧
      Tendsto (fun n : ℕ => Real.log |(constructionRationalV a b c n : ℝ)| / ((c : ℝ) * n))
        atTop (𝓝 (parameterCoefficientRate p)) ∧
      limsup (fun n : ℕ => ((Real.log ‖constructionIntegral a b c n‖ / ((c : ℝ) * n) : ℝ) : EReal))
        atTop ≤ (parameterIntegralRate p : EReal) := by
  filter_upwards [construction_coefficient_saddle_near_candidate,
    construction_pi_coeff_growth_near_candidate, constructionIntegral_limsup_near_candidate]
    with p hp hv hJ
  intro a b c hc hce he
  have ha := (hp a b c hc he).1
  have hac : Admissible (constructionParameter a b c) := he ▸ ha
  exact ⟨ha, constructionIntegral_rational_linearForm a b c,
    fun n => ⟨constructionRationalV_neg hc hce hac n, constructionIntegral_ne_zero hc hce hac n⟩,
    (hv a b c hc hce he).2, hJ a b c hc hce he⟩

end PiIrrationality
