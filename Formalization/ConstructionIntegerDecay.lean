import Formalization.ConstructionIntegerRates
import Formalization.ConstructionAnalyticRates
import Formalization.ParameterNeighborhood

/-! Decay and Hata bounds for the normalized integer forms near the candidate. -/

namespace PiIrrationality

open Filter
open scoped Topology

theorem construction_linearForm_abs {a b c n : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) (hn : 0 < n) :
    |linearForm Real.pi (constructionIntegerU a b c n) (constructionIntegerV a b c n)| =
      (constructionNormalizationMultiplier a b c n : ℝ) * ‖constructionIntegral a b c n‖ := by
  have h := congrArg norm (construction_integer_linearForm hc he hp hn)
  rw [norm_mul] at h
  have hM : (constructionNormalizationMultiplier a b c n : ℂ) =
      ((constructionNormalizationMultiplier a b c n : ℝ) : ℂ) := by norm_cast
  have hL : (constructionIntegerU a b c n : ℂ) +
      (constructionIntegerV a b c n : ℂ) * Real.pi =
      ((linearForm Real.pi (constructionIntegerU a b c n)
        (constructionIntegerV a b c n) : ℝ) : ℂ) := by
    unfold linearForm
    push_cast
    rfl
  have hpos : 0 < (constructionNormalizationMultiplier a b c n : ℝ) := by
    exact_mod_cast constructionNormalizationMultiplier_pos a b c n
  rw [hM, hL, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hpos] at h
  exact h.symm

theorem construction_linearForm_log_limsup {a b c : ℕ} (hc : 0 < c)
    (he : Even c) (hp : Admissible (constructionParameter a b c)) {C s : ℝ}
    (hC : 0 < C)
    (hbound : ∀ n : ℕ, 0 < n →
      ‖constructionIntegral a b c n‖ ≤ C * Real.exp ((c : ℝ) * n * s)) :
    limsup (fun n : ℕ =>
      ((Real.log |linearForm Real.pi (constructionIntegerU a b c n)
        (constructionIntegerV a b c n)| / ((c : ℝ) * n) : ℝ) : EReal)) atTop ≤
      ((s + parameterCost (constructionParameter a b c) : ℝ) : EReal) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hupper (n : ℕ) (hn : 0 < n) :
      Real.log |linearForm Real.pi (constructionIntegerU a b c n)
        (constructionIntegerV a b c n)| / ((c : ℝ) * n) ≤
      Real.log (constructionNormalizationMultiplier a b c n : ℝ) / ((c : ℝ) * n) +
        s + Real.log C / ((c : ℝ) * n) := by
    have hJpos := norm_pos_iff.mpr (constructionIntegral_ne_zero hc he hp n)
    have hMpos : 0 < (constructionNormalizationMultiplier a b c n : ℝ) := by
      exact_mod_cast constructionNormalizationMultiplier_pos a b c n
    have hlog := Real.log_le_log hJpos (hbound n hn)
    rw [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
    rw [construction_linearForm_abs hc he hp hn, Real.log_mul hMpos.ne' hJpos.ne',
      add_div]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hdiv := div_le_div_of_nonneg_right hlog (mul_pos hcR hnR).le
    have heq : (Real.log C + (c : ℝ) * n * s) / ((c : ℝ) * n) =
        s + Real.log C / ((c : ℝ) * n) := by field_simp; ring
    rw [heq] at hdiv
    linarith
  have hd : Tendsto (fun n : ℕ => (c : ℝ) * n) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hcR
  have hz : Tendsto (fun n : ℕ => Real.log C / ((c : ℝ) * n)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hd
  have h := ((constructionNormalizationCost_limit hc he hp).add_const s).add hz
  have h' : Tendsto (fun n : ℕ =>
      Real.log (constructionNormalizationMultiplier a b c n : ℝ) / ((c : ℝ) * n) +
        s + Real.log C / ((c : ℝ) * n)) atTop
      (𝓝 (s + parameterCost (constructionParameter a b c))) := by
    convert h using 1 <;> simp only [add_zero] <;> ring
  calc
    _ ≤ limsup (fun n : ℕ =>
        ((Real.log (constructionNormalizationMultiplier a b c n : ℝ) / ((c : ℝ) * n) +
          s + Real.log C / ((c : ℝ) * n) : ℝ) : EReal)) atTop := by
      refine limsup_le_limsup ?_
        (isCoboundedUnder_le_of_le atTop (fun _ => bot_le))
        ⟨⊤, Eventually.of_forall (fun _ => le_top)⟩
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      exact_mod_cast hupper n hn
    _ = _ := (EReal.tendsto_coe.mpr h').limsup_eq

theorem construction_linearForm_limsup_near_candidate : ∀ᶠ p in 𝓝 candidate,
    ∀ a b c : ℕ, 0 < c → Even c → constructionParameter a b c = p →
      limsup (fun n : ℕ =>
        ((Real.log |linearForm Real.pi (constructionIntegerU a b c n)
          (constructionIntegerV a b c n)| / ((c : ℝ) * n) : ℝ) : EReal)) atTop ≤
        ((parameterIntegralRate p + parameterCost p : ℝ) : EReal) := by
  obtain ⟨r, C, hr, hC, hb⟩ := constructionIntegral_uniform_exp_bound
  have hcont : Continuous (fun p : ℝ × ℝ => parameterNormOne (p - candidate)) := by
    unfold parameterNormOne
    fun_prop
  have hzero : parameterNormOne (candidate - candidate) < r := by
    simpa [parameterNormOne] using hr
  have hnear := hcont.continuousAt.eventually (gt_mem_nhds hzero)
  filter_upwards [hnear, construction_coefficient_saddle_near_candidate] with p hp hs
  intro a b c hc he hrep
  have ha : Admissible (constructionParameter a b c) := hrep ▸ (hs a b c hc hrep).1
  have h := construction_linearForm_log_limsup hc he ha hC (s := parameterIntegralRate p)
    (fun n hn => by
      simpa only [hrep] using hb a b c n hc hn (by simpa only [hrep] using hp))
  simpa only [hrep] using h

theorem construction_hata_bound_near_candidate : ∀ᶠ p in 𝓝 candidate,
    ∀ a b c : ℕ, 0 < c → Even c → constructionParameter a b c = p →
      IrrationalityMeasureAtMost Real.pi (parameterAuxiliaryBound p) := by
  filter_upwards [constructionIntegerV_log_limit_near_candidate,
    construction_linearForm_limsup_near_candidate, parameterRates_positive_near_candidate]
    with p hV hL hpos
  intro a b c hc he hrep
  exact construction_hata_bound_of_rates hc (by linarith [hpos.1])
    (by linarith [hpos.2]) (hV a b c hc he hrep) (hL a b c hc he hrep)

end PiIrrationality
