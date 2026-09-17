import Formalization.ComplexDensityModulus
import Formalization.SaddlePhaseMaximum
import Formalization.ContourEstimate
import Formalization.LinearFormNonvanishing

/-! The actual exponential integral bound and logarithmic limsup (4.27)--(4.28). -/

namespace PiIrrationality

open Filter
open scoped Topology

noncomputable def integralDecayRate : ℝ :=
  complexPhase (1857 / 5570) (3714 / 5570) saddleUpper

noncomputable def contourWeight (e u : ℝ) : ℝ :=
  ‖deriv (smoothTauPlus e) u‖ / ‖25 - gammaPath e (u ^ 2)‖

noncomputable def contourAmplitude : ℝ :=
  10 * ∫ u in (0 : ℝ)..1, contourWeight saddleEta u

theorem contourWeight_nonneg (e u : ℝ) : 0 ≤ contourWeight e u := by
  unfold contourWeight
  positivity

theorem contourWeight_continuousOn {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    ContinuousOn (contourWeight e) (Set.Icc 0 1) := by
  have hd := (smoothTauPlus_contDiff he0 he1).continuous_deriv_one.norm
  have hg : Continuous (gammaPath e) :=
    continuous_iff_continuousAt.mpr (fun t => (gammaPath_hasDerivAt e t).continuousAt)
  have hp : Continuous (fun u : ℝ => ‖25 - gammaPath e (u ^ 2)‖) :=
    (continuous_const.sub (hg.comp (continuous_id.pow 2))).norm
  intro u hu
  have hb := gammaPath_pole_norm_ge_twenty (e := e) (sq_nonneg u)
    (show u ^ 2 ≤ 1 by nlinarith [hu.1, hu.2])
  exact (hd.continuousAt.div hp.continuousAt (by linarith)).continuousWithinAt

theorem contourWeight_intervalIntegrable {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    IntervalIntegrable (contourWeight e) MeasureTheory.volume 0 1 :=
  (contourWeight_continuousOn he0 he1).intervalIntegrable_of_Icc (by norm_num)

theorem complexDensity_saddle_lift_bound (n : ℕ) (hn : 0 < n) (u : ℝ)
    (hu : u ∈ Set.Ioc (0 : ℝ) 1) :
    ‖complexDensity n (smoothTauPlus saddleEta u) * deriv (smoothTauPlus saddleEta) u‖ ≤
      5 * contourWeight saddleEta u * Real.exp (5570 * (n : ℝ) * integralDecayRate) := by
  rcases hu.2.eq_or_lt with he | hu1
  · subst u
    rw [complexDensity_smoothTauPlus_one n hn, zero_mul, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (contourWeight_nonneg _ _)) (Real.exp_pos _).le
  have ht0 : 0 < u ^ 2 := sq_pos_of_pos hu.1
  have ht1 : u ^ 2 < 1 := by nlinarith [hu.1]
  have he0 := saddleEta_pos.le
  have he1 := saddleEta_lt_one.le
  have hy : (smoothTauPlus saddleEta u) ^ 2 = gammaPath saddleEta (u ^ 2) := by
    rw [smoothTauPlus_eq he0 he1 hu.1.le, tauPlus_sq]
  have hp : 25 - gammaPath saddleEta (u ^ 2) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    have h := gammaPath_pole_norm_ge_twenty (e := saddleEta) ht0.le ht1.le
    linarith
  have hmod := complexDensity_modulus n hy (gammaPath_ne_zero he0 he1 ht0 ht1.le)
    (gammaPath_quadratic_ne_zero saddleEta_gt_nine_tenths ht0 ht1) hp
  calc
    _ = 5 * contourWeight saddleEta u * Real.exp (5570 * (n : ℝ) *
        complexPhase (1857 / 5570) (3714 / 5570) (gammaPath saddleEta (u ^ 2))) := by
      rw [norm_mul, hmod]
      unfold contourWeight
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (complexPhase_saddle_arc_le (u ^ 2) ⟨ht0, ht1⟩) (by positivity)))
      (mul_nonneg (by norm_num) (contourWeight_nonneg _ _))

theorem paperIntegral_exp_bound (n : ℕ) (hn : 0 < n) :
    ‖paperIntegral n‖ ≤ contourAmplitude * Real.exp (5570 * (n : ℝ) * integralDecayRate) := by
  have he0 := saddleEta_pos.le
  have he1 := saddleEta_lt_one.le
  have hA := (contourWeight_intervalIntegrable he0 he1).const_mul 5
  have hp := intervalIntegral_norm_bound_with_factor hA
    (fun u => mul_nonneg (by norm_num) (contourWeight_nonneg saddleEta u))
    (Real.exp_pos (5570 * (n : ℝ) * integralDecayRate)).le (complexDensity_saddle_lift_bound n hn)
  have hbm : ∀ u ∈ Set.Ioc (0 : ℝ) 1,
      ‖complexDensity n (smoothTauMinus saddleEta u) * deriv (smoothTauMinus saddleEta) u‖ ≤
        5 * contourWeight saddleEta u * Real.exp (5570 * (n : ℝ) * integralDecayRate) := by
    intro u hu
    rw [smoothTauMinus_density_norm n he0 he1]
    exact complexDensity_saddle_lift_bound n hn u hu
  have hm := intervalIntegral_norm_bound_with_factor hA
    (fun u => mul_nonneg (by norm_num) (contourWeight_nonneg saddleEta u))
    (Real.exp_pos (5570 * (n : ℝ) * integralDecayRate)).le hbm
  rw [intervalIntegral.integral_const_mul] at hp hm
  rw [paperIntegral_deformed n he0 he1, norm_mul, Complex.norm_I, one_mul]
  calc
    _ ≤ ‖densityPathIntegral n (smoothTauPlus saddleEta)‖ +
        ‖densityPathIntegral n (smoothTauMinus saddleEta)‖ := by
      simpa only [norm_neg] using norm_add_le
        (-densityPathIntegral n (smoothTauPlus saddleEta)) (densityPathIntegral n (smoothTauMinus saddleEta))
    _ ≤ _ := by
      dsimp [densityPathIntegral, contourAmplitude]
      nlinarith

theorem contourAmplitude_pos : 0 < contourAmplitude := by
  have hj : 0 < ‖paperIntegral 1‖ := norm_pos_iff.mpr (paperIntegral_ne_zero 1 (by norm_num))
  have hp := hj.trans_le (paperIntegral_exp_bound 1 (by norm_num))
  exact (mul_pos_iff_of_pos_right (Real.exp_pos _)).mp hp

theorem paperIntegral_log_upper (n : ℕ) (hn : 0 < n) :
    Real.log ‖paperIntegral n‖ / (5570 * (n : ℝ)) ≤
      integralDecayRate + Real.log contourAmplitude / (5570 * (n : ℝ)) := by
  have hj := norm_pos_iff.mpr (paperIntegral_ne_zero n hn)
  have h := Real.log_le_log hj (paperIntegral_exp_bound n hn)
  rw [Real.log_mul contourAmplitude_pos.ne' (Real.exp_pos _).ne', Real.log_exp] at h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ (Real.log contourAmplitude + 5570 * (n : ℝ) * integralDecayRate) / (5570 * (n : ℝ)) :=
      div_le_div_of_nonneg_right h (by positivity)
    _ = _ := by field_simp; ring

theorem paperIntegral_log_upper_eventually {epsilon : ℝ} (he : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, Real.log ‖paperIntegral n‖ / (5570 * (n : ℝ)) <
      integralDecayRate + epsilon := by
  have hd : Tendsto (fun n : ℕ => 5570 * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have h : Tendsto (fun n : ℕ => Real.log contourAmplitude / (5570 * (n : ℝ)))
      atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds.div_atTop hd
  filter_upwards [eventually_gt_atTop (0 : ℕ), h.eventually (gt_mem_nhds he)] with n hn hne
  exact (paperIntegral_log_upper n hn).trans_lt (by linarith)

theorem paperIntegral_log_limsup :
    limsup (fun n : ℕ => ((Real.log ‖paperIntegral n‖ / (5570 * (n : ℝ)) : ℝ) : EReal)) atTop ≤
      (integralDecayRate : EReal) := by
  have hd : Tendsto (fun n : ℕ => 5570 * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have h : Tendsto (fun n : ℕ => integralDecayRate +
      Real.log contourAmplitude / (5570 * (n : ℝ))) atTop (𝓝 integralDecayRate) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.div_atTop hd).const_add integralDecayRate
  have hE := EReal.tendsto_coe.mpr h
  calc
    _ ≤ limsup (fun n : ℕ => ((integralDecayRate +
        Real.log contourAmplitude / (5570 * (n : ℝ)) : ℝ) : EReal)) atTop := by
      refine limsup_le_limsup ?_
        (isCoboundedUnder_le_of_le atTop (fun _ => bot_le))
        ⟨⊤, Eventually.of_forall (fun _ => le_top)⟩
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      exact_mod_cast paperIntegral_log_upper n hn
    _ = _ := hE.limsup_eq

end PiIrrationality
