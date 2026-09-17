import Formalization.IntegralDecay

/-! Uniform smooth-lift and amplitude bounds, including both path endpoints. -/

namespace PiIrrationality

open Set
open scoped ContDiff

theorem smoothTauPlus_joint_contDiffAt {q : ℝ × ℝ} (he0 : 0 ≤ q.1) (he1 : q.1 ≤ 1) :
    ContDiffAt ℝ ω (fun p : ℝ × ℝ => smoothTauPlus p.1 p.2) q := by
  have h1 : ContDiffAt ℝ ω (fun p : ℝ × ℝ => (p.1 : ℂ)) q :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp q (by fun_prop)
  have h2 : ContDiffAt ℝ ω (fun p : ℝ × ℝ => (p.2 : ℂ)) q :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp q (by fun_prop)
  have hd : ContDiffAt ℝ ω (fun p : ℝ × ℝ =>
      1 - Complex.I * (p.1 : ℂ) * (1 - (p.2 : ℂ) ^ (2 : ℕ))) q := by fun_prop
  have hn : ContDiffAt ℝ ω (fun _ : ℝ × ℝ => (-3 : ℂ) + 4 * Complex.I) q := contDiffAt_const
  have hc : ContDiffAt ℝ ω (fun p : ℝ × ℝ => smoothArcCore p.1 p.2) q := by
    simpa only [smoothArcCore, div_eq_mul_inv, Pi.inv_apply] using!
      hn.mul (hd.inv (smoothArcCore_den_ne_zero q.1 q.2))
  have hs := (Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane)
    _ (smoothArcCore_mem_slitPlane he0 he1 q.2)
  have hsR : ContDiffAt ℝ ω Complex.sqrt (smoothArcCore q.1 q.2) :=
    (hs.contDiffAt (n := ω)).restrict_scalars ℝ
  simpa only [smoothTauPlus, Function.comp_def] using! h2.neg.mul (hsR.comp q hc)

theorem smoothTauPlus_partial_deriv {q : ℝ × ℝ} (he0 : 0 ≤ q.1) (he1 : q.1 ≤ 1) :
    deriv (smoothTauPlus q.1) q.2 =
      (fderiv ℝ (fun p : ℝ × ℝ => smoothTauPlus p.1 p.2) q) (0, 1) := by
  have hf := (smoothTauPlus_joint_contDiffAt he0 he1).differentiableAt (by simp)
  have hg := (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
  exact (hf.hasFDerivAt.comp_hasDerivAt q.2 hg).deriv

theorem smoothTauPlus_joint_deriv_norm_continuousOn :
    ContinuousOn (fun q : ℝ × ℝ => ‖deriv (smoothTauPlus q.1) q.2‖)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  have hc : ContinuousOn
      (fun q : ℝ × ℝ =>
        ‖(fderiv ℝ (fun p : ℝ × ℝ => smoothTauPlus p.1 p.2) q) (0, 1)‖)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
    intro q hq
    exact (((smoothTauPlus_joint_contDiffAt hq.1.1 hq.1.2).continuousAt_fderiv (by simp)).clm_apply
      continuousAt_const).norm.continuousWithinAt
  exact hc.congr (fun q hq => congrArg norm (smoothTauPlus_partial_deriv hq.1.1 hq.1.2))

theorem smoothTauPlus_deriv_uniform_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ e : ℝ, 0 ≤ e → e ≤ 1 →
      ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ‖deriv (smoothTauPlus e) u‖ ≤ M := by
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hB : BddAbove ((fun q : ℝ × ℝ => ‖deriv (smoothTauPlus q.1) q.2‖) ''
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
    hK.bddAbove_image smoothTauPlus_joint_deriv_norm_continuousOn
  obtain ⟨M, hM⟩ := hB
  refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro e he0 he1 u hu0 hu1
  have hval : ‖deriv (smoothTauPlus e) u‖ ∈
      (fun q : ℝ × ℝ => ‖deriv (smoothTauPlus q.1) q.2‖) ''
        (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := ⟨(e, u), ⟨⟨he0, he1⟩, ⟨hu0, hu1⟩⟩, rfl⟩
  exact (hM hval).trans (le_max_right _ _)

theorem contourWeight_uniform_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ e : ℝ, 0 ≤ e → e ≤ 1 →
      ∀ u : ℝ, 0 ≤ u → u ≤ 1 → contourWeight e u ≤ M := by
  obtain ⟨M, hM, hbound⟩ := smoothTauPlus_deriv_uniform_bound
  refine ⟨M, hM, ?_⟩
  intro e he0 he1 u hu0 hu1
  have hd := gammaPath_pole_norm_ge_twenty (e := e) (sq_nonneg u)
    (show u ^ 2 ≤ 1 by nlinarith)
  apply (div_le_iff₀ (by linarith : 0 < ‖25 - gammaPath e (u ^ 2)‖)).mpr
  have hp := mul_nonneg hM.le
    (show 0 ≤ ‖25 - gammaPath e (u ^ 2)‖ - 1 by linarith)
  nlinarith [hbound e he0 he1 u hu0 hu1]

theorem contourAmplitude_uniform_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ e : ℝ, 0 ≤ e → e ≤ 1 →
      10 * (∫ u in (0 : ℝ)..1, contourWeight e u) ≤ M := by
  obtain ⟨M, hM, hbound⟩ := contourWeight_uniform_bound
  refine ⟨10 * M, by positivity, ?_⟩
  intro e he0 he1
  have h := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
    (contourWeight_intervalIntegrable he0 he1) (intervalIntegrable_const (c := M))
    (fun u hu => hbound e he0 he1 u hu.1 hu.2)
  norm_num at h
  linarith

end PiIrrationality
