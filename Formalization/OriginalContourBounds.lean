import Formalization.SmoothContourUniform

/-! Uniform rectifiability and the original-parameter square-root derivative estimate. -/

namespace PiIrrationality

open Filter Set
open scoped Topology NNReal ENNReal

theorem tauPlus_eq_smooth_sqrt {e t : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (ht : 0 ≤ t) :
    tauPlus e t = smoothTauPlus e (Real.sqrt t) := by
  rw [smoothTauPlus_eq he0 he1 (Real.sqrt_nonneg _), Real.sq_sqrt ht]

theorem tauPlus_hasDerivAt_sqrt {e t : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (ht : 0 < t) :
    HasDerivAt (tauPlus e)
      ((1 / (2 * Real.sqrt t)) • deriv (smoothTauPlus e) (Real.sqrt t)) t := by
  have hf := ((smoothTauPlus_contDiff he0 he1).differentiable (by norm_num)
    (Real.sqrt t)).hasDerivAt
  apply (hf.scomp t (Real.hasDerivAt_sqrt ht.ne')).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with u hu
  exact tauPlus_eq_smooth_sqrt he0 he1 hu.le

theorem tauPlus_deriv_uniform_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ e : ℝ, 0 ≤ e → e ≤ 1 →
      ∀ t : ℝ, 0 < t → t ≤ 1 → ‖deriv (tauPlus e) t‖ ≤ M / Real.sqrt t := by
  obtain ⟨M, hM, hbound⟩ := smoothTauPlus_deriv_uniform_bound
  refine ⟨M / 2, by positivity, ?_⟩
  intro e he0 he1 t ht0 ht1
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hs1 : Real.sqrt t ≤ 1 := by simpa using Real.sqrt_le_sqrt ht1
  calc
    _ = (1 / (2 * Real.sqrt t)) * ‖deriv (smoothTauPlus e) (Real.sqrt t)‖ := by
      rw [(tauPlus_hasDerivAt_sqrt he0 he1 ht0).deriv, norm_smul,
        Real.norm_of_nonneg (by positivity)]
    _ ≤ (1 / (2 * Real.sqrt t)) * M :=
      mul_le_mul_of_nonneg_left (hbound e he0 he1 _ hs.le hs1) (by positivity)
    _ = (M / 2) / Real.sqrt t := by ring

theorem tauPlus_continuousOn_unit {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    ContinuousOn (tauPlus e) (Icc (0 : ℝ) 1) := by
  have hc := (smoothTauPlus_contDiff he0 he1).continuous.comp Real.continuous_sqrt
  exact hc.continuousOn.congr (fun t ht => tauPlus_eq_smooth_sqrt he0 he1 ht.1)

theorem tauMinus_continuousOn_unit {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    ContinuousOn (tauMinus e) (Icc (0 : ℝ) 1) :=
  (tauPlus_continuousOn_unit he0 he1).star

theorem originalContour_variation_uniform_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ e : ℝ, 0 ≤ e → e ≤ 1 →
      eVariationOn (tauPlus e) (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal M ∧
      eVariationOn (tauMinus e) (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal M := by
  obtain ⟨M, hM, hbound⟩ := smoothTauPlus_deriv_uniform_bound
  refine ⟨M, hM, ?_⟩
  intro e he0 he1
  let K : ℝ≥0 := ⟨M, hM.le⟩
  have hK : (K : ℝ≥0∞) = ENNReal.ofReal M := by
    rw [← ENNReal.ofReal_coe_nnreal]
    rfl
  have hlip : LipschitzOnWith K (smoothTauPlus e) (Icc (0 : ℝ) 1) :=
    Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun u _ => (smoothTauPlus_contDiff he0 he1).differentiable (by norm_num) u)
      (fun u hu => by exact_mod_cast hbound e he0 he1 u hu.1 hu.2) (convex_Icc _ _)
  have hmaps : MapsTo Real.sqrt (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro t ht
    exact ⟨Real.sqrt_nonneg _, by simpa using Real.sqrt_le_sqrt ht.2⟩
  have hvar : eVariationOn Real.sqrt (Icc (0 : ℝ) 1) = 1 := by
    simpa using (Real.sqrt_monotone.monotoneOn Set.univ).eVariationOn_eq
      (a := 0) (b := 1) (mem_univ 0) (mem_univ 1)
  have hp := hlip.comp_eVariationOn_le hmaps
  rw [hvar, mul_one, hK] at hp
  have heq : EqOn (tauPlus e) (smoothTauPlus e ∘ Real.sqrt) (Icc (0 : ℝ) 1) :=
    fun t ht => tauPlus_eq_smooth_sqrt he0 he1 ht.1
  rw [← eVariationOn.congr heq] at hp
  have hm : eVariationOn (tauMinus e) (Icc (0 : ℝ) 1) ≤
      eVariationOn (tauPlus e) (Icc (0 : ℝ) 1) := by
    change eVariationOn (fun x => star (tauPlus e x)) (Icc (0 : ℝ) 1) ≤
      eVariationOn (tauPlus e) (Icc (0 : ℝ) 1)
    have h := Complex.isometry_conj.lipschitz.lipschitzOnWith.comp_eVariationOn_le
      (show MapsTo (tauPlus e) (Icc (0 : ℝ) 1) Set.univ by intro _ _; trivial)
    simpa only [Function.comp_def, Complex.star_def,
      ENNReal.coe_one, one_mul] using h
  exact ⟨hp, hm.trans hp⟩

theorem originalContour_rectifiable {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    ContinuousOn (tauPlus e) (Icc (0 : ℝ) 1) ∧
    ContinuousOn (tauMinus e) (Icc (0 : ℝ) 1) ∧
    BoundedVariationOn (tauPlus e) (Icc (0 : ℝ) 1) ∧
    BoundedVariationOn (tauMinus e) (Icc (0 : ℝ) 1) := by
  obtain ⟨M, _, hbound⟩ := originalContour_variation_uniform_bound
  obtain ⟨hp, hm⟩ := hbound e he0 he1
  exact ⟨tauPlus_continuousOn_unit he0 he1, tauMinus_continuousOn_unit he0 he1,
    (hp.trans_lt ENNReal.ofReal_lt_top).ne, (hm.trans_lt ENNReal.ofReal_lt_top).ne⟩

end PiIrrationality
