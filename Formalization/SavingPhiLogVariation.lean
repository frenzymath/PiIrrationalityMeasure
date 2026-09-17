import Formalization.SavingOmegaLogVariation

/-! The uniform actual saving expansions (6.20)--(6.21) at the candidate. -/

namespace PiIrrationality

theorem savingOmega_scaled_candidate (h : ℝ × ℝ) :
    savingOmega (1857 + 5570 * h.1) (3714 + 5570 * h.2) 5570 =
      5570 * savingPhi (candidate + h) := by
  have he := savingOmega_eq_scaled_phi (candidate + h).1 (candidate + h).2
    (by norm_num : (0 : ℝ) < 5570)
  have hx : 5570 * (candidate + h).1 = 1857 + 5570 * h.1 := by
    dsimp [candidate]
    ring
  have hy : 5570 * (candidate + h).2 = 3714 + 5570 * h.2 := by
    dsimp [candidate]
    ring
  rw [hx, hy] at he
  exact he

theorem savingPhi_candidate_log_variation :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ h : ℝ × ℝ,
      0 < parameterNormOne h → parameterNormOne h ≤ r →
      |savingPhi (candidate + h) - savingPhi candidate -
        candidateSectorVariation h * Real.log (1 / parameterNormOne h)| ≤
          C * parameterNormOne h := by
  obtain ⟨r, C, hr, hC, hmodel⟩ := savingOmega_candidate_log_variation
  refine ⟨r / 5570, C + |Real.log 5570|, by positivity, by positivity, ?_⟩
  intro h hd hdr
  have hn : parameterNormOne ((5570 : ℝ) • h) = 5570 * parameterNormOne h := by
    rw [parameterNormOne_smul]
    norm_num
  have hs : parameterNormOne ((5570 : ℝ) • h) ≤ r := by
    rw [hn]
    simpa only [mul_comm] using (le_div_iff₀ (by norm_num : (0 : ℝ) < 5570)).mp hdr
  have hpos : 0 < parameterNormOne ((5570 : ℝ) • h) := by rw [hn]; positivity
  have he := hmodel ((5570 : ℝ) • h) hpos hs
  have hzero : savingOmega 1857 3714 5570 = 5570 * savingPhi candidate := by
    simpa only [Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero] using
      savingOmega_scaled_candidate 0
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, hn,
    savingOmega_scaled_candidate, hzero,
    candidateSectorVariation_smul h (by norm_num : (0 : ℝ) ≤ 5570)] at he
  have hlog : Real.log (1 / (5570 * parameterNormOne h)) =
      Real.log (1 / parameterNormOne h) - Real.log 5570 := by
    rw [Real.log_div one_ne_zero (mul_ne_zero (by norm_num) hd.ne'),
      Real.log_div one_ne_zero hd.ne', Real.log_mul (by norm_num) hd.ne', Real.log_one]
    ring
  rw [hlog] at he
  let E := savingPhi (candidate + h) - savingPhi candidate -
    candidateSectorVariation h * Real.log (1 / parameterNormOne h)
  have he' : |5570 * E + 5570 * candidateSectorVariation h * Real.log 5570| ≤
      C * (5570 * parameterNormOne h) := by
    convert he using 1
    congr 1
    dsimp [E]
    ring
  have hcorr : |5570 * candidateSectorVariation h * Real.log 5570| ≤
      5570 * parameterNormOne h * |Real.log 5570| := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5570)]
    gcongr
    exact candidateSectorVariation_abs_le h
  have ht := abs_sub (5570 * E + 5570 * candidateSectorVariation h * Real.log 5570)
    (5570 * candidateSectorVariation h * Real.log 5570)
  rw [add_sub_cancel_right, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5570)] at ht
  change |E| ≤ _
  nlinarith only [ht, he', hcorr]

theorem savingPhi_candidate_directional_log_variation :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ v : ℝ × ℝ,
      parameterNormOne v = 1 → ∀ e : ℝ, 0 < e → e ≤ r →
      |savingPhi (candidate + e • v) - savingPhi candidate -
        e * candidateSectorVariation v * Real.log (1 / e)| ≤ C * e := by
  obtain ⟨r, C, hr, hC, hmodel⟩ := savingPhi_candidate_log_variation
  refine ⟨r, C, hr, hC, ?_⟩
  intro v hv e he her
  have hn : parameterNormOne (e • v) = e := by
    rw [parameterNormOne_smul, hv, mul_one, abs_of_pos he]
  simpa only [hn, candidateSectorVariation_smul v he.le] using
    hmodel (e • v) (by rwa [hn]) (by rwa [hn])

end PiIrrationality
