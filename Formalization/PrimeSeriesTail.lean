import Formalization.PrimeLogIntervals

/-! The logarithmic tail enclosure (3.15). -/

namespace PiIrrationality

open Filter
open scoped Topology

noncomputable def periodicLogTail (ell r : ℝ) (K : ℕ) : ℝ :=
  Real.log (((K : ℝ) + r) / ((K : ℝ) + ell))

theorem periodicLogTail_limit (ell r : ℝ) (K : ℕ) :
    Tendsto (fun q : ℕ => periodicLogTail ell r (q + K)) atTop (𝓝 0) := by
  have hden : Tendsto (fun q : ℕ => (q : ℝ) + K + ell) atTop atTop :=
    tendsto_atTop_add_const_right atTop ell
      (tendsto_atTop_add_const_right atTop (K : ℝ) tendsto_natCast_atTop_atTop)
  have hratio : Tendsto (fun q : ℕ =>
      (((q + K : ℕ) : ℝ) + r) / (((q + K : ℕ) : ℝ) + ell)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add (hden.const_div_atTop (r - ell))
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [hden.eventually_gt_atTop 0] with q hq
    push_cast
    field_simp
    ring
  simpa only [periodicLogTail, Real.log_one, Function.comp_def] using
    (Real.continuousAt_log one_ne_zero).tendsto.comp hratio

theorem periodicLogTail_step_bounds {ell r : ℝ}
    (hℓ : 0 < ell) (hr : ell < r) (q : ℕ) :
    periodicSummandReal ell r (q + 1) ≤
        periodicLogTail ell r q - periodicLogTail ell r (q + 1) ∧
      periodicLogTail ell r q - periodicLogTail ell r (q + 1) ≤
        periodicSummandReal ell r q := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have ha : 0 < (q : ℝ) + ell := by linarith
  have hb : 0 < (q : ℝ) + r := by linarith
  have ha1 : 0 < (q : ℝ) + 1 + ell := by linarith
  have hb1 : 0 < (q : ℝ) + 1 + r := by linarith
  let x := (((q : ℝ) + r) * ((q : ℝ) + 1 + ell)) /
    (((q : ℝ) + ell) * ((q : ℝ) + 1 + r))
  have hx : 0 < x := div_pos (mul_pos hb ha1) (mul_pos ha hb1)
  have heq : periodicLogTail ell r q - periodicLogTail ell r (q + 1) =
      Real.log x := by
    unfold periodicLogTail
    push_cast
    rw [← Real.log_div (div_ne_zero hb.ne' ha.ne') (div_ne_zero hb1.ne' ha1.ne')]
    congr 1
    dsimp [x]
    field_simp
  have hup : x - 1 = (r - ell) / (((q : ℝ) + ell) * ((q : ℝ) + 1 + r)) := by
    dsimp [x]
    field_simp
    ring
  have hlo : 1 - x⁻¹ = (r - ell) / (((q : ℝ) + r) * ((q : ℝ) + 1 + ell)) := by
    dsimp [x]
    field_simp
    ring
  rw [heq]
  constructor
  · calc
      periodicSummandReal ell r (q + 1) ≤ 1 - x⁻¹ := by
        rw [hlo]
        unfold periodicSummandReal
        push_cast
        apply div_le_div_of_nonneg_left (sub_nonneg.mpr hr.le) (mul_pos hb ha1)
        nlinarith
      _ ≤ Real.log x := Real.one_sub_inv_le_log_of_pos hx
  · calc
      Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx
      _ ≤ periodicSummandReal ell r q := by
        rw [hup]
        unfold periodicSummandReal
        apply div_le_div_of_nonneg_left (sub_nonneg.mpr hr.le) (mul_pos ha hb)
        nlinarith

/-- Both bounds of (3.15); the result also holds at `K = 0`. -/
theorem periodicSummandReal_tail_bounds {ell r : ℝ}
    (hℓ : 0 < ell) (hr : ell < r) (hr1 : r ≤ 1) (K : ℕ) :
    periodicLogTail ell r K ≤ ∑' q : ℕ, periodicSummandReal ell r (q + K) ∧
      (∑' q : ℕ, periodicSummandReal ell r (q + K)) ≤
        periodicLogTail ell r K + periodicSummandReal ell r K := by
  have hs := periodicSummandReal_summable hℓ hr hr1
  have hsK := (summable_nat_add_iff K).mpr hs
  have hsK1 := (summable_nat_add_iff (K + 1)).mpr hs
  have htel (N : ℕ) :
      ∑ q ∈ Finset.range N, (periodicLogTail ell r (q + K) -
        periodicLogTail ell r (q + K + 1)) =
          periodicLogTail ell r K - periodicLogTail ell r (N + K) := by
    simpa only [Nat.add_assoc, Nat.add_comm 1 K, Nat.zero_add] using
      Finset.sum_range_sub' (fun q => periodicLogTail ell r (q + K)) N
  have hlim : Tendsto (fun N => periodicLogTail ell r K -
      periodicLogTail ell r (N + K)) atTop (𝓝 (periodicLogTail ell r K)) := by
    simpa using tendsto_const_nhds.sub (periodicLogTail_limit ell r K)
  have hlo : periodicLogTail ell r K ≤ ∑' q : ℕ, periodicSummandReal ell r (q + K) := by
    apply le_of_tendsto_of_tendsto hlim hsK.hasSum.tendsto_sum_nat
    filter_upwards with N
    rw [← htel]
    exact Finset.sum_le_sum fun q _ => (periodicLogTail_step_bounds hℓ hr (q + K)).2
  have hup : (∑' q : ℕ, periodicSummandReal ell r (q + (K + 1))) ≤
      periodicLogTail ell r K := by
    apply le_of_tendsto_of_tendsto hsK1.hasSum.tendsto_sum_nat hlim
    filter_upwards with N
    rw [← htel]
    apply Finset.sum_le_sum
    intro q _
    simpa only [Nat.add_assoc] using (periodicLogTail_step_bounds hℓ hr (q + K)).1
  refine ⟨hlo, ?_⟩
  have heq := hsK.tsum_eq_zero_add
  simp only [Nat.zero_add, Nat.add_assoc, Nat.add_comm 1 K] at heq
  linarith

end PiIrrationality
