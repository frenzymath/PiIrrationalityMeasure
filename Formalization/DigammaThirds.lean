import Formalization.PrimeSavingDigamma

/-! The special digamma values needed for the old saving constant. -/

namespace PiIrrationality

open Filter
open scoped Topology

theorem realDigamma_one : realDigamma 1 = -Real.eulerMascheroniConstant := by
  simp [realDigamma, Complex.digamma_one]

theorem realDigamma_half : realDigamma (1 / 2) =
    -2 * Real.log 2 - Real.eulerMascheroniConstant := by
  unfold realDigamma
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    Complex.digamma_one_half]
  simp [Complex.log_re]

theorem harmonic_thirds_identity (N : ℕ) :
    (∑ k ∈ Finset.range N,
      (1 / ((k : ℝ) + 1 / 3) + 1 / ((k : ℝ) + 2 / 3) - 2 / ((k : ℝ) + 1))) =
        3 * ((harmonic (3 * N) : ℝ) - (harmonic N : ℝ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hidx : 3 * (N + 1) = (3 * N + 1) + 1 + 1 := by omega
      rw [hidx, harmonic_succ, harmonic_succ, harmonic_succ, harmonic_succ]
      push_cast
      have h1 : (N : ℝ) + 1 / 3 ≠ 0 := by positivity
      have h2 : (N : ℝ) + 2 / 3 ≠ 0 := by positivity
      have h3 : (N : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring

theorem harmonic_thirds_limit :
    Tendsto (fun N : ℕ => (harmonic (3 * N) : ℝ) - (harmonic N : ℝ))
      atTop (𝓝 (Real.log 3)) := by
  have hN : Tendsto (fun N : ℕ => 3 * N) atTop atTop := by
    apply tendsto_atTop_mono (f := fun N : ℕ => N)
    · intro N
      omega
    · exact tendsto_id
  have h := ((Real.tendsto_harmonic_sub_log.comp hN).sub
    Real.tendsto_harmonic_sub_log).add_const (Real.log 3)
  simp only [sub_self, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNr : (N : ℝ) ≠ 0 := by positivity
  dsimp only [Function.comp_apply]
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hNr]
  ring

theorem realDigamma_thirds_sum :
    realDigamma (1 / 3) + realDigamma (2 / 3) =
      -2 * Real.eulerMascheroniConstant - 3 * Real.log 3 := by
  have h := (hasSum_reciprocal_difference (ell := 1 / 3) (r := 1)
    (by norm_num) (by norm_num)).add
      (hasSum_reciprocal_difference (ell := 2 / 3) (r := 1) (by norm_num) (by norm_num))
  have hs : Tendsto (fun N : ℕ => 3 * ((harmonic (3 * N) : ℝ) - (harmonic N : ℝ)))
      atTop (𝓝 (2 * realDigamma 1 - realDigamma (1 / 3) - realDigamma (2 / 3))) := by
    convert! h.tendsto_sum_nat using 1
    · funext N
      rw [← harmonic_thirds_identity]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    · ring
  have he := tendsto_nhds_unique hs (harmonic_thirds_limit.const_mul 3)
  rw [realDigamma_one] at he
  linarith

theorem realDigamma_thirds_difference :
    realDigamma (2 / 3) - realDigamma (1 / 3) = Real.pi / Real.sqrt 3 := by
  have hG (x : ℝ) (hx : 0 < x) : DifferentiableAt ℝ Real.Gamma x :=
    Real.differentiableAt_Gamma (fun m => by
      have hm := Nat.cast_nonneg (α := ℝ) m
      linarith)
  have h1 := hG (1 / 3) (by norm_num)
  have h2 := hG (2 / 3) (by norm_num)
  have h2' : HasDerivAt (fun x : ℝ => Real.Gamma (1 - x))
      (-deriv Real.Gamma (2 / 3)) (1 / 3) := by
    have h2a : HasDerivAt Real.Gamma (deriv Real.Gamma (2 / 3)) (1 - (1 / 3 : ℝ)) := by
      norm_num only [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num]
      exact h2.hasDerivAt
    convert! h2a.comp (1 / 3) ((hasDerivAt_id (1 / 3 : ℝ)).const_sub 1) using 1 <;> norm_num
  have hl := h1.hasDerivAt.mul h2'
  have hsin : Real.sin (Real.pi * (1 / 3)) = Real.sqrt 3 / 2 := by
    rw [mul_one_div, Real.sin_pi_div_three]
  have hcos : Real.cos (Real.pi * (1 / 3)) = 1 / 2 := by
    rw [mul_one_div, Real.cos_pi_div_three]
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsn : Real.sin (Real.pi * (1 / 3)) ≠ 0 := by rw [hsin]; positivity
  have hr := (hasDerivAt_const (1 / 3 : ℝ) Real.pi).div
    (((hasDerivAt_id (1 / 3 : ℝ)).const_mul Real.pi).sin) hsn
  have heq : (fun x : ℝ => Real.Gamma x * Real.Gamma (1 - x)) =
      (fun x => Real.pi / Real.sin (Real.pi * x)) :=
    funext Real.Gamma_mul_Gamma_one_sub
  change HasDerivAt (fun x : ℝ => Real.Gamma x * Real.Gamma (1 - x)) _ _ at hl
  rw [heq] at hl
  have he := hl.unique hr
  have hp := Real.Gamma_mul_Gamma_one_sub (1 / 3 : ℝ)
  norm_num only [id_eq, show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num] at he hp
  rw [hsin, hcos] at he
  rw [hsin] at hp
  rw [realDigamma_eq_logDeriv (by norm_num : (0 : ℝ) < 2 / 3),
    realDigamma_eq_logDeriv (by norm_num : (0 : ℝ) < 1 / 3), logDeriv_apply, logDeriv_apply]
  have hG1 := (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3)).ne'
  have hG2 := (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 2 / 3)).ne'
  field_simp at he hp ⊢
  nlinarith [Real.pi_pos]

theorem realDigamma_two_thirds :
    realDigamma (2 / 3) = -Real.eulerMascheroniConstant -
      (3 / 2) * Real.log 3 + Real.pi / (2 * Real.sqrt 3) := by
  have hs := realDigamma_thirds_sum
  have hd := realDigamma_thirds_difference
  rw [show Real.pi / (2 * Real.sqrt 3) = (Real.pi / Real.sqrt 3) / 2 by ring]
  linarith

end PiIrrationality
