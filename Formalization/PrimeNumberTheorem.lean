import Formalization.PNT.Wiener
import Mathlib

/-!
The Chebyshev form of the prime number theorem needed in Section 3.2.
The passage from the von Mangoldt form follows PNT+ Consequences.lean,
at commit a5154676af9aa3095150ee410cdda80555aa0642 (Apache 2.0).
-/

namespace PiIrrationality

open Filter Asymptotics ArithmeticFunction Finset
open scoped Topology

private theorem vonMangoldt_sum_Iic_limit :
    Tendsto (fun N : ℕ => (∑ n ∈ Iic N, vonMangoldt n) / (N : ℝ)) atTop (𝓝 1) := by
  have heq : (fun N : ℕ => (∑ n ∈ Iic N, vonMangoldt n) / (N : ℝ)) =
      (fun N : ℕ => cumsum vonMangoldt N / (N : ℝ) + vonMangoldt N / (N : ℝ)) := by
    funext N
    rw [← Nat.range_succ_eq_Iic, cumsum, Finset.sum_range_succ]
    exact add_div _ _ _
  rw [heq, ← add_zero (1 : ℝ)]
  apply Tendsto.add WeakPNT
  have hlog : Tendsto (fun N : ℕ => Real.log N / (N : ℝ)) atTop (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    exact h.comp tendsto_natCast_atTop_atTop
  exact squeeze_zero (fun N => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg N))
    (fun N => div_le_div_of_nonneg_right vonMangoldt_le_log (Nat.cast_nonneg N)) hlog

theorem chebyshevPsi_asymptotic :
    Chebyshev.psi ~[atTop] (fun x : ℝ => x) := by
  have hfloor : Chebyshev.psi ~[atTop] (fun x : ℝ => (⌊x⌋₊ : ℝ)) := by
    rw [isEquivalent_iff_tendsto_one]
    · have h := vonMangoldt_sum_Iic_limit.comp (tendsto_nat_floor_atTop (α := ℝ))
      simpa only [Function.comp_def, Pi.div_def, Chebyshev.psi_eq_sum_Icc, Finset.Iic_eq_Icc,
        Nat.bot_eq_zero] using h
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      exact_mod_cast (Nat.floor_pos.mpr hx).ne'
  exact hfloor.trans (Asymptotics.isEquivalent_nat_floor (R := ℝ))

private theorem sqrt_mul_log_isLittleO :
    (fun x : ℝ => Real.sqrt x * Real.log x) =o[atTop] (fun x : ℝ => x) := by
  have hsqr : ∀ᶠ x : ℝ in atTop, Real.sqrt x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (Real.sqrt_ne_zero hx.le).mpr hx.ne'
  apply (isLittleO_mul_iff_isLittleO_div hsqr).mpr
  have heq : (fun x : ℝ => x / Real.sqrt x) = (fun x : ℝ => x ^ (1 / 2 : ℝ)) := by
    funext x
    rw [Real.div_sqrt, Real.sqrt_eq_rpow]
  rw [heq]
  exact isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)

theorem chebyshevTheta_asymptotic :
    Chebyshev.theta ~[atTop] (fun x : ℝ => x) := by
  have hdiff : (Chebyshev.psi - Chebyshev.theta) =O[atTop]
      (fun x : ℝ => 2 * Real.sqrt x * Real.log x) := by
    rw [isBigO_iff']
    refine ⟨1, one_pos, ?_⟩
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hp : 0 ≤ 2 * Real.sqrt x * Real.log x :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg x)) (Real.log_nonneg (by linarith))
    simp only [Pi.sub_apply, Real.norm_eq_abs, one_mul, abs_of_nonneg hp]
    rw [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))]
    have h := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (show 1 ≤ x by linarith)
    exact (le_abs_self _).trans h
  have hsmall : (Chebyshev.psi - Chebyshev.theta) =o[atTop] (fun x : ℝ => x) :=
    hdiff.trans_isLittleO (by
      simpa only [mul_assoc] using sqrt_mul_log_isLittleO.const_mul_left (2 : ℝ))
  have h := chebyshevPsi_asymptotic.sub_isLittleO hsmall
  simpa only [sub_sub_cancel] using h

theorem chebyshevTheta_div_self_limit :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  apply (isEquivalent_iff_tendsto_one ?_).mp chebyshevTheta_asymptotic
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact hx.ne'

end PiIrrationality
