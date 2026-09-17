import Formalization.PrimeSavingAsymptotic
import Formalization.NormalizedCoefficient
import Formalization.Normalization

/-! Actual denominator and normalization growth, culminating in equation (3.27). -/

namespace PiIrrationality

open Filter
open scoped Topology

theorem lcmRange_log_eq_psi (n : ℕ) :
    Real.log (lcmRange n : ℝ) = Chebyshev.psi (n : ℝ) := by
  exact (Chebyshev.psi_eq_log_lcmUpto n).symm

theorem lcmRange_log_mul_limit (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℕ => Real.log (lcmRange (d * n) : ℝ) / (n : ℝ))
      atTop (𝓝 (d : ℝ)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hpsi : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) := by
    apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).mp chebyshevPsi_asymptotic
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact hx.ne'
  have hs : Tendsto (fun n : ℕ =>
      Chebyshev.psi ((d : ℝ) * (n : ℝ)) / ((d : ℝ) * (n : ℝ)) * (d : ℝ))
      atTop (𝓝 (d : ℝ)) := by
    simpa only [Function.comp_def, one_mul] using
      (hpsi.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hd')).mul_const (d : ℝ)
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [lcmRange_log_eq_psi, Nat.cast_mul]
  field_simp

theorem reducedLcm_real_pos (n : ℕ) : (0 : ℝ) < (reducedLcm n : ℝ) := by
  have hl : 0 < lcmRange (7430 * n) := Nat.lcmUpto_pos _
  have hp := Phi_pos n
  simp only [reducedLcm, Rat.cast_div, Rat.cast_natCast]
  apply div_pos <;> assumption_mod_cast

theorem reducedLcm_log_formula (n : ℕ) :
    Real.log (reducedLcm n : ℝ) =
      Real.log (lcmRange (7430 * n) : ℝ) - Real.log (Phi n : ℝ) := by
  have hl : (lcmRange (7430 * n) : ℝ) ≠ 0 := by
    exact_mod_cast (show lcmRange (7430 * n) ≠ 0 from Nat.lcmUpto_ne_zero _)
  have hp : (Phi n : ℝ) ≠ 0 := by exact_mod_cast (Phi_pos n).ne'
  simp only [reducedLcm, Rat.cast_div, Rat.cast_natCast]
  exact Real.log_div hl hp

theorem reducedLcm_log_limit :
    Tendsto (fun n : ℕ => Real.log (reducedLcm n : ℝ) / (n : ℝ))
      atTop (𝓝 (7430 - primeSavingSeries)) := by
  have h := (lcmRange_log_mul_limit 7430 (by norm_num)).sub Phi_log_limit
  simpa only [Nat.cast_ofNat, reducedLcm_log_formula, sub_div] using h

theorem normalizationMultiplier_real_pos (n : ℕ) :
    (0 : ℝ) < (normalizationMultiplier n : ℝ) := by
  simp only [normalizationMultiplier, Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat]
  exact mul_pos (zpow_pos (by norm_num) _) (reducedLcm_real_pos n)

theorem normalizationMultiplier_log_formula (n : ℕ) :
    Real.log (normalizationMultiplier n : ℝ) =
      (4 - 4645 * (n : ℝ)) * Real.log 2 + Real.log (reducedLcm n : ℝ) := by
  simp only [normalizationMultiplier, Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat]
  rw [Real.log_mul (ne_of_gt (zpow_pos (by norm_num : (0 : ℝ) < 2) _))
    (reducedLcm_real_pos n).ne', Real.log_zpow]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]

theorem normalizationMultiplier_log_limit :
    Tendsto (fun n : ℕ => Real.log (normalizationMultiplier n : ℝ) / (n : ℝ))
      atTop (𝓝 (7430 - 4645 * Real.log 2 - primeSavingSeries)) := by
  have hz : Tendsto (fun n : ℕ => (4 * Real.log 2) / (n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun n : ℕ => (4 * Real.log 2) / (n : ℝ) - 4645 * Real.log 2 +
      Real.log (reducedLcm n : ℝ) / (n : ℝ))
      atTop (𝓝 (7430 - 4645 * Real.log 2 - primeSavingSeries)) := by
    have h := (hz.sub_const (4645 * Real.log 2)).add reducedLcm_log_limit
    have heq : (0 - 4645 * Real.log 2) + (7430 - primeSavingSeries) =
        7430 - 4645 * Real.log 2 - primeSavingSeries := by ring
    rw [heq] at h
    exact h
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [normalizationMultiplier_log_formula]
  field_simp

/-- Equation (3.27) for the actual multiplier of Proposition 2.7. -/
theorem normalizationCost_limit :
    Tendsto (fun n : ℕ => Real.log (normalizationMultiplier n : ℝ) / (5570 * (n : ℝ)))
      atTop (𝓝 (normalizationCost primeSavingSeries)) := by
  rw [normalizationCost_explicit]
  simpa only [div_div, mul_comm] using normalizationMultiplier_log_limit.div_const 5570

end PiIrrationality
