import Formalization.BinetSymmetricIntegral
import Formalization.DigammaBinet

/-! The integral form of Binet's digamma formula printed before (3.21). -/

namespace PiIrrationality

open MeasureTheory Set

theorem binetPairKernel_integral_norm {y a : ℝ} :
    (∫ u : ℝ in Ioi 0, ‖binetPairKernel y a u‖) =
      ∫ u : ℝ in Ioi 0, binetPairKernel y a u := by
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  exact Real.norm_of_nonneg (binetPairKernel_nonneg hu.le)

theorem summable_binetPairKernel_integral_norm {y : ℝ} (hy : 0 < y) :
    Summable (fun n : ℕ => ∫ u : ℝ in Ioi 0, ‖binetPairKernel y (binetPole n) u‖) := by
  simp only [binetPairKernel_integral_norm]
  have hsum := (hasSum_binetMoment (by norm_num : 0 < (1 : ℕ))).summable.div_const (y ^ 2)
  simp only [Nat.reduceMul] at hsum
  apply Summable.of_nonneg_of_le
    (fun n => integral_nonneg_of_ae ?_)
    (fun n => integral_binetPairKernel_bound hy (binetPole_pos n)) hsum
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  exact binetPairKernel_nonneg hu.le

theorem summable_binetPairKernel_integral_norm_swap {y : ℝ} (hy : 0 < y) :
    Summable (fun n : ℕ => ∫ u : ℝ in Ioi 0, ‖binetPairKernel (binetPole n) y u‖) := by
  simp only [binetPairKernel_integral_norm]
  simpa only [binetPairKernel_integral_norm, integral_binetPairKernel_symm hy (binetPole_pos _)]
    using summable_binetPairKernel_integral_norm hy

theorem hasSum_binetLaplace_integrals {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => ∫ u : ℝ in Ioi 0, binetPairKernel y (binetPole n) u)
      (binetLaplace y) := by
  have h := hasSum_integral_of_summable_integral_norm
    (fun n => integrableOn_binetPairKernel hy (binetPole_pos n))
    (summable_binetPairKernel_integral_norm hy)
  convert! h using 1
  unfold binetLaplace
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  have hs := (hasSum_binetKernel hu).mul_left (Real.exp (-(y * u)))
  exact hs.tsum_eq.symm

theorem hasSum_binetExponentials {u : ℝ} (hu : 0 < u) :
    HasSum (fun n : ℕ => Real.exp (-(binetPole n * u)))
      (1 / (Real.exp (2 * Real.pi * u) - 1)) := by
  have hpos : 0 < 2 * Real.pi * u := by positivity
  have hlt : ‖Real.exp (-(2 * Real.pi * u))‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_lt_one_iff]
    linarith
  have h := (hasSum_geometric_of_norm_lt_one hlt).mul_left (Real.exp (-(2 * Real.pi * u)))
  convert! h using 1
  · ext n
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    unfold binetPole
    ring
  · rw [Real.exp_neg]
    have he : Real.exp (2 * Real.pi * u) - 1 ≠ 0 :=
      (sub_pos.mpr (Real.one_lt_exp_iff.mpr hpos)).ne'
    field_simp [he, (Real.exp_pos _).ne']
    <;> ring

theorem binetLaplace_second_integral {y : ℝ} (hy : 0 < y) :
    binetLaplace y =
      2 * ∫ t : ℝ in Ioi 0, t / ((t ^ 2 + y ^ 2) * (Real.exp (2 * Real.pi * t) - 1)) := by
  have h := hasSum_integral_of_summable_integral_norm
    (fun n => integrableOn_binetPairKernel (binetPole_pos n) hy)
    (summable_binetPairKernel_integral_norm_swap hy)
  have heq : (fun n : ℕ => ∫ u : ℝ in Ioi 0, binetPairKernel (binetPole n) y u) =
      (fun n : ℕ => ∫ u : ℝ in Ioi 0, binetPairKernel y (binetPole n) u) := by
    ext n
    exact integral_binetPairKernel_symm (binetPole_pos n) hy
  rw [heq] at h
  rw [(hasSum_binetLaplace_integrals hy).unique h, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have hs := (hasSum_binetExponentials ht).mul_left (2 * t / (t ^ 2 + y ^ 2))
  have he (n : ℕ) : (2 * t / (t ^ 2 + y ^ 2)) * Real.exp (-(binetPole n * t)) =
      binetPairKernel (binetPole n) y t := by unfold binetPairKernel; ring
  simp_rw [he] at hs
  rw [hs.tsum_eq]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem integrableOn_binetSecondKernel {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun t : ℝ =>
      t / ((t ^ 2 + y ^ 2) * (Real.exp (2 * Real.pi * t) - 1))) (Ioi 0) := by
  by_contra h
  have he := binetLaplace_second_integral hy
  rw [integral_undef h, mul_zero] at he
  exact (binetLaplace_pos hy).ne' he

theorem realDigamma_binetSecondFormula {y : ℝ} (hy : 0 < y) :
    realDigamma y = Real.log y - 1 / (2 * y) -
      2 * ∫ t : ℝ in Ioi 0, t / ((t ^ 2 + y ^ 2) * (Real.exp (2 * Real.pi * t) - 1)) := by
  rw [realDigamma_binetLaplace hy, binetLaplace_second_integral hy]

end PiIrrationality
