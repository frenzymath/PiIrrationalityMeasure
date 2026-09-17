import Formalization.ParameterRates

/-! The analytic coefficient-saddle coordinate and its Mobius correspondence (6.67). -/

namespace PiIrrationality

open Filter
open scoped Topology ContDiff

noncomputable def realSaddleCoordinate (y : ℝ) : ℝ :=
  (Real.sqrt (y / 25) - 1) / (Real.sqrt (y / 25) + 1)

theorem realSaddleCoordinate_mem {y : ℝ} (hy : 25 < y) :
    realSaddleCoordinate y ∈ Set.Ioo 0 1 := by
  have hs : 1 < Real.sqrt (y / 25) := Real.lt_sqrt_of_sq_lt (by linarith)
  have hd : 0 < Real.sqrt (y / 25) + 1 := by positivity
  exact ⟨div_pos (by linarith) hd, (div_lt_iff₀ hd).mpr (by linarith)⟩

theorem realSaddleCoordinate_mobius {y : ℝ} (hy : 25 < y) :
    y = 25 * (1 + realSaddleCoordinate y) ^ 2 / (1 - realSaddleCoordinate y) ^ 2 := by
  have hs : Real.sqrt (y / 25) ^ 2 = y / 25 := Real.sq_sqrt (by linarith)
  have hd : Real.sqrt (y / 25) + 1 ≠ 0 := by positivity
  unfold realSaddleCoordinate
  field_simp [hd]
  nlinarith only [hs]

theorem realSaddleCoordinate_of_mobius {z : ℝ} (hz : z ∈ Set.Ioo 0 1) :
    realSaddleCoordinate (25 * (1 + z) ^ 2 / (1 - z) ^ 2) = z := by
  have hd : 0 < 1 - z := by linarith [hz.2]
  have hq : 0 ≤ (1 + z) / (1 - z) := div_nonneg (by linarith [hz.1]) hd.le
  have hs : Real.sqrt ((25 * (1 + z) ^ 2 / (1 - z) ^ 2) / 25) =
      (1 + z) / (1 - z) := by
    rw [show (25 * (1 + z) ^ 2 / (1 - z) ^ 2) / 25 =
      ((1 + z) / (1 - z)) ^ 2 by rw [div_pow]; ring]
    exact Real.sqrt_sq hq
  unfold realSaddleCoordinate
  rw [hs]
  field_simp
  ring

theorem realSaddleCoordinate_unique {y z : ℝ} (hy : 25 < y) (hz : z ∈ Set.Ioo 0 1) :
    y = 25 * (1 + z) ^ 2 / (1 - z) ^ 2 ↔ z = realSaddleCoordinate y := by
  constructor
  · intro h
    rw [h, realSaddleCoordinate_of_mobius hz]
  · rintro rfl
    exact realSaddleCoordinate_mobius hy

noncomputable def parameterCoefficientSaddle (p : ℝ × ℝ) : ℝ :=
  realSaddleCoordinate (parameterRealSaddle p)

theorem parameterCoefficientSaddle_candidate :
    parameterCoefficientSaddle candidate = coefficientSaddle := by
  rw [parameterCoefficientSaddle, parameterRealSaddle_candidate,
    coefficientSaddle_real_root, realSaddleCoordinate_of_mobius coefficientSaddle_mem]

theorem analyticAt_parameterCoefficientSaddle :
    AnalyticAt ℝ parameterCoefficientSaddle candidate := by
  have hc := analyticAt_parameterRealSaddle.contDiffAt (n := ω)
  have hs : ContDiffAt ℝ ω (fun p => Real.sqrt (parameterRealSaddle p / 25)) candidate :=
    (hc.div_const 25).sqrt (by
      rw [parameterRealSaddle_candidate]
      exact div_ne_zero stationaryRoot_pos.ne' (by norm_num))
  exact ((hs.sub contDiffAt_const).div (hs.add contDiffAt_const) (by positivity)).analyticAt

theorem parameterCoefficientSaddle_near_candidate : ∀ᶠ p in 𝓝 candidate,
    parameterCoefficientSaddle p ∈ Set.Ioo 0 1 ∧
    parameterRealSaddle p = 25 * (1 + parameterCoefficientSaddle p) ^ 2 /
      (1 - parameterCoefficientSaddle p) ^ 2 ∧
    ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      parameterRealSaddle p = 25 * (1 + z) ^ 2 / (1 - z) ^ 2 →
        z = parameterCoefficientSaddle p := by
  filter_upwards [parameterRealSaddle_near_candidate] with p hp
  exact ⟨realSaddleCoordinate_mem hp.2, realSaddleCoordinate_mobius hp.2,
    fun z hz => (realSaddleCoordinate_unique hp.2 hz).mp⟩

theorem parameterCoefficientRate_mobius_near_candidate : ∀ᶠ p in 𝓝 candidate,
    parameterCoefficientRate p =
      (p.1 + p.2 - 1) * Real.log 25 + (4 * p.2 - 2) * Real.log 2 +
      2 * p.1 * Real.log (1 + parameterCoefficientSaddle p) +
      p.2 * Real.log (PReal (parameterCoefficientSaddle p)) +
      (-2 * p.1 - 4 * p.2 + 2) * Real.log (1 - parameterCoefficientSaddle p) -
      Real.log (parameterCoefficientSaddle p) := by
  filter_upwards [parameterCoefficientSaddle_near_candidate] with p hp
  unfold parameterCoefficientRate
  rw [hp.2.1]
  exact real_phase_mobius p.1 p.2 hp.1.1 hp.1.2

end PiIrrationality
