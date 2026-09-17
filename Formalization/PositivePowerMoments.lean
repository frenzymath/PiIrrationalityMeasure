import Formalization.PositivePowerProbability
import Formalization.PositivePowerMean

/-! The actual moments of arbitrary positive-power coefficient laws. -/

namespace PiIrrationality.PositivePower

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable (u v : ℕ) {d : ℕ} (hd : 0 < d)

theorem law_hasDerivAt_cgf {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {t : ℝ} (ht : x * Real.exp t < 1) :
    HasDerivAt (cgf (fun k : ℕ => (k : ℝ)) (law u v hd x hx0.le hx1 1).toMeasure)
      (mean u v d (x * Real.exp t)) t := by
  have hy : 0 < x * Real.exp t := mul_pos hx0 (Real.exp_pos t)
  have hS := (realValue_pos u v d hx0.le hx1).ne'
  have hSy := (realValue_pos u v d hy.le ht).ne'
  have heq : cgf (fun k : ℕ => (k : ℝ)) (law u v hd x hx0.le hx1 1).toMeasure =ᶠ[𝓝 t]
      (fun s => Real.log (realValue u v d (x * Real.exp s) / realValue u v d x)) := by
    have hc : Continuous (fun s : ℝ => x * Real.exp s) := by fun_prop
    filter_upwards [hc.continuousAt.eventually (gt_mem_nhds ht)] with s hs
    rw [cgf, law_mgf u v hd hx0.le hx1 s hs]
  apply heq.symm.hasDerivAt_iff.mp
  have hcomp : HasDerivAt (fun s : ℝ => realValue u v d (x * Real.exp s))
      (deriv (realValue u v d) (x * Real.exp t) * (x * Real.exp t)) t := by
    simpa only [Function.comp_def] using
      (realValue_differentiableAt u v d ht).hasDerivAt.comp t
        ((Real.hasDerivAt_exp t).const_mul x)
  have h := (hcomp.div_const (realValue u v d x)).log (div_ne_zero hSy hS)
  convert! h using 1
  rw [mean_eq_logDeriv u v d hy.le ht, logDeriv_apply]
  field_simp

theorem law_expectation {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∫ k : ℕ, (k : ℝ) ∂(law u v hd x hx0.le hx1 1).toMeasure = mean u v d x := by
  have ht : x * Real.exp 0 < 1 := by simpa using hx1
  have h := (law_hasDerivAt_cgf u v hd hx0 hx1 ht).deriv
  rw [deriv_cgf_zero (law_interior_integrableExpSet u v hd hx0.le hx1 ht)] at h
  simpa using h

theorem law_cgf_second_derivative {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    iteratedDeriv 2 (cgf (fun k : ℕ => (k : ℝ))
      (law u v hd x hx0.le hx1 1).toMeasure) 0 = saddleVariance u v d x := by
  have heq : deriv (cgf (fun k : ℕ => (k : ℝ)) (law u v hd x hx0.le hx1 1).toMeasure)
      =ᶠ[𝓝 0] fun t => mean u v d (x * Real.exp t) := by
    have hc : Continuous (fun t : ℝ => x * Real.exp t) := by fun_prop
    have ht : x * Real.exp 0 < 1 := by simpa using hx1
    filter_upwards [hc.continuousAt.eventually (gt_mem_nhds ht)] with t ht
    exact (law_hasDerivAt_cgf u v hd hx0 hx1 ht).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, heq.deriv_eq]
  have he : HasDerivAt (fun t : ℝ => x * Real.exp t) x 0 := by
    simpa only [Real.exp_zero, mul_one] using (Real.hasDerivAt_exp 0).const_mul x
  have hd0 : HasDerivAt (mean u v d) (meanPrime u v d x) (x * Real.exp 0) := by
    simpa only [Real.exp_zero, mul_one] using mean_hasDerivAt u v d hx0.le hx1
  have h := hd0.comp 0 he
  simpa only [Function.comp_def, Real.exp_zero, mul_one, saddleVariance,
    (mean_hasDerivAt u v d hx0.le hx1).deriv, mul_comm] using h.deriv

theorem law_variance {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    variance (fun k : ℕ => (k : ℝ)) (law u v hd x hx0.le hx1 1).toMeasure =
      saddleVariance u v d x := by
  have ht : x * Real.exp 0 < 1 := by simpa using hx1
  have h0 := law_interior_integrableExpSet u v hd hx0.le hx1 ht
  rw [← law_cgf_second_derivative u v hd hx0 hx1, iteratedDeriv_two_cgf h0,
    variance_eq_sub (memLp_of_mem_interior_integrableExpSet h0 2)]
  simp [deriv_cgf_zero h0]

theorem law_variance_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < variance (fun k : ℕ => (k : ℝ)) (law u v hd x hx0.le hx1 1).toMeasure := by
  rw [law_variance u v hd hx0 hx1]
  exact saddleVariance_pos u v hd hx0 hx1

end PiIrrationality.PositivePower
