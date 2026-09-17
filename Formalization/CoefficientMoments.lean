import Formalization.CoefficientProbability
import Formalization.CoefficientMean

/-! Actual expectation and variance of the tilted law, equation (4.9). -/

namespace PiIrrationality

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem pmf_nat_integrable_of_summable (p : PMF ℕ) (f : ℕ → ℝ)
    (hf : Summable (fun k => (p k).toReal * ‖f k‖)) : Integrable f p.toMeasure := by
  rw [← Measure.sum_smul_dirac p.toMeasure]
  apply integrable_sum_dirac
  · intro k
    exact measure_ne_top _ _
  · simpa only [PMF.toMeasure_apply_singleton p _ (MeasurableSet.singleton _)] using hf

theorem coefficientLaw_integrable_exp {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (t : ℝ) (ht : x * Real.exp t < 1) :
    Integrable (fun k : ℕ => Real.exp (t * (k : ℝ))) (coefficientLaw x hx0 hx1 1).toMeasure := by
  apply pmf_nat_integrable_of_summable
  simpa only [coefficientLaw_toReal, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    mul_comm t] using (coefficientProbability_exponential_sum hx0 1 t ht).summable

theorem coefficientLaw_mgf {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (t : ℝ) (ht : x * Real.exp t < 1) :
    mgf (fun k : ℕ => (k : ℝ)) (coefficientLaw x hx0 hx1 1).toMeasure t =
      SReal (x * Real.exp t) / SReal x := by
  rw [mgf, PMF.integral_eq_tsum _ _ (coefficientLaw_integrable_exp hx0 hx1 t ht)]
  simpa only [coefficientLaw_toReal, smul_eq_mul, mul_comm t, pow_one] using
    (coefficientProbability_exponential_sum hx0 1 t ht).tsum_eq

theorem coefficientLaw_interior_integrableExpSet {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    {t : ℝ} (ht : x * Real.exp t < 1) :
    t ∈ interior (integrableExpSet (fun k : ℕ => (k : ℝ))
      (coefficientLaw x hx0 hx1 1).toMeasure) := by
  apply mem_interior_iff_mem_nhds.mpr
  have hc : Continuous (fun s : ℝ => x * Real.exp s) := by fun_prop
  filter_upwards [hc.continuousAt.eventually (gt_mem_nhds ht)] with s hs
  exact coefficientLaw_integrable_exp hx0 hx1 s hs

theorem SReal_differentiableAt {x : ℝ} (hx1 : x < 1) : DifferentiableAt ℝ SReal x := by
  have h : 1 - x ≠ 0 := by linarith
  unfold SReal PReal
  fun_prop (disch := positivity)

theorem coefficientLaw_hasDerivAt_cgf {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {t : ℝ} (ht : x * Real.exp t < 1) :
    HasDerivAt (cgf (fun k : ℕ => (k : ℝ)) (coefficientLaw x hx0.le hx1 1).toMeasure)
      (coefficientMean (x * Real.exp t)) t := by
  have hy : 0 < x * Real.exp t := mul_pos hx0 (Real.exp_pos t)
  have hS := SReal_ne_zero hx0.le hx1
  have hSy := SReal_ne_zero hy.le ht
  have heq : cgf (fun k : ℕ => (k : ℝ)) (coefficientLaw x hx0.le hx1 1).toMeasure =ᶠ[𝓝 t]
      (fun s => Real.log (SReal (x * Real.exp s) / SReal x)) := by
    have hc : Continuous (fun s : ℝ => x * Real.exp s) := by fun_prop
    filter_upwards [hc.continuousAt.eventually (gt_mem_nhds ht)] with s hs
    rw [cgf, coefficientLaw_mgf hx0.le hx1 s hs]
  apply heq.symm.hasDerivAt_iff.mp
  have hcomp : HasDerivAt (fun s : ℝ => SReal (x * Real.exp s))
      (deriv SReal (x * Real.exp t) * (x * Real.exp t)) t := by
    simpa only [Function.comp_def] using (SReal_differentiableAt ht).hasDerivAt.comp t
      ((Real.hasDerivAt_exp t).const_mul x)
  have h := (hcomp.div_const (SReal x)).log (div_ne_zero hSy hS)
  convert! h using 1
  rw [coefficientMean_eq_logDeriv hy.le ht, logDeriv_apply]
  field_simp

theorem coefficientLaw_expectation {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∫ k : ℕ, (k : ℝ) ∂(coefficientLaw x hx0.le hx1 1).toMeasure = coefficientMean x := by
  have ht : x * Real.exp 0 < 1 := by simpa using hx1
  have hd := (coefficientLaw_hasDerivAt_cgf hx0 hx1 ht).deriv
  have h0 := coefficientLaw_interior_integrableExpSet hx0.le hx1 ht
  rw [deriv_cgf_zero h0] at hd
  simpa using hd

theorem coefficientLaw_cgf_second_derivative {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    iteratedDeriv 2 (cgf (fun k : ℕ => (k : ℝ)) (coefficientLaw x hx0.le hx1 1).toMeasure) 0 =
      x * deriv coefficientMean x := by
  have heq : deriv (cgf (fun k : ℕ => (k : ℝ)) (coefficientLaw x hx0.le hx1 1).toMeasure)
      =ᶠ[𝓝 0] fun t => coefficientMean (x * Real.exp t) := by
    have hc : Continuous (fun t : ℝ => x * Real.exp t) := by fun_prop
    have ht : x * Real.exp 0 < 1 := by simpa using hx1
    filter_upwards [hc.continuousAt.eventually (gt_mem_nhds ht)] with t ht
    exact (coefficientLaw_hasDerivAt_cgf hx0 hx1 ht).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, heq.deriv_eq]
  have he : HasDerivAt (fun t : ℝ => x * Real.exp t) x 0 := by
    simpa only [Real.exp_zero, mul_one] using (Real.hasDerivAt_exp 0).const_mul x
  have hd0 : HasDerivAt coefficientMean (coefficientMeanPrime x) (x * Real.exp 0) := by
    simpa only [Real.exp_zero, mul_one] using coefficientMean_hasDerivAt hx0.le hx1
  have hd := hd0.comp 0 he
  simpa only [Function.comp_def, Real.exp_zero, mul_one,
    (coefficientMean_hasDerivAt hx0.le hx1).deriv, mul_comm] using hd.deriv

theorem coefficientLaw_variance {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    variance (fun k : ℕ => (k : ℝ)) (coefficientLaw x hx0.le hx1 1).toMeasure =
      x * deriv coefficientMean x := by
  have ht : x * Real.exp 0 < 1 := by simpa using hx1
  have h0 := coefficientLaw_interior_integrableExpSet hx0.le hx1 ht
  rw [← coefficientLaw_cgf_second_derivative hx0 hx1, iteratedDeriv_two_cgf h0,
    variance_eq_sub (memLp_of_mem_interior_integrableExpSet h0 2)]
  simp [deriv_cgf_zero h0]

theorem coefficientLaw_variance_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < variance (fun k : ℕ => (k : ℝ)) (coefficientLaw x hx0.le hx1 1).toMeasure := by
  rw [coefficientLaw_variance hx0 hx1, (coefficientMean_hasDerivAt hx0.le hx1).deriv]
  exact mul_pos hx0 (coefficientMeanPrime_pos hx0.le hx1)

end PiIrrationality
