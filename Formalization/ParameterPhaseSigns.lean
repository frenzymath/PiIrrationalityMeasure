import Formalization.ArcTransform
import Formalization.PhaseSignPattern
import Formalization.ParameterContour

/-! Persistence of all seven strict monomial coefficient signs in (6.50). -/

namespace PiIrrationality

open Filter Polynomial
open scoped Topology ContDiff

noncomputable def parameterArcPolynomial (p : ℝ × ℝ) : Polynomial ℝ :=
  parameterPhasePolynomial p (parameterSaddleEta p)

theorem parameterArcPolynomial_candidate :
    parameterArcPolynomial candidate = C ((125 : ℝ) / 557) *
      phaseTransformedPolynomial saddleEta := by
  rw [parameterArcPolynomial, parameterSaddleEta_candidate, parameterPhasePolynomial_candidate]

theorem parameterArcPolynomial_degree_le (p : ℝ × ℝ) :
    (parameterArcPolynomial p).natDegree ≤ 6 := parameterPhasePolynomial_degree_le _ _

theorem analyticAt_parameterArcPolynomial_coeff (k : ℕ) :
    AnalyticAt ℝ (fun p => (parameterArcPolynomial p).coeff k) candidate := by
  have hm : ContDiffAt ℝ ω (fun p : ℝ × ℝ => (p, parameterSaddleEta p)) candidate :=
    contDiffAt_id.prodMk analyticAt_parameterSaddleEta.contDiffAt
  exact ((contDiff_parameterPhasePolynomial_coeff k).contDiffAt.comp candidate hm).analyticAt

theorem parameterArcPolynomial_signs_candidate :
    PhaseCoefficientSigns (parameterArcPolynomial candidate) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ :=
    phase_transformed_signs saddleEta_gt_nine_tenths saddleEta_lt_one
  unfold PhaseCoefficientSigns
  rw [parameterArcPolynomial_candidate]
  simp only [Polynomial.coeff_C_mul, phaseTransformedPolynomial_coeff_zero,
    phaseTransformedPolynomial_coeff_one, phaseTransformedPolynomial_coeff_two,
    phaseTransformedPolynomial_coeff_three, phaseTransformedPolynomial_coeff_four,
    phaseTransformedPolynomial_coeff_five, phaseTransformedPolynomial_coeff_six]
  exact ⟨mul_pos (by norm_num) h0, mul_pos (by norm_num) h1,
    mul_pos (by norm_num) h2, mul_pos (by norm_num) h3,
    mul_neg_of_pos_of_neg (by norm_num) h4, mul_neg_of_pos_of_neg (by norm_num) h5,
    mul_neg_of_pos_of_neg (by norm_num) h6⟩

theorem parameterArcPolynomial_signs_near_candidate : ∀ᶠ p in 𝓝 candidate,
    PhaseCoefficientSigns (parameterArcPolynomial p) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := parameterArcPolynomial_signs_candidate
  exact ((analyticAt_parameterArcPolynomial_coeff 0).continuousAt.eventually_const_lt h0).and
    (((analyticAt_parameterArcPolynomial_coeff 1).continuousAt.eventually_const_lt h1).and
      (((analyticAt_parameterArcPolynomial_coeff 2).continuousAt.eventually_const_lt h2).and
        (((analyticAt_parameterArcPolynomial_coeff 3).continuousAt.eventually_const_lt h3).and
          (((analyticAt_parameterArcPolynomial_coeff 4).continuousAt.eventually_lt_const h4).and
            (((analyticAt_parameterArcPolynomial_coeff 5).continuousAt.eventually_lt_const h5).and
              ((analyticAt_parameterArcPolynomial_coeff 6).continuousAt.eventually_lt_const h6))))))

theorem parameterArcPolynomial_root_count_near_candidate : ∀ᶠ p in 𝓝 candidate,
    (parameterArcPolynomial p).natDegree = 6 ∧
    (parameterArcPolynomial p).signVariations = 1 ∧
    (parameterArcPolynomial p).roots.countP (0 < ·) ≤ 1 := by
  filter_upwards [parameterArcPolynomial_signs_near_candidate] with p hp
  have hd := parameterArcPolynomial_degree_le p
  exact ⟨hp.natDegree hd, hp.signVariations hd, hp.positive_root_count hd⟩

end PiIrrationality
