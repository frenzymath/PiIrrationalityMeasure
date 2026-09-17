import Formalization.ParameterPhaseSigns
import Formalization.GeneralArcCritical
import Formalization.ParameterPhaseCritical

/-! The actual saddle remains the unique global phase maximum near the candidate. -/

namespace PiIrrationality

open Filter
open scoped Topology

theorem parameterArcPhase_unique_critical_near_candidate : ∀ᶠ p in 𝓝 candidate,
    ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      deriv (fun t => complexPhase p.1 p.2 (gammaPath (parameterSaddleEta p) t)) x = 0 ↔
        x = parameterSaddleLambda p := by
  filter_upwards [parameterArcPolynomial_signs_near_candidate, parameterContour_near_candidate,
    parameterArcPhase_stationary_near_candidate] with p hs hp hd
  have hl : parameterSaddleLambda p ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨by linarith [hp.2.2.1], by linarith [hp.2.2.2.1]⟩
  have hroot := (general_complexPhase_arc_deriv_zero_iff hp.1 hl).mp hd.deriv
  intro x hx
  constructor
  · intro hx0
    exact arcClearedDerivative_root_unique hs hx hl
      ((general_complexPhase_arc_deriv_zero_iff hp.1 hx).mp hx0) hroot
  · rintro rfl
    exact hd.deriv

theorem parameterArcPhase_strict_maximum_near_candidate : ∀ᶠ p in 𝓝 candidate,
    ∀ x ∈ Set.Ioo (0 : ℝ) 1, x ≠ parameterSaddleLambda p →
      complexPhase p.1 p.2 (gammaPath (parameterSaddleEta p) x) < parameterIntegralRate p := by
  have ha : ∀ᶠ p : ℝ × ℝ in 𝓝 candidate, 0 < p.1 :=
    continuous_fst.continuousAt.eventually_const_lt (by norm_num [candidate])
  have hb : ∀ᶠ p : ℝ × ℝ in 𝓝 candidate, 0 < p.2 :=
    continuous_snd.continuousAt.eventually_const_lt (by norm_num [candidate])
  filter_upwards [ha, hb, parameterArcPolynomial_signs_near_candidate,
    parameterContour_near_candidate, parameterArcPhase_stationary_near_candidate]
    with p ha hb hs hp hd
  have hl : parameterSaddleLambda p ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨by linarith [hp.2.2.1], by linarith [hp.2.2.2.1]⟩
  have hroot := (general_complexPhase_arc_deriv_zero_iff hp.1 hl).mp hd.deriv
  intro x hx hne
  have hmax := general_complexPhase_arc_strict_max hs ha hb hp.1 hl hroot x hx hne
  rw [hp.2.2.2.2] at hmax
  exact hmax

theorem parameterArcPhase_maximum_near_candidate : ∀ᶠ p in 𝓝 candidate,
    ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      complexPhase p.1 p.2 (gammaPath (parameterSaddleEta p) x) ≤ parameterIntegralRate p ∧
      (complexPhase p.1 p.2 (gammaPath (parameterSaddleEta p) x) = parameterIntegralRate p ↔
        x = parameterSaddleLambda p) := by
  filter_upwards [parameterArcPhase_strict_maximum_near_candidate,
    parameterContour_near_candidate] with p hmax hp
  intro x hx
  by_cases he : x = parameterSaddleLambda p
  · rw [he, hp.2.2.2.2]
    simp [parameterIntegralRate]
  · have hlt := hmax x hx he
    exact ⟨hlt.le, iff_of_false hlt.ne he⟩

end PiIrrationality
