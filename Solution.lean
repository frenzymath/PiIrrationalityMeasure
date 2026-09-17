import Formalization.PiMeasureTheorem
import Formalization.LocalOptimality
import Formalization.ParameterSaddleRoots

/-!
Proofs of the three statements in `Challenge.lean`, without importing it.
The statement definitions are repeated in their own namespace, in the same
order, so that Comparator also compares Lean's generated auxiliary constants.
The bridge below identifies them with the existing proof development.
-/

namespace PiIrrationalityChallenge

def IrrationalityMeasureAtMost (theta mu : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps →
    ∃ q0 : ℕ, ∀ p : ℤ, ∀ q : ℕ,
      q0 ≤ q → 0 < q →
        |theta - (p : ℝ) / (q : ℝ)| > (q : ℝ) ^ (-mu - eps)

noncomputable def IrrationalityMeasure (theta : ℝ) : ℝ :=
  sInf {mu : ℝ | IrrationalityMeasureAtMost theta mu}

def Admissible (p : ℝ × ℝ) : Prop :=
  p.1 + p.2 > 1 ∧
  2 * p.2 > 1 ∧
  7 * p.2 < 5 ∧
  2 * p.1 + 4 * p.2 - 2 > 1

def StrictLocalMinimizer (f : ℝ × ℝ → ℝ) (domain : ℝ × ℝ → Prop)
    (p0 : ℝ × ℝ) : Prop :=
  ∃ delta : ℝ, 0 < delta ∧
    ∀ p : ℝ × ℝ, domain p → p ≠ p0 →
      ‖p - p0‖ < delta → f p0 < f p

noncomputable def candidate : ℝ × ℝ :=
  ((1857 : ℝ) / 5570, (1857 : ℝ) / 2785)

noncomputable def savingChi (X Y Z : ℝ) : ℝ :=
  if Int.fract (X + 1 / 2) + 2 * Int.fract Y < Int.fract Z then 1 else 0

noncomputable def savingDensity (A B C t : ℝ) : ℝ :=
  savingChi (A * t) (B * t) (C * t) / t ^ 2

noncomputable def savingOmega (A B C : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), savingDensity A B C t

noncomputable def savingPhi (p : ℝ × ℝ) : ℝ := savingOmega p.1 p.2 1

noncomputable def parameterSmoothCost (p : ℝ × ℝ) : ℝ :=
  2 * p.1 + 4 * p.2 - 2 - (5 * p.2 - 5 / 2) * Real.log 2

noncomputable def parameterCost (p : ℝ × ℝ) : ℝ :=
  parameterSmoothCost p - savingPhi p

noncomputable def complexPhase (alpha beta : ℝ) (y : ℂ) : ℝ :=
  alpha * Real.log ‖y‖ + beta * Real.log ‖y ^ 2 + 6 * y + 25‖ -
    Real.log ‖25 - y‖

noncomputable def parameterStationary (p : ℝ × ℝ) (y : ℝ) : ℝ :=
  (p.1 + 2 * p.2 - 1) * y ^ 3 - (19 * p.1 + 44 * p.2 + 6) * y ^ 2 -
    (125 * p.1 + 150 * p.2 + 25) * y - 625 * p.1

noncomputable def parameterStationaryComplex (p : ℝ × ℝ) (z : ℂ) : ℂ :=
  ((p.1 + 2 * p.2 - 1 : ℝ) : ℂ) * z ^ 3 -
    ((19 * p.1 + 44 * p.2 + 6 : ℝ) : ℂ) * z ^ 2 -
    ((125 * p.1 + 150 * p.2 + 25 : ℝ) : ℂ) * z - ((625 * p.1 : ℝ) : ℂ)

noncomputable def paperRealSaddle (p : ℝ × ℝ) : ℝ :=
  Classical.epsilon (fun y : ℝ => 25 < y ∧ parameterStationary p y = 0)

noncomputable def paperComplexSaddle (p : ℝ × ℝ) : ℂ :=
  Classical.epsilon (fun z : ℂ => 0 < z.im ∧ parameterStationaryComplex p z = 0)

noncomputable def paperCoefficientRate (p : ℝ × ℝ) : ℝ :=
  complexPhase p.1 p.2 (paperRealSaddle p : ℂ)

noncomputable def paperIntegralRate (p : ℝ × ℝ) : ℝ :=
  complexPhase p.1 p.2 (paperComplexSaddle p)

noncomputable def paperAuxiliaryBound (p : ℝ × ℝ) : ℝ :=
  1 + (paperCoefficientRate p + parameterCost p) /
    (-paperIntegralRate p - parameterCost p)

open PiIrrationality Filter
open scoped Topology

/-- Root existence and uniqueness identify the statement's saddles locally. -/
theorem paperSaddles_eventuallyEq : ∀ᶠ p in 𝓝 candidate,
    paperRealSaddle p = parameterRealSaddle p ∧
      paperComplexSaddle p = parameterComplexSaddle p := by
  filter_upwards [parameterRealSaddle_near_candidate,
    parameterComplexSaddle_near_candidate, parameterSaddle_unique_near_candidate]
    with p hr hc hu
  have hrSpec : 25 < paperRealSaddle p ∧ parameterStationary p (paperRealSaddle p) = 0 :=
    Classical.epsilon_spec (p := fun y : ℝ => 25 < y ∧ parameterStationary p y = 0)
      ⟨parameterRealSaddle p, hr.2, hr.1⟩
  have hcSpec : 0 < (paperComplexSaddle p).im ∧
      parameterStationaryComplex p (paperComplexSaddle p) = 0 :=
    Classical.epsilon_spec (p := fun z : ℂ =>
      0 < z.im ∧ parameterStationaryComplex p z = 0)
      ⟨parameterComplexSaddle p, hc.2, hc.1⟩
  exact ⟨(hu.1 _).mp hrSpec.2, hu.2 _ hcSpec.2 hcSpec.1⟩

theorem paperAuxiliaryBound_eventuallyEq :
    paperAuxiliaryBound =ᶠ[𝓝 candidate] parameterAuxiliaryBound := by
  filter_upwards [paperSaddles_eventuallyEq] with p hp
  simp only [paperAuxiliaryBound, paperCoefficientRate, paperIntegralRate,
    parameterAuxiliaryBound, AuxiliaryBound, parameterCoefficientRate,
    parameterIntegralRate, hp.1, hp.2]
  rfl

/-- Local equality transfers the proved minimum to the independent statement. -/
theorem paperAuxiliaryBound_strictLocalMinimizer :
    StrictLocalMinimizer paperAuxiliaryBound Admissible candidate := by
  have he := paperAuxiliaryBound_eventuallyEq
  have he0 : paperAuxiliaryBound candidate = parameterAuxiliaryBound candidate :=
    he.self_of_nhds
  obtain ⟨r, hr, hmin⟩ := parameterAuxiliaryBound_strictLocalMinimizer
  obtain ⟨s, hs, heq⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨min r s, lt_min hr hs, ?_⟩
  intro p hp hne hdist
  have hps : dist p candidate < s := by
    simpa only [dist_eq_norm] using hdist.trans_le (min_le_right r s)
  rw [he0, heq hps]
  exact hmin p hp hne (hdist.trans_le (min_le_left r s))

end PiIrrationalityChallenge

open PiIrrationalityChallenge

theorem comparator_theorem11 :
    IrrationalityMeasure Real.pi < (7101862832357 : ℝ) / 10 ^ 12 := by
  exact PiIrrationality.theorem11_proof

theorem comparator_pi_rational_approximation_bound :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ q0 : ℕ, ∀ p : ℤ, ∀ q : ℕ, q0 ≤ q → 0 < q →
      |Real.pi - (p : ℝ) / (q : ℝ)| >
        (q : ℝ) ^ (-(7101862832357 : ℝ) / 10 ^ 12 - epsilon) := by
  have h := PiIrrationality.pi_irrationalityMeasureAtMost.mono
    PiIrrationality.paperAuxiliaryValue_lt_cutoff.le
  simpa only [PiIrrationality.IrrationalityMeasureAtMost, neg_div] using h

theorem comparator_theorem12 :
    StrictLocalMinimizer paperAuxiliaryBound Admissible candidate := by
  exact paperAuxiliaryBound_strictLocalMinimizer
