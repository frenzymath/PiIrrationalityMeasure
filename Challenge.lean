import Mathlib

/-!
# Main results of the pi irrationality-measure paper

This is the trusted statement for Comparator. It imports only Mathlib and
contains the definitions needed to read Theorems 1.1 and 1.2. The three proof
placeholders are intentional; the proofs are supplied by `Solution.lean`.

Parameters are (alpha, beta) = (A1 / 2, A2), as in (1.3). The saddle points
below are selected directly from the stationary cubic (6.7). Near `candidate`,
the real root above 25 and the root in the upper half-plane both exist and
are unique. The solution proves this local identification with the analytic
branches used in the development. No existence or regularity assumption is
left in the main theorem. Values outside that neighborhood do not affect it.
-/

namespace PiIrrationalityChallenge

/-- The eventual rational-approximation exponents in the introduction. -/
def IrrationalityMeasureAtMost (theta mu : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps →
    ∃ q0 : ℕ, ∀ p : ℤ, ∀ q : ℕ,
      q0 ≤ q → 0 < q →
        |theta - (p : ℝ) / (q : ℝ)| > (q : ℝ) ^ (-mu - eps)

noncomputable def IrrationalityMeasure (theta : ℝ) : ℝ :=
  sInf {mu : ℝ | IrrationalityMeasureAtMost theta mu}

/-- The open arithmetic chamber (1.4). -/
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

/-- The candidate (1.7), in normalized coordinates. -/
noncomputable def candidate : ℝ × ℝ :=
  ((1857 : ℝ) / 5570, (1857 : ℝ) / 2785)

/-- The fractional-part indicator and weighted saving integral (6.1)--(6.4). -/
noncomputable def savingChi (X Y Z : ℝ) : ℝ :=
  if Int.fract (X + 1 / 2) + 2 * Int.fract Y < Int.fract Z then 1 else 0

noncomputable def savingDensity (A B C t : ℝ) : ℝ :=
  savingChi (A * t) (B * t) (C * t) / t ^ 2

noncomputable def savingOmega (A B C : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), savingDensity A B C t

noncomputable def savingPhi (p : ℝ × ℝ) : ℝ := savingOmega p.1 p.2 1

/-- The normalization cost (6.9)--(6.10). -/
noncomputable def parameterSmoothCost (p : ℝ × ℝ) : ℝ :=
  2 * p.1 + 4 * p.2 - 2 - (5 * p.2 - 5 / 2) * Real.log 2

noncomputable def parameterCost (p : ℝ × ℝ) : ℝ :=
  parameterSmoothCost p - savingPhi p

/-- The logarithmic phase and its stationary cubic (6.6)--(6.7). -/
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

/-- The actual phase rates (6.8), evaluated at the specified saddle points. -/
noncomputable def paperCoefficientRate (p : ℝ × ℝ) : ℝ :=
  complexPhase p.1 p.2 (paperRealSaddle p : ℂ)

noncomputable def paperIntegralRate (p : ℝ × ℝ) : ℝ :=
  complexPhase p.1 p.2 (paperComplexSaddle p)

/-- The explicit auxiliary upper-bound function (6.11). -/
noncomputable def paperAuxiliaryBound (p : ℝ × ℝ) : ℝ :=
  1 + (paperCoefficientRate p + parameterCost p) /
    (-paperIntegralRate p - parameterCost p)

end PiIrrationalityChallenge

open PiIrrationalityChallenge

/-- Theorem 1.1: the strict irrationality-measure bound. -/
theorem comparator_theorem11 :
    IrrationalityMeasure Real.pi < (7101862832357 : ℝ) / 10 ^ 12 := by
  sorry

/-- A direct consequence, exposing all rational-approximation quantifiers. -/
theorem comparator_pi_rational_approximation_bound :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ q0 : ℕ, ∀ p : ℤ, ∀ q : ℕ, q0 ≤ q → 0 < q →
      |Real.pi - (p : ℝ) / (q : ℝ)| >
        (q : ℝ) ^ (-(7101862832357 : ℝ) / 10 ^ 12 - epsilon) := by
  sorry

/-- Theorem 1.2: strict local minimality over the real arithmetic chamber. -/
theorem comparator_theorem12 :
    StrictLocalMinimizer paperAuxiliaryBound Admissible candidate := by
  sorry
