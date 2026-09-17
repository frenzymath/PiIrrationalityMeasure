import Formalization.PrimeSavingAsymptotic
import Formalization.PNT.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries

/-! The digamma endpoint expression in (3.14). -/

namespace PiIrrationality

open Filter
open scoped Topology

noncomputable def realDigamma (x : ℝ) : ℝ := (Complex.digamma (x : ℂ)).re

theorem realDigamma_eq_logDeriv {x : ℝ} (hx : 0 < x) :
    realDigamma x = logDeriv Real.Gamma x := by
  have hn : ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have h := congrArg Complex.re hm
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at h
    have := Nat.cast_nonneg (α := ℝ) m
    linarith
  have hd : deriv Real.Gamma x = (deriv Complex.Gamma (x : ℂ)).re :=
    (Complex.differentiableAt_Gamma (x : ℂ) hn).hasDerivAt.real_of_complex.deriv
  rw [realDigamma, Complex.digamma_def, logDeriv_apply, logDeriv_apply, hd,
    Complex.Gamma_ofReal, Complex.div_ofReal_re]

theorem realDigamma_add_one {x : ℝ} (hx : 0 < x) :
    realDigamma (x + 1) = realDigamma x + 1 / x := by
  have hn : ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have h := congrArg Complex.re hm
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at h
    have := Nat.cast_nonneg (α := ℝ) m
    linarith
  unfold realDigamma
  rw [Complex.ofReal_add, Complex.ofReal_one, Complex.digamma_apply_add_one _ hn]
  simp only [Complex.add_re, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]

/-- The finite recurrence used to shift endpoints to `100 + x` in (3.19). -/
theorem realDigamma_add_nat {x : ℝ} (hx : 0 < x) (N : ℕ) :
    realDigamma (x + N) = realDigamma x + ∑ q ∈ Finset.range N, 1 / (x + (q : ℝ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN : 0 < x + (N : ℝ) := add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg N)
    rw [Nat.cast_succ, ← add_assoc, realDigamma_add_one hN, ih, Finset.sum_range_succ]
    ring

theorem hasSum_reciprocal_difference {ell r : ℝ} (hℓ : 0 < ell) (hr : 0 < r) :
    HasSum (fun q : ℕ => 1 / ((q : ℝ) + ell) - 1 / ((q : ℝ) + r))
      (realDigamma r - realDigamma ell) := by
  have hl := Complex.hasSum_digamma_of_re_pos (z₀ := (ell : ℂ)) hℓ
  have hr' := Complex.hasSum_digamma_of_re_pos (z₀ := (r : ℂ)) hr
  have hs : HasSum (fun q : ℕ => ((ell : ℂ) + q)⁻¹ - ((r : ℂ) + q)⁻¹)
      (Complex.digamma (r : ℂ) - Complex.digamma (ell : ℂ)) := by
    convert! hr'.sub hl using 1 <;> first | (funext q; ring) | ring
  simpa only [Complex.sub_re, ← Complex.ofReal_natCast, ← Complex.ofReal_add,
    ← Complex.ofReal_inv, Complex.ofReal_re, realDigamma, one_div, add_comm] using
      Complex.hasSum_re hs

theorem periodicSummandReal_tsum_eq_digamma {ell r : ℝ}
    (hℓ : 0 < ell) (hr : ell < r) :
    (∑' q : ℕ, periodicSummandReal ell r q) = realDigamma r - realDigamma ell := by
  simp_rw [periodicSummandReal_eq_sub_inv hℓ hr]
  exact (hasSum_reciprocal_difference hℓ (hℓ.trans hr)).tsum_eq

theorem primeSavingSeries_eq_digamma :
    primeSavingSeries = ∑ j ∈ activeSavingCells,
      (realDigamma (savingRight j) - realDigamma (savingLeft j)) := by
  unfold primeSavingSeries
  apply Finset.sum_congr rfl
  intro j hj
  exact periodicSummandReal_tsum_eq_digamma (savingInterval_endpoints hj).1
    (savingInterval_endpoints hj).2.1

/-- Equation (3.14), including its actual digamma endpoint values. -/
theorem Phi_log_limit_digamma :
    Tendsto (fun n : ℕ => Real.log (Phi n : ℝ) / (n : ℝ)) atTop
      (𝓝 (∑ j ∈ activeSavingCells,
        (realDigamma (savingRight j) - realDigamma (savingLeft j)))) := by
  rw [← primeSavingSeries_eq_digamma]
  exact Phi_log_limit

theorem Phi_log_limit_logDeriv :
    Tendsto (fun n : ℕ => Real.log (Phi n : ℝ) / (n : ℝ)) atTop
      (𝓝 (∑ j ∈ activeSavingCells,
        (logDeriv Real.Gamma (savingRight j) - logDeriv Real.Gamma (savingLeft j)))) := by
  have heq : (∑ j ∈ activeSavingCells,
      (realDigamma (savingRight j) - realDigamma (savingLeft j))) =
        ∑ j ∈ activeSavingCells,
          (logDeriv Real.Gamma (savingRight j) - logDeriv Real.Gamma (savingLeft j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have h := savingInterval_endpoints hj
    rw [realDigamma_eq_logDeriv (h.1.trans h.2.1), realDigamma_eq_logDeriv h.1]
  rw [← heq]
  exact Phi_log_limit_digamma

end PiIrrationality
