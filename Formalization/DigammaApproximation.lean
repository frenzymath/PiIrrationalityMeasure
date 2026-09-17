import Formalization.DigammaBinet
import Formalization.BernoulliCertificate
import Formalization.DigammaLogApprox

/-! The explicit digamma approximation and uniform error (3.19)--(3.23). -/

namespace PiIrrationality

noncomputable def digammaApprox (x : ℝ) : ℝ :=
  digammaLogApprox x - 1 / (2 * (100 + x)) - binetLaplaceApprox (100 + x) 11 -
    ∑ q ∈ Finset.range 100, 1 / (x + (q : ℝ))

def digammaApproxRat (x : ℚ) : ℚ :=
  2 * (∑ q ∈ Finset.range 8, (x / (200 + x)) ^ (2 * q + 1) / (2 * (q : ℚ) + 1)) -
    1 / (2 * (100 + x)) -
    (∑ m ∈ Finset.range 11, bernoulli (2 * (m + 1)) /
      ((2 * (m + 1) : ℕ) * (100 + x) ^ (2 * (m + 1)))) -
    ∑ q ∈ Finset.range 100, 1 / (x + (q : ℚ))

theorem digammaApproxRat_cast (x : ℚ) :
    (digammaApproxRat x : ℝ) = digammaApprox (x : ℝ) := by
  unfold digammaApproxRat digammaApprox
  rw [digammaLogApprox_eq]
  unfold binetLaplaceApprox
  push_cast
  rfl

def digammaErrorBound : ℚ :=
  2 / (17 * (1 - 1 / 201 ^ 2) * 201 ^ 17) + 236364091 / (2730 * 24 * 100 ^ 24)

theorem digammaErrorBound_pos : 0 < digammaErrorBound := by
  norm_num [digammaErrorBound]

theorem digammaErrorBound_total :
    5568 * (digammaErrorBound : ℝ) < (46 : ℝ) / 10 ^ 38 := by
  norm_num [digammaErrorBound]

theorem realDigamma_bernoulli_remainder_eleven {y : ℝ} (hy : 0 < y) :
    |realDigamma y - Real.log y + 1 / (2 * y) + binetLaplaceApprox y 11| <
      (236364091 : ℝ) / (2730 * 24 * y ^ 24) := by
  have h := realDigamma_bernoulli_remainder hy 11
  norm_num only [Nat.reduceAdd, Nat.reduceMul, bernoulli_twenty_four, Rat.cast_div,
    Rat.cast_neg, Rat.cast_ofNat, abs_div, abs_neg, Nat.cast_ofNat] at h
  convert! h using 1
  ring

theorem digammaApprox_error {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    |realDigamma x - Real.log 100 - digammaApprox x| < (digammaErrorBound : ℝ) := by
  have hy : 0 < 100 + x := by linarith
  have hB := realDigamma_bernoulli_remainder_eleven hy
  have hB' : |realDigamma (100 + x) - Real.log (100 + x) + 1 / (2 * (100 + x)) +
      binetLaplaceApprox (100 + x) 11| < (236364091 : ℝ) / (2730 * 24 * 100 ^ 24) := by
    apply hB.trans_le
    gcongr
    linarith
  have hL := digammaLogApprox_error hx0 hx1
  have hrec := realDigamma_add_nat hx0 100
  norm_num only [Nat.cast_ofNat] at hrec
  rw [add_comm x 100] at hrec
  have hlog : Real.log (100 + x) = Real.log 100 + Real.log (1 + x / 100) := by
    rw [← Real.log_mul (by norm_num : (100 : ℝ) ≠ 0) (by positivity : 1 + x / 100 ≠ 0)]
    congr 1
    ring
  have he : realDigamma x - Real.log 100 - digammaApprox x =
      (realDigamma (100 + x) - Real.log (100 + x) + 1 / (2 * (100 + x)) +
        binetLaplaceApprox (100 + x) 11) +
      (Real.log (1 + x / 100) - digammaLogApprox x) := by
    unfold digammaApprox
    rw [hrec, hlog]
    ring
  rw [he]
  calc
    _ ≤ |realDigamma (100 + x) - Real.log (100 + x) + 1 / (2 * (100 + x)) +
        binetLaplaceApprox (100 + x) 11| +
      |Real.log (1 + x / 100) - digammaLogApprox x| := abs_add_le _ _
    _ < (236364091 : ℝ) / (2730 * 24 * 100 ^ 24) +
        2 / (17 * (1 - (201 : ℝ) ^ (-2 : ℤ)) * 201 ^ 17) := by
      rw [abs_of_pos hL.1]
      exact add_lt_add hB' hL.2
    _ = (digammaErrorBound : ℝ) := by norm_num [digammaErrorBound]

end PiIrrationality
