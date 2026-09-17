import Formalization.PrimeSeriesTail
import Formalization.PrimeSavingAsymptotic
import Formalization.PrimeSavingMeasure

/-! The finite series enclosure and its strict error bound (3.16). -/

namespace PiIrrationality

noncomputable def primeSavingPartialSum (K : ℕ) : ℝ := paperPrimeIntervals.partialSum K

noncomputable def primeSavingTailLogs (K : ℕ) : ℝ :=
  ∑ j ∈ activeSavingCells, periodicLogTail (savingLeft j) (savingRight j) K

noncomputable def primeSavingTailError (K : ℕ) : ℝ :=
  ∑ j ∈ activeSavingCells, periodicSummandReal (savingLeft j) (savingRight j) K

theorem primeSavingSeries_split (K : ℕ) :
    primeSavingSeries = primeSavingPartialSum K + ∑ j ∈ activeSavingCells,
      ∑' q : ℕ, periodicSummandReal (savingLeft j) (savingRight j) (q + K) := by
  change (∑ j ∈ activeSavingCells, ∑' q : ℕ,
    periodicSummandReal (savingLeft j) (savingRight j) q) =
      (∑ j ∈ activeSavingCells, ∑ q ∈ Finset.range K,
        periodicSummandReal (savingLeft j) (savingRight j) q) + _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  exact ((paperPrimeIntervals.summable_component hj).sum_add_tsum_nat_add K).symm

theorem primeSavingSeries_tail_enclosure (K : ℕ) :
    primeSavingPartialSum K + primeSavingTailLogs K ≤ primeSavingSeries ∧
      primeSavingSeries ≤ primeSavingPartialSum K + primeSavingTailLogs K +
        primeSavingTailError K := by
  have hb j (hj : j ∈ activeSavingCells) := periodicSummandReal_tail_bounds
    (savingInterval_endpoints hj).1 (savingInterval_endpoints hj).2.1
    (savingInterval_endpoints hj).2.2.2.le K
  have hlo : primeSavingTailLogs K ≤ ∑ j ∈ activeSavingCells,
      ∑' q : ℕ, periodicSummandReal (savingLeft j) (savingRight j) (q + K) :=
    Finset.sum_le_sum fun j hj => (hb j hj).1
  have hup : (∑ j ∈ activeSavingCells,
      ∑' q : ℕ, periodicSummandReal (savingLeft j) (savingRight j) (q + K)) ≤
        primeSavingTailLogs K + primeSavingTailError K := by
    unfold primeSavingTailLogs primeSavingTailError
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j hj => (hb j hj).2
  have hsplit := primeSavingSeries_split K
  constructor <;> linarith

theorem periodicSummandReal_pos {ell r : ℝ}
    (hℓ : 0 < ell) (hr : ell < r) (K : ℕ) :
    0 < periodicSummandReal ell r K := by
  unfold periodicSummandReal
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  exact div_pos (sub_pos.mpr hr) (mul_pos (by linarith) (by linarith))

theorem periodicSummandReal_lt_length_div_sq {ell r : ℝ}
    (hℓ : 0 < ell) (hr : ell < r) {K : ℕ} (hK : 0 < K) :
    periodicSummandReal ell r K < (r - ell) / (K : ℝ) ^ 2 := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  unfold periodicSummandReal
  apply div_lt_div_of_pos_left (sub_pos.mpr hr) (sq_pos_of_pos hKR)
  nlinarith [mul_pos hℓ (hℓ.trans hr), mul_pos hKR hℓ, mul_pos hKR (hℓ.trans hr)]

/-- Equation (3.16), with the exact measure of the actual periodic set. -/
theorem primeSavingTailError_bounds {K : ℕ} (hK : 0 < K) :
    0 < primeSavingTailError K ∧
      primeSavingTailError K < ((1724689 : ℝ) / 13797510) / (K : ℝ) ^ 2 := by
  have h1 : 1 ∈ activeSavingCells :=
    mem_activeSavingCells.mpr (Or.inl ⟨by norm_num, by norm_num⟩)
  have hp j (hj : j ∈ activeSavingCells) := periodicSummandReal_pos
    (savingInterval_endpoints hj).1 (savingInterval_endpoints hj).2.1 K
  have hb j (hj : j ∈ activeSavingCells) := periodicSummandReal_lt_length_div_sq
    (savingInterval_endpoints hj).1 (savingInterval_endpoints hj).2.1 hK
  constructor
  · exact Finset.sum_pos' (fun j hj => (hp j hj).le) ⟨1, h1, hp 1 h1⟩
  · rw [← savingIntervals_total_length, Finset.sum_div]
    exact Finset.sum_lt_sum (fun j hj => (hb j hj).le) ⟨1, h1, hb 1 h1⟩

theorem primeSavingTailError_lt_measure {K : ℕ} (hK : 0 < K) :
    primeSavingTailError K < MeasureTheory.volume.real primeSavingSet / (K : ℝ) ^ 2 := by
  rw [primeSavingSet_volume_real]
  exact (primeSavingTailError_bounds hK).2

theorem primeSavingTailError_100000 :
    primeSavingTailError 100000 < (1251 : ℝ) / 10 ^ 14 ∧
      primeSavingTailError 100000 / 5570 < (2245 : ℝ) / 10 ^ 18 := by
  have h := (primeSavingTailError_bounds (by norm_num : 0 < (100000 : ℕ))).2
  norm_num at h
  constructor <;> linarith

end PiIrrationality
