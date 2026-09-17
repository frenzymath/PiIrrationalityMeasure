import Formalization.DigammaApproximation
import Formalization.PrimeSavingMeasure

/-! The finite rational endpoint sum (3.24) and its total analytic error. -/

namespace PiIrrationality

def savingLeftRat (j : ℕ) : ℚ := (j : ℚ) / 3714

def savingRightRat (j : ℕ) : ℚ :=
  if j % 2 = 0 then
    if j ≤ 1114 then 3 * (j : ℚ) / 11140 else (2 * (j : ℚ) + 1) / 7430
  else if j ≤ 371 then (3 * (j : ℚ) + 1) / 11140
  else if j ≤ 1857 then (2 * (j : ℚ) + 1) / 7430
  else (3 * (j : ℚ) - 1) / 11140

theorem savingLeftRat_cast (j : ℕ) : (savingLeftRat j : ℝ) = savingLeft j := by
  simp [savingLeftRat, savingLeft]

theorem savingRightRat_cast (j : ℕ) : (savingRightRat j : ℝ) = savingRight j := by
  unfold savingRightRat savingRight
  split_ifs <;> push_cast <;> rfl

def savingApproxTerm (j : ℕ) : ℚ :=
  digammaApproxRat (savingRightRat j) - digammaApproxRat (savingLeftRat j)

def primeSavingApproxRat : ℚ := ∑ j ∈ activeSavingCells, savingApproxTerm j

theorem savingApproxTerm_cast (j : ℕ) : (savingApproxTerm j : ℝ) =
    digammaApprox (savingRight j) - digammaApprox (savingLeft j) := by
  simp only [savingApproxTerm, Rat.cast_sub, digammaApproxRat_cast,
    savingRightRat_cast, savingLeftRat_cast]

theorem primeSavingApproxRat_cast : (primeSavingApproxRat : ℝ) =
    ∑ j ∈ activeSavingCells,
      (digammaApprox (savingRight j) - digammaApprox (savingLeft j)) := by
  simp only [primeSavingApproxRat, Rat.cast_sum, savingApproxTerm_cast]

def savingCellIndex (q : ℕ) : ℕ :=
  if q < 1856 then q + 1 else 1859 + 2 * (q - 1856)

theorem savingCellIndex_image :
    (Finset.range 2784).image savingCellIndex = activeSavingCells := by
  ext j
  simp only [Finset.mem_image, Finset.mem_range, mem_activeSavingCells]
  constructor
  · rintro ⟨q, hq, rfl⟩
    unfold savingCellIndex
    split_ifs <;> omega
  · rintro (⟨hj1, hj2⟩ | ⟨hj1, hj2, hj3⟩)
    · refine ⟨j - 1, by omega, ?_⟩
      simp only [savingCellIndex, if_pos (by omega : j - 1 < 1856)]
      omega
    · refine ⟨1856 + (j - 1859) / 2, by omega, ?_⟩
      simp only [savingCellIndex, if_neg (by omega : ¬1856 + (j - 1859) / 2 < 1856)]
      omega

theorem savingCellIndex_injective : Function.Injective savingCellIndex := by
  intro a b hab
  unfold savingCellIndex at hab
  split_ifs at hab <;> omega

def primeSavingApproxPrefix (N : ℕ) : ℚ :=
  ∑ q ∈ Finset.range N, savingApproxTerm (savingCellIndex q)

theorem primeSavingApproxPrefix_zero : primeSavingApproxPrefix 0 = 0 := by
  simp [primeSavingApproxPrefix]

theorem primeSavingApproxPrefix_succ (N : ℕ) :
    primeSavingApproxPrefix (N + 1) = primeSavingApproxPrefix N +
      savingApproxTerm (savingCellIndex N) := by
  exact Finset.sum_range_succ _ N

theorem primeSavingApproxPrefix_last : primeSavingApproxPrefix 2784 = primeSavingApproxRat := by
  unfold primeSavingApproxPrefix primeSavingApproxRat
  rw [← savingCellIndex_image, Finset.sum_image]
  exact fun _ _ _ _ h => savingCellIndex_injective h

theorem savingApproxTerm_error {j : ℕ} (hj : j ∈ activeSavingCells) :
    |realDigamma (savingRight j) - realDigamma (savingLeft j) - (savingApproxTerm j : ℝ)| <
      2 * (digammaErrorBound : ℝ) := by
  have he := savingInterval_endpoints hj
  have hl := digammaApprox_error he.1 (he.2.1.trans he.2.2.2)
  have hr := digammaApprox_error (he.1.trans he.2.1) he.2.2.2
  rw [savingApproxTerm_cast]
  have h : realDigamma (savingRight j) - realDigamma (savingLeft j) -
      (digammaApprox (savingRight j) - digammaApprox (savingLeft j)) =
      (realDigamma (savingRight j) - Real.log 100 - digammaApprox (savingRight j)) -
      (realDigamma (savingLeft j) - Real.log 100 - digammaApprox (savingLeft j)) := by ring
  rw [h]
  exact (abs_sub _ _).trans_lt (by linarith [add_lt_add hr hl])

theorem primeSavingApproxRat_error :
    |primeSavingSeries - (primeSavingApproxRat : ℝ)| < 5568 * (digammaErrorBound : ℝ) := by
  rw [primeSavingSeries_eq_digamma, primeSavingApproxRat, Rat.cast_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ activeSavingCells,
        |realDigamma (savingRight j) - realDigamma (savingLeft j) -
          (savingApproxTerm j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ < ∑ j ∈ activeSavingCells, 2 * (digammaErrorBound : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact ⟨1, mem_activeSavingCells.mpr (by norm_num)⟩
      · intro j hj
        exact savingApproxTerm_error hj
    _ = 5568 * (digammaErrorBound : ℝ) := by
      rw [Finset.sum_const, activeSavingCells_card]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      ring

theorem primeSavingApproxRat_error_decimal :
    |primeSavingSeries - (primeSavingApproxRat : ℝ)| < (46 : ℝ) / 10 ^ 38 :=
  primeSavingApproxRat_error.trans digammaErrorBound_total

end PiIrrationality
