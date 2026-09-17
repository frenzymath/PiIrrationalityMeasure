import Formalization.PrimeSavingApproximation

/-! Fixed-denominator rounding for the finite rational computation (3.25). -/

namespace PiIrrationality

def digammaApproxTable (x : ℚ) : ℚ :=
  2 * (∑ q ∈ Finset.range 8, (x / (200 + x)) ^ (2 * q + 1) / (2 * (q : ℚ) + 1)) -
    1 / (2 * (100 + x)) -
    (∑ m ∈ Finset.range 11, paperBernoulli (2 * (m + 1)) /
      ((2 * (m + 1) : ℕ) * (100 + x) ^ (2 * (m + 1)))) -
    ∑ q ∈ Finset.range 100, 1 / (x + (q : ℚ))

theorem digammaApproxTable_eq (x : ℚ) : digammaApproxTable x = digammaApproxRat x := by
  unfold digammaApproxTable digammaApproxRat
  congr 2
  apply Finset.sum_congr rfl
  intro m hm
  rw [bernoulli_eq_paperBernoulli (by have := Finset.mem_range.mp hm; omega)]

def roundedDigamma (x : ℚ) : ℤ := ⌊(10 : ℚ) ^ 32 * digammaApproxTable x⌋

theorem roundedDigamma_bounds (x : ℚ) :
    (roundedDigamma x : ℚ) / 10 ^ 32 ≤ digammaApproxRat x ∧
      digammaApproxRat x < ((roundedDigamma x : ℚ) + 1) / 10 ^ 32 := by
  have hl := Int.floor_le ((10 : ℚ) ^ 32 * digammaApproxTable x)
  have hu := Int.lt_floor_add_one ((10 : ℚ) ^ 32 * digammaApproxTable x)
  change (roundedDigamma x : ℚ) ≤ _ at hl
  change _ < (roundedDigamma x : ℚ) + 1 at hu
  rw [digammaApproxTable_eq] at hl hu
  constructor
  · rw [div_le_iff₀ (by norm_num : (0 : ℚ) < 10 ^ 32)]
    linarith
  · rw [lt_div_iff₀ (by norm_num : (0 : ℚ) < 10 ^ 32)]
    linarith

def roundedSavingTerm (j : ℕ) : ℤ :=
  roundedDigamma (savingRightRat j) - roundedDigamma (savingLeftRat j)

theorem roundedSavingTerm_error (j : ℕ) :
    |savingApproxTerm j - (roundedSavingTerm j : ℚ) / 10 ^ 32| < (1 : ℚ) / 10 ^ 32 := by
  obtain ⟨hl1, hl2⟩ := roundedDigamma_bounds (savingLeftRat j)
  obtain ⟨hr1, hr2⟩ := roundedDigamma_bounds (savingRightRat j)
  simp only [savingApproxTerm, roundedSavingTerm, Int.cast_sub]
  rw [abs_lt]
  constructor <;> linarith

def roundedSavingChunk (k : ℕ) : ℤ :=
  ((List.range 32).map fun q => roundedSavingTerm (savingCellIndex (32 * k + q))).sum

def roundedSavingTotal : ℤ := ((List.range 87).map roundedSavingChunk).sum

theorem sum_list_range_int (f : ℕ → ℤ) (N : ℕ) :
    ((List.range N).map f).sum = ∑ q ∈ Finset.range N, f q := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, Finset.sum_range_succ, ih]

theorem roundedSavingTotal_eq_sum :
    roundedSavingTotal = ∑ q ∈ Finset.range 2784,
      roundedSavingTerm (savingCellIndex q) := by
  unfold roundedSavingTotal
  rw [sum_list_range_int]
  simp only [roundedSavingChunk, sum_list_range_int]
  have h (N : ℕ) :
      (∑ k ∈ Finset.range N, ∑ q ∈ Finset.range 32,
        roundedSavingTerm (savingCellIndex (32 * k + q))) =
      ∑ q ∈ Finset.range (32 * N), roundedSavingTerm (savingCellIndex q) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, Nat.mul_succ, Finset.sum_range_add]
  exact h 87

set_option maxRecDepth 100000 in
theorem roundedSavingTotal_error :
    |primeSavingApproxRat - (roundedSavingTotal : ℚ) / 10 ^ 32| < (2784 : ℚ) / 10 ^ 32 := by
  rw [← primeSavingApproxPrefix_last, primeSavingApproxPrefix, roundedSavingTotal_eq_sum]
  push_cast
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ q ∈ Finset.range 2784,
        |savingApproxTerm (savingCellIndex q) -
          (roundedSavingTerm (savingCellIndex q) : ℚ) / 10 ^ 32| :=
      Finset.abs_sum_le_sum_abs _ _
    _ < ∑ q ∈ Finset.range 2784, (1 : ℚ) / 10 ^ 32 := by
      apply Finset.sum_lt_sum_of_nonempty (by simp)
      exact fun q _ => roundedSavingTerm_error (savingCellIndex q)
    _ = _ := by norm_num

end PiIrrationality
