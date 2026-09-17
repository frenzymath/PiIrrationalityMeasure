import Formalization.PeriodicPrimeIntervals
import Formalization.ConstructionGrid

/-! A finite grid interval model for the general construction saving set. -/

namespace PiIrrationality

open Set

noncomputable def constructionGridThreshold (a b c K j : ℕ) : ℝ :=
  (((((j / (K / (2 * a)) + 1) / 2 : ℕ) : ℝ) +
      2 * ((j / (K / b) : ℕ) : ℝ) - ((j / (K / c) : ℕ) : ℝ)) - 1 / 2) /
    ((a : ℝ) + 2 * b - c)

noncomputable def constructionGridLeft (K j : ℕ) : ℝ := (j : ℝ) / K

noncomputable def constructionGridRight (a b c K j : ℕ) : ℝ :=
  min (((j + 1 : ℕ) : ℝ) / K) (constructionGridThreshold a b c K j)

noncomputable def constructionGridIndices (a b c K : ℕ) : Finset ℕ :=
  (Finset.range K).filter (fun j =>
    1 ≤ j ∧ constructionGridLeft K j < constructionGridRight a b c K j)

theorem constructionSavingCondition_zero_cell {a b c K : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hK : 0 < K) (hKa : 2 * a ∣ K) (hKb : b ∣ K) (hKc : c ∣ K)
    (hcb : c < 2 * b) {u : ℝ}
    (hu : u ∈ Ico (0 : ℝ) (1 / K)) :
    ¬ constructionSavingCondition a b c u := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have h2a : 2 * a ≤ K := Nat.le_of_dvd hK hKa
  have hb' : b ≤ K := Nat.le_of_dvd hK hKb
  have hc' : c ≤ K := Nat.le_of_dvd hK hKc
  have hu0 : 0 ≤ u := hu.1
  have huK : (K : ℝ) * u < 1 := by
    simpa [mul_comm] using (lt_div_iff₀ hK').mp hu.2
  have hA0 : 0 ≤ (a : ℝ) * u := mul_nonneg (by positivity) hu0
  have hB0 : 0 ≤ (b : ℝ) * u := mul_nonneg (by positivity) hu0
  have hC0 : 0 ≤ (c : ℝ) * u := mul_nonneg (by positivity) hu0
  have hA1 : (a : ℝ) * u < 1 / 2 := by
    have h2a' : (2 * a : ℝ) ≤ K := by exact_mod_cast h2a
    nlinarith [mul_le_mul_of_nonneg_right h2a' hu0]
  have hB1 : (b : ℝ) * u < 1 := by
    have hb'' : (b : ℝ) ≤ K := by exact_mod_cast hb'
    nlinarith [mul_le_mul_of_nonneg_right hb'' hu0]
  have hC1 : (c : ℝ) * u < 1 := by
    have hc'' : (c : ℝ) ≤ K := by exact_mod_cast hc'
    nlinarith [mul_le_mul_of_nonneg_right hc'' hu0]
  have hq : 0 ≤ (a : ℝ) * u + 2 * ((b : ℝ) * u) - (c : ℝ) * u := by
    have hcb' : (c : ℝ) ≤ 2 * b := by exact_mod_cast hcb.le
    nlinarith [mul_le_mul_of_nonneg_right hcb' hu0]
  intro hs
  have hchi := (constructionSavingCondition_iff_chi a b c u).mp hs
  rw [savingChi_eq_zero_of_no_wrap hA0 hA1 hB0 hB1 hC0 hC1 hq] at hchi
  norm_num at hchi

theorem constructionGridIndices_mem {a b c K j : ℕ}
    {ha : 0 < a} {hb : 0 < b} {hc : 0 < c} {hK : 0 < K}
    {hdivA : 2 * a ∣ K} {hdivB : b ∣ K} {hdivC : c ∣ K}
    {hq : 0 < (a : ℝ) + 2 * b - c}
    (hj : j ∈ constructionGridIndices a b c K) :
    1 ≤ j ∧ j < K ∧
      constructionGridLeft K j < constructionGridRight a b c K j := by
  rw [constructionGridIndices] at hj
  obtain ⟨hjK, hjp⟩ := Finset.mem_filter.mp hj
  exact ⟨hjp.1, Finset.mem_range.mp hjK, hjp.2⟩

theorem constructionGridIndices_bounds {a b c K j : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hK : 0 < K)
    (hdivA : 2 * a ∣ K) (hdivB : b ∣ K) (hdivC : c ∣ K)
    (hq : 0 < (a : ℝ) + 2 * b - c)
    (hj : j ∈ constructionGridIndices a b c K) :
    0 < constructionGridLeft K j ∧
      constructionGridLeft K j < constructionGridRight a b c K j ∧
      constructionGridRight a b c K j ≤ 1 := by
  have hmem := constructionGridIndices_mem (ha := ha) (hb := hb) (hc := hc)
    (hK := hK) (hdivA := hdivA) (hdivB := hdivB) (hdivC := hdivC) (hq := hq) hj
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  refine ⟨?_, hmem.2.2, ?_⟩
  · dsimp [constructionGridLeft]
    apply div_pos
    · exact_mod_cast hmem.1
    · exact hK'
  · dsimp [constructionGridRight]
    apply le_trans (min_le_left _ _) ?_
    apply (div_le_iff₀ hK').mpr
    simpa using (show ((j + 1 : ℕ) : ℝ) ≤ (K : ℝ) by
      exact_mod_cast Nat.succ_le_of_lt hmem.2.1)

noncomputable def constructionGridPeriodicIntervals
    (a b c K : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hK : 0 < K)
    (hdivA : 2 * a ∣ K) (hdivB : b ∣ K) (hdivC : c ∣ K)
    (hq : 0 < (a : ℝ) + 2 * b - c) : PeriodicPrimeIntervals :=
  { indices := constructionGridIndices a b c K
    left := constructionGridLeft K
    right := constructionGridRight a b c K
    bounds := by
      intro j hj
      exact constructionGridIndices_bounds ha hb hc hK hdivA hdivB hdivC hq hj
    disjoint := by
      intro i hi j hj hne
      have hi' := constructionGridIndices_mem (ha := ha) (hb := hb) (hc := hc)
        (hK := hK) (hdivA := hdivA) (hdivB := hdivB) (hdivC := hdivC) (hq := hq) hi
      have hj' := constructionGridIndices_mem (ha := ha) (hb := hb) (hc := hc)
        (hK := hK) (hdivA := hdivA) (hdivB := hdivB) (hdivC := hdivC) (hq := hq) hj
      apply Set.disjoint_left.mpr
      intro u hui huj
      apply Set.disjoint_left.mp
        (constructionGridCell_Ico_pairwiseDisjoint hK hi'.2.1 hj'.2.1 hne)
      · exact ⟨hui.1, lt_of_lt_of_le hui.2 (min_le_left _ _)⟩
      · exact ⟨huj.1, lt_of_lt_of_le huj.2 (min_le_left _ _)⟩ }

theorem constructionGridPeriodicIntervals_bounds {a b c K : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hK : 0 < K)
    (hdivA : 2 * a ∣ K) (hdivB : b ∣ K) (hdivC : c ∣ K)
    (hq : 0 < (a : ℝ) + 2 * b - c) :
    ∀ j ∈ (constructionGridPeriodicIntervals a b c K ha hb hc hK hdivA hdivB hdivC hq).indices,
      0 < (constructionGridPeriodicIntervals a b c K ha hb hc hK hdivA hdivB hdivC hq).left j ∧
        (constructionGridPeriodicIntervals a b c K ha hb hc hK hdivA hdivB hdivC hq).left j <
          (constructionGridPeriodicIntervals a b c K ha hb hc hK hdivA hdivB hdivC hq).right j ∧
        (constructionGridPeriodicIntervals a b c K ha hb hc hK hdivA hdivB hdivC hq).right j ≤ 1 := by
  intro j hj
  exact constructionGridIndices_bounds ha hb hc hK hdivA hdivB hdivC hq hj

theorem constructionGridInterval_subset_savingSet {a b c K j : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hK : 0 < K)
    (hdivA : 2 * a ∣ K) (hdivB : b ∣ K) (hdivC : c ∣ K)
    (hq : 0 < (a : ℝ) + 2 * b - c)
    (hj : j ∈ constructionGridIndices a b c K) :
    Set.Ico (constructionGridLeft K j) (constructionGridRight a b c K j) ⊆
      constructionSavingSet a b c := by
  intro u hu
  have hmem := constructionGridIndices_mem (ha := ha) (hb := hb) (hc := hc)
    (hK := hK) (hdivA := hdivA) (hdivB := hdivB) (hdivC := hdivC) (hq := hq) hj
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have huGrid : u ∈ Ico ((j : ℝ) / K) (((j + 1 : ℕ) : ℝ) / K) := by
    refine ⟨hu.1, ?_⟩
    exact lt_of_lt_of_le hu.2 (min_le_left _ _)
  have hcond := (constructionSavingCondition_threshold_on_grid_Ico ha hb hc hK
    hdivA hdivB hdivC hq huGrid).mpr (by
      have hright : u < constructionGridRight a b c K j := hu.2
      dsimp [constructionGridRight] at hright
      have hmin : u < min (((j + 1 : ℕ) : ℝ) / K)
          (constructionGridThreshold a b c K j) := hright
      exact lt_of_lt_of_le hmin (min_le_right _ _))
  refine ⟨(div_nonneg (Nat.cast_nonneg j) hK'.le).trans huGrid.1, ?_, hcond⟩
  have hj1 : (j + 1 : ℕ) ≤ K := by omega
  have hj1' : ((j + 1 : ℕ) : ℝ) / K ≤ 1 := by
    apply (div_le_iff₀ hK').mpr
    simpa using (show ((j + 1 : ℕ) : ℝ) ≤ (K : ℝ) by exact_mod_cast hj1)
  exact huGrid.2.trans_le hj1'

theorem constructionSavingSet_subset_gridIntervals {a b c K : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hK : 0 < K)
    (hdivA : 2 * a ∣ K) (hdivB : b ∣ K) (hdivC : c ∣ K)
    (hq : 0 < (a : ℝ) + 2 * b - c) :
    constructionSavingSet a b c ⊆
      ⋃ j ∈ constructionGridIndices a b c K,
        Set.Ico (constructionGridLeft K j) (constructionGridRight a b c K j) := by
  intro u hu
  have hu0 : 0 ≤ u := hu.1
  have hu1 : u < 1 := hu.2.1
  let j : ℕ := ⌊(K : ℝ) * u⌋₊
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hfloor : (j : ℝ) ≤ (K : ℝ) * u ∧ (K : ℝ) * u < (j : ℝ) + 1 := by
    exact ⟨Nat.floor_le (mul_nonneg hK'.le hu0), Nat.lt_floor_add_one _⟩
  have hjK : j < K := by
    have : (K : ℝ) * u < K := by nlinarith
    exact (Nat.floor_lt (mul_nonneg hK'.le hu0)).mpr (by exact_mod_cast this)
  have huGrid : u ∈ Ico ((j : ℝ) / K) (((j + 1 : ℕ) : ℝ) / K) := by
    constructor
    · apply (div_le_iff₀ hK').mpr
      simpa [mul_comm] using hfloor.1
    · apply (lt_div_iff₀ hK').mpr
      simpa [mul_comm] using hfloor.2
  have hj0 : 1 ≤ j := by
    by_contra hj0
    have hjz : j = 0 := by omega
    have hlin := (constructionSavingCondition_on_grid_Ico ha hb hc hK
      hdivA hdivB hdivC huGrid).mp hu.2.2
    simp only [hjz, Nat.zero_div, zero_add, Nat.reduceDiv, Nat.cast_zero,
      mul_zero, add_zero, sub_zero] at hlin
    nlinarith [mul_nonneg hq.le hu0]
  have hthr := (constructionSavingCondition_threshold_on_grid_Ico ha hb hc hK
    hdivA hdivB hdivC hq huGrid).mp hu.2.2
  have hjmem : j ∈ constructionGridIndices a b c K := by
    rw [constructionGridIndices]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hjK, hj0, ?_⟩
    dsimp [constructionGridLeft, constructionGridRight]
    exact huGrid.1.trans_lt (lt_min huGrid.2 hthr)
  refine Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hjmem, ?_⟩⟩
  exact ⟨huGrid.1, lt_min huGrid.2 hthr⟩

theorem constructionGridPeriodicIntervals_region_eq {a b c K : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hK : 0 < K)
    (hdivA : 2 * a ∣ K) (hdivB : b ∣ K) (hdivC : c ∣ K)
    (hq : 0 < (a : ℝ) + 2 * b - c) :
    (constructionGridPeriodicIntervals a b c K ha hb hc hK hdivA hdivB hdivC hq).region =
      constructionSavingSet a b c := by
  ext u
  constructor
  · intro hu
    obtain ⟨j, hu⟩ := Set.mem_iUnion.mp hu
    obtain ⟨hj, hu⟩ := Set.mem_iUnion.mp hu
    exact constructionGridInterval_subset_savingSet ha hb hc hK hdivA hdivB hdivC hq hj hu
  · intro hu
    exact constructionSavingSet_subset_gridIntervals ha hb hc hK hdivA hdivB hdivC hq hu

theorem construction_grid_positive {a b c : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) :
    0 < a ∧ 0 < b ∧ 0 < (a : ℝ) + 2 * b - c := by
  have hm := construction_admissible_inequalities hc hp
  have hq : (c : ℝ) < a + 2 * b := by
    exact_mod_cast (show c < a + 2 * b by omega)
  exact ⟨by omega, by omega, by linarith⟩

theorem constructionSavingSet_exists_periodic_intervals {a b c : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) :
    ∃ E : PeriodicPrimeIntervals, E.region = constructionSavingSet a b c := by
  obtain ⟨ha, hb, hq⟩ := construction_grid_positive hc hp
  obtain ⟨hK, hKa, hKb, hKc⟩ := constructionGridDenominator_properties ha hb hc
  exact ⟨constructionGridPeriodicIntervals a b c (constructionGridDenominator a b c)
    ha hb hc hK hKa hKb hKc hq,
    constructionGridPeriodicIntervals_region_eq ha hb hc hK hKa hKb hKc hq⟩

theorem construction_periodic_intervals_left_bound {a b c : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) (E : PeriodicPrimeIntervals)
    (hregion : E.region = constructionSavingSet a b c) :
    ∀ j ∈ E.indices, 1 / (constructionDegree a b c : ℝ) < E.left j := by
  obtain ⟨e, he, hgap⟩ := constructionSaving_initial_gap hc hp
  intro j hj
  have hb := E.bounds j hj
  have hmem : E.left j ∈ constructionSavingSet a b c := by
    rw [← hregion]
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, le_rfl, hb.2.1⟩⟩
  have hlarge : 1 / (constructionDegree a b c : ℝ) + e < E.left j := by
    by_contra h
    exact hgap _ hb.1 (le_of_not_gt h) hmem.2.2
  linarith

end PiIrrationality
