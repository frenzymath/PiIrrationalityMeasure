import Formalization.PrimeLogIntervals

/-! Finite periodic interval systems and the exact truncated prime partition. -/

namespace PiIrrationality

open Filter
open scoped Topology

structure PeriodicPrimeIntervals where
  indices : Finset ℕ
  left : ℕ → ℝ
  right : ℕ → ℝ
  bounds : ∀ j ∈ indices, 0 < left j ∧ left j < right j ∧ right j ≤ 1
  disjoint : Set.PairwiseDisjoint (↑indices : Set ℕ) (fun j => Set.Ico (left j) (right j))

namespace PeriodicPrimeIntervals

variable (E : PeriodicPrimeIntervals)

def region : Set ℝ := ⋃ j ∈ E.indices, Set.Ico (E.left j) (E.right j)

noncomputable def truncation (n T : ℕ) : Finset ℕ :=
  (E.indices.product (Finset.range T)).biUnion (fun jq =>
    primeBand ((n : ℝ) / ((jq.2 : ℝ) + E.right jq.1))
      ((n : ℝ) / ((jq.2 : ℝ) + E.left jq.1)))

noncomputable def series : ℝ :=
  ∑ j ∈ E.indices, ∑' q : ℕ, periodicSummandReal (E.left j) (E.right j) q

noncomputable def partialSum (T : ℕ) : ℝ :=
  ∑ j ∈ E.indices, ∑ q ∈ Finset.range T, periodicSummandReal (E.left j) (E.right j) q

theorem summable_component {j : ℕ} (hj : j ∈ E.indices) :
    Summable (fun q => periodicSummandReal (E.left j) (E.right j) q) := by
  have hb := E.bounds j hj
  exact periodicSummandReal_summable hb.1 hb.2.1 hb.2.2

theorem partialSum_limit : Tendsto E.partialSum atTop (𝓝 E.series) := by
  apply tendsto_finsetSum
  intro j hj
  exact (E.summable_component hj).hasSum.tendsto_sum_nat

theorem series_eq_reciprocal : E.series = ∑ j ∈ E.indices, ∑' q : ℕ,
    (1 / ((q : ℝ) + E.left j) - 1 / ((q : ℝ) + E.right j)) := by
  apply Finset.sum_congr rfl
  intro j hj
  apply tsum_congr
  intro q
  have hb := E.bounds j hj
  exact periodicSummandReal_eq_sub_inv hb.1 hb.2.1 q

theorem truncation_disjoint {n : ℕ} (hn : 0 < n) (T : ℕ) :
    Set.PairwiseDisjoint (↑(E.indices.product (Finset.range T)) : Set (ℕ × ℕ))
      (fun jq => primeBand ((n : ℝ) / ((jq.2 : ℝ) + E.right jq.1))
        ((n : ℝ) / ((jq.2 : ℝ) + E.left jq.1))) := by
  intro i hi j hj hne
  have hi' := Finset.mem_product.mp hi
  have hj' := Finset.mem_product.mp hj
  have hbi := E.bounds i.1 hi'.1
  have hbj := E.bounds j.1 hj'.1
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  obtain ⟨_, hqi, hui⟩ := (mem_primeBand_reciprocal hbi.1 hbi.2.1 hbi.2.2 hn i.2 p).mp hpi
  obtain ⟨_, hqj, huj⟩ := (mem_primeBand_reciprocal hbj.1 hbj.2.1 hbj.2.2 hn j.2 p).mp hpj
  have hq : i.2 = j.2 := by exact_mod_cast hqi.symm.trans hqj
  by_cases hij : i.1 = j.1
  · exact hne (Prod.ext hij hq)
  · exact Set.disjoint_left.mp (E.disjoint hi'.1 hj'.1 hij) hui huj

theorem truncation_log_sum {n : ℕ} (hn : 0 < n) (T : ℕ) :
    ∑ p ∈ E.truncation n T, Real.log (p : ℝ) =
      ∑ j ∈ E.indices, ∑ q ∈ Finset.range T,
        ∑ p ∈ primeBand ((n : ℝ) / ((q : ℝ) + E.right j))
          ((n : ℝ) / ((q : ℝ) + E.left j)), Real.log (p : ℝ) := by
  rw [truncation, Finset.sum_biUnion (E.truncation_disjoint hn T)]
  exact Finset.sum_product _ _ _

theorem truncation_log_limit (T : ℕ) :
    Tendsto (fun n : ℕ => (∑ p ∈ E.truncation n T, Real.log (p : ℝ)) / (n : ℝ))
      atTop (𝓝 (E.partialSum T)) := by
  have h : Tendsto (fun n : ℕ =>
      ∑ j ∈ E.indices, ∑ q ∈ Finset.range T,
        (∑ p ∈ primeBand ((n : ℝ) / ((q : ℝ) + E.right j))
          ((n : ℝ) / ((q : ℝ) + E.left j)), Real.log (p : ℝ)) / (n : ℝ))
      atTop (𝓝 (E.partialSum T)) := by
    apply tendsto_finsetSum
    intro j hj
    apply tendsto_finsetSum
    intro q _
    have hb := E.bounds j hj
    rw [periodicSummandReal_eq_sub_inv hb.1 hb.2.1]
    exact primeBand_reciprocal_limit hb.1 hb.2.1 q
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [E.truncation_log_sum hn]
  simp only [Finset.sum_div]

theorem mem_truncation {n T p : ℕ} (hn : 0 < n) (hT : 0 < T) :
    p ∈ E.truncation n T ↔ Nat.Prime p ∧ Int.fract ((n : ℝ) / p) ∈ E.region ∧
      (n : ℝ) / (T : ℝ) < (p : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  constructor
  · intro hp
    obtain ⟨⟨j, q⟩, hjq, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hj, hq⟩ := Finset.mem_product.mp hjq
    have hq' : (q : ℝ) + 1 ≤ (T : ℝ) := by
      exact_mod_cast (show q + 1 ≤ T by simpa using Finset.mem_range.mp hq)
    have hb := E.bounds j hj
    obtain ⟨hp', hfloor, hu⟩ :=
      (mem_primeBand_reciprocal hb.1 hb.2.1 hb.2.2 hn q p).mp hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.pos
    have heq : (n : ℝ) / p = (q : ℝ) + Int.fract ((n : ℝ) / p) := by
      simpa only [hfloor, Int.cast_natCast] using (Int.floor_add_fract ((n : ℝ) / p)).symm
    refine ⟨hp', Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, hu⟩⟩, ?_⟩
    apply (div_lt_iff₀ hT').mpr
    have hnt : (n : ℝ) / p < (T : ℝ) := by linarith [hu.2, hb.2.2]
    have h := (div_lt_iff₀ hp0).mp hnt
    linarith
  · rintro ⟨hp, hu, hlarge⟩
    obtain ⟨j, hu⟩ := Set.mem_iUnion.mp hu
    obtain ⟨hj, hu⟩ := Set.mem_iUnion.mp hu
    have hb := E.bounds j hj
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hnp : 0 ≤ (n : ℝ) / p := div_nonneg hn'.le hp0.le
    let q := ⌊(n : ℝ) / p⌋₊
    have hfloor : ⌊(n : ℝ) / p⌋ = (q : ℤ) := (Int.natCast_floor_eq_floor hnp).symm
    have hq : q < T := by
      apply (Nat.floor_lt hnp).mpr
      apply (div_lt_iff₀ hp0).mpr
      have h := (div_lt_iff₀ hT').mp hlarge
      linarith
    apply Finset.mem_biUnion.mpr
    refine ⟨(j, q), Finset.mem_product.mpr ⟨hj, Finset.mem_range.mpr hq⟩, ?_⟩
    exact (mem_primeBand_reciprocal hb.1 hb.2.1 hb.2.2 hn q p).mpr ⟨hp, hfloor, hu⟩

end PeriodicPrimeIntervals
end PiIrrationality
