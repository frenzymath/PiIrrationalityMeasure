import Formalization.PeriodicPrimeProducts
import Formalization.PrimeSavingSelection

/-! Apply the periodic prime-product theorem to the actual Phi of the article. -/

namespace PiIrrationality

open Filter
open scoped Topology

noncomputable def paperPrimeIntervals : PeriodicPrimeIntervals where
  indices := activeSavingCells
  left := savingLeft
  right := savingRight
  bounds := fun _ hj =>
    let he := savingInterval_endpoints hj
    ⟨he.1, he.2.1, he.2.2.2.le⟩
  disjoint := savingIntervals_pairwiseDisjoint

theorem paperPrimeIntervals_region : paperPrimeIntervals.region = primeSavingSet := by
  exact primeSavingSet_eq_intervals.symm

theorem paperPrimeIntervals_series : paperPrimeIntervals.series = primeSavingSeries := rfl

theorem paperPrimeIntervals_left_bound :
    ∀ j ∈ paperPrimeIntervals.indices, (1 : ℝ) / 7430 < paperPrimeIntervals.left j := by
  intro j hj
  have hj' : j ∈ activeSavingCells := hj
  have hlow : (1 : ℝ) ≤ j := by
    exact_mod_cast (show 1 ≤ j by have := mem_activeSavingCells.mp hj'; omega)
  change (1 : ℝ) / 7430 < (j : ℝ) / 3714
  linarith

theorem paperPrimeIntervals_selectedPrimes {n : ℕ} (hn : 1 ≤ n) :
    paperPrimeIntervals.selectedPrimes 7430 n = removablePrimes n := by
  classical
  ext p
  have hrem : p ∈ removablePrimes n ↔ removablePrime n p := by
    simp only [removablePrimes, Finset.mem_filter]
    exact ⟨And.right, fun h => ⟨removablePrime_mem_range n p h, h⟩⟩
  rw [paperPrimeIntervals.mem_selectedPrimes (by norm_num), hrem,
    paperPrimeIntervals_region, removablePrime_iff_periodic_of_pos hn]
  constructor
  · rintro ⟨hp, hs, hb, he⟩
    refine ⟨hp, ?_, ?_, he⟩
    · apply Nat.sqrt_lt'.mpr
      have h := (Real.sqrt_lt (by positivity : (0 : ℝ) ≤ 7430 * n)
        (Nat.cast_nonneg p)).mp hs
      exact_mod_cast h
    · exact_mod_cast hb
  · rintro ⟨hp, hs, hb, he⟩
    refine ⟨hp, ?_, ?_, he⟩
    · apply (Real.sqrt_lt (by positivity : (0 : ℝ) ≤ 7430 * n)
        (Nat.cast_nonneg p)).mpr
      exact_mod_cast Nat.sqrt_lt'.mp hs
    · exact_mod_cast hb

theorem paperPrimeIntervals_product {n : ℕ} (hn : 1 ≤ n) :
    paperPrimeIntervals.product 7430 n = Phi n := by
  rw [PeriodicPrimeIntervals.product, paperPrimeIntervals_selectedPrimes hn]
  rfl

/-- The first equality in (3.14), with the actual arithmetic prime product. -/
theorem Phi_log_limit :
    Tendsto (fun n : ℕ => Real.log (Phi n : ℝ) / (n : ℝ)) atTop (𝓝 primeSavingSeries) := by
  have h := paperPrimeIntervals.product_limit (by norm_num : (1 : ℝ) < 7430)
    paperPrimeIntervals_left_bound
  rw [paperPrimeIntervals_series] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [paperPrimeIntervals_product hn]

theorem Phi_log_limit_endpoint_series :
    Tendsto (fun n : ℕ => Real.log (Phi n : ℝ) / (n : ℝ)) atTop
      (𝓝 (∑ j ∈ activeSavingCells, ∑' q : ℕ,
        (1 / ((q : ℝ) + savingLeft j) - 1 / ((q : ℝ) + savingRight j)))) := by
  rw [← primeSavingSeries_eq_endpoint_series]
  exact Phi_log_limit

end PiIrrationality
