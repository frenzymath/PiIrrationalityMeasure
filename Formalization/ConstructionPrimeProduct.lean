import Formalization.ConstructionPrimeSelection
import Formalization.PeriodicPrimeProducts

/-! The general arithmetic prime product once a finite interval model is supplied. -/

namespace PiIrrationality

open Filter
open scoped Topology

theorem constructionPhi_eq_periodic_product_eventually
    {a b c : ℕ} (hc : 0 < c) (hp : Admissible (constructionParameter a b c))
    (E : PeriodicPrimeIntervals)
    (hregion : E.region = constructionSavingSet a b c)
    (hleft : ∀ j ∈ E.indices,
      1 / (constructionDegree a b c : ℝ) < E.left j) :
    ∀ᶠ n : ℕ in atTop,
      E.product (constructionDegree a b c : ℝ) n = constructionPhi a b c n := by
  let D : ℝ := constructionDegree a b c
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast constructionDegree_pos hc hp
  have hlarge : ∀ᶠ n : ℕ in atTop, (25 : ℝ) < D * (n : ℝ) := by
    have h := tendsto_natCast_atTop_atTop.const_mul_atTop hD
    exact h.eventually (eventually_gt_atTop (25 : ℝ))
  filter_upwards [eventually_gt_atTop (0 : ℕ), hlarge] with n hn h25
  have hprod : E.product D n = constructionPhi a b c n := by
    classical
    have hsets : E.selectedPrimes D n = constructionRemovablePrimes a b c n := by
      ext p
      rw [E.mem_selectedPrimes hD.le n p]
      simp only [constructionRemovablePrimes, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · intro hsel
        have hprime := hsel.1
        have hsqrt : (5 : ℝ) < Real.sqrt (D * (n : ℝ)) := by
          apply Real.lt_sqrt_of_sq_lt
          nlinarith [h25]
        have hfive : 5 < p := by
          exact_mod_cast (show (5 : ℝ) < p from lt_trans hsqrt hsel.2.1)
        have hbound : p ≤ constructionDegree a b c * n := by
          have hboundR : (p : ℝ) ≤ (constructionDegree a b c : ℝ) * (n : ℝ) := by
            simpa [D] using hsel.2.2.1
          exact_mod_cast hboundR
        have hfrac : Int.fract ((n : ℝ) / p) ∈ constructionSavingSet a b c := by
          rw [← hregion]
          exact hsel.2.2.2
        have hnat : Nat.sqrt (constructionDegree a b c * n) < p := by
          apply Nat.sqrt_lt'.mpr
          have hs' : Real.sqrt ((constructionDegree a b c : ℝ) * (n : ℝ)) < (p : ℝ) := by
            simpa [D] using hsel.2.1
          have hsq := (Real.sqrt_lt (by positivity : (0 : ℝ) ≤
            (constructionDegree a b c : ℝ) * (n : ℝ)) (Nat.cast_nonneg p)).mp hs'
          exact_mod_cast hsq
        have hrem := (constructionRemovablePrime_iff_periodic a b c n p).mpr
          ⟨hprime, hfive, hnat, hbound, hfrac⟩
        exact ⟨⟨by omega, hbound⟩, hrem⟩
      · rintro ⟨⟨hpone, hbound⟩, hrem⟩
        have hsel := (constructionRemovablePrime_iff_periodic a b c n p).mp hrem
        refine ⟨hsel.1, ?_, ?_, ?_⟩
        · have hsqrt : Real.sqrt (D * (n : ℝ)) < (p : ℝ) := by
            apply (Real.sqrt_lt (by positivity : (0 : ℝ) ≤ D * (n : ℝ))
              (Nat.cast_nonneg p)).mpr
            have hsq : constructionDegree a b c * n < p ^ 2 :=
              Nat.sqrt_lt'.mp hsel.2.2.1
            have hsqR : ((constructionDegree a b c * n : ℕ) : ℝ) <
                ((p ^ 2 : ℕ) : ℝ) := by exact_mod_cast hsq
            simpa [D, Nat.cast_mul, Nat.cast_pow] using hsqR
          simpa [D] using hsqrt
        · have hboundR : (p : ℝ) ≤ ((constructionDegree a b c * n : ℕ) : ℝ) := by
            exact_mod_cast hbound
          simpa [D, Nat.cast_mul] using hboundR
        · rw [hregion]
          exact hsel.2.2.2.2
    unfold PeriodicPrimeIntervals.product constructionPhi
    rw [hsets]
  exact hprod

theorem constructionPhi_log_limit_of_periodic_intervals
    {a b c : ℕ} (hc : 0 < c) (hp : Admissible (constructionParameter a b c))
    (E : PeriodicPrimeIntervals)
    (hregion : E.region = constructionSavingSet a b c)
    (hleft : ∀ j ∈ E.indices,
      1 / (constructionDegree a b c : ℝ) < E.left j) :
    Tendsto (fun n : ℕ => Real.log (constructionPhi a b c n : ℝ) / (n : ℝ))
      atTop (𝓝 E.series) := by
  let D : ℝ := constructionDegree a b c
  have hD : 1 < D := by
    dsimp [D]
    have hdeg := construction_admissible_inequalities hc hp
    have hcast : (constructionDegree a b c : ℝ) =
        2 * (a : ℝ) + 4 * b - 2 * c := constructionDegree_cast (by omega)
    rw [hcast]
    have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hc.ne')
    have hdeg' : (3 : ℝ) * c < 2 * a + 4 * b := by exact_mod_cast hdeg.2.2.2
    nlinarith
  have hprod := E.product_limit hD hleft
  have heq := constructionPhi_eq_periodic_product_eventually hc hp E hregion hleft
  apply hprod.congr'
  filter_upwards [heq] with n hn
  rw [hn]

end PiIrrationality
