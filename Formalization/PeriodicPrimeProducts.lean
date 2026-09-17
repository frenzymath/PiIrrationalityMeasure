import Formalization.PeriodicPrimeIntervals

/-! The periodic prime-product limit, including both moving cutoffs (Lemma 3.2). -/

namespace PiIrrationality

open Filter
open scoped Topology

namespace PeriodicPrimeIntervals

variable (E : PeriodicPrimeIntervals)

noncomputable def selectedPrimes (D : ℝ) (n : ℕ) : Finset ℕ := by
  classical
  exact (Nat.primesLE ⌊D * (n : ℝ)⌋₊).filter (fun p =>
    Real.sqrt (D * (n : ℝ)) < (p : ℝ) ∧ Int.fract ((n : ℝ) / p) ∈ E.region)

noncomputable def product (D : ℝ) (n : ℕ) : ℕ := (E.selectedPrimes D n).prod id

theorem mem_selectedPrimes {D : ℝ} (hD : 0 ≤ D) (n p : ℕ) :
    p ∈ E.selectedPrimes D n ↔ Nat.Prime p ∧ Real.sqrt (D * (n : ℝ)) < (p : ℝ) ∧
      (p : ℝ) ≤ D * (n : ℝ) ∧ Int.fract ((n : ℝ) / p) ∈ E.region := by
  simp only [selectedPrimes, Finset.mem_filter, Nat.mem_primesLE,
    Nat.le_floor_iff (mul_nonneg hD (Nat.cast_nonneg n))]
  tauto

theorem selectedPrimes_prime {D : ℝ} {n p : ℕ} (hp : p ∈ E.selectedPrimes D n) :
    Nat.Prime p := by
  classical
  exact (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2

theorem product_pos (D : ℝ) (n : ℕ) : 0 < E.product D n := by
  exact Finset.prod_pos (fun p hp => (E.selectedPrimes_prime hp).pos)

theorem log_product (D : ℝ) (n : ℕ) :
    Real.log (E.product D n : ℝ) = ∑ p ∈ E.selectedPrimes D n, Real.log (p : ℝ) := by
  simp only [product, Nat.cast_prod, id_eq]
  apply Real.log_prod
  intro p hp
  exact_mod_cast (E.selectedPrimes_prime hp).ne_zero

theorem region_prime_upper_bound {D : ℝ} (hD : 0 < D)
    (hleft : ∀ j ∈ E.indices, 1 / D < E.left j) {n p : ℕ} (hp : Nat.Prime p)
    (hu : Int.fract ((n : ℝ) / p) ∈ E.region) : (p : ℝ) < D * (n : ℝ) := by
  obtain ⟨j, hu⟩ := Set.mem_iUnion.mp hu
  obtain ⟨hj, hu⟩ := Set.mem_iUnion.mp hu
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hn0 : 0 ≤ (n : ℝ) / p := div_nonneg (Nat.cast_nonneg n) hp0.le
  have hf0 : (0 : ℝ) ≤ (⌊(n : ℝ) / p⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.mpr hn0
  have hnp : 1 / D < (n : ℝ) / p := by
    linarith [hleft j hj, hu.1, Int.fract_add_floor ((n : ℝ) / p)]
  have h := (div_lt_div_iff₀ hD hp0).mp hnp
  simpa only [one_mul, mul_one, mul_comm] using h

theorem sqrt_cutoff_le_truncation {D : ℝ} {n T : ℕ} (hT : 0 < T)
    (hn : D * (T : ℝ) ^ 2 ≤ (n : ℝ)) :
    Real.sqrt (D * (n : ℝ)) ≤ (n : ℝ) / (T : ℝ) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  apply Real.sqrt_le_iff.mpr
  refine ⟨div_nonneg (Nat.cast_nonneg n) hT'.le, ?_⟩
  rw [div_pow]
  apply (le_div_iff₀ (sq_pos_of_pos hT')).mpr
  have h := mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith

theorem truncation_subset_selectedPrimes {D : ℝ} (hD : 0 < D)
    (hleft : ∀ j ∈ E.indices, 1 / D < E.left j) {n T : ℕ} (hn : 0 < n) (hT : 0 < T)
    (hlarge : D * (T : ℝ) ^ 2 ≤ (n : ℝ)) : E.truncation n T ⊆ E.selectedPrimes D n := by
  intro p hp
  obtain ⟨hp', hu, hcut⟩ := (E.mem_truncation hn hT).mp hp
  apply (E.mem_selectedPrimes hD.le n p).mpr
  exact ⟨hp', lt_of_le_of_lt (sqrt_cutoff_le_truncation hT hlarge) hcut,
    (E.region_prime_upper_bound hD hleft hp' hu).le, hu⟩

theorem selectedPrimes_sdiff_truncation_small {D : ℝ} {n T : ℕ}
    (hn : 0 < n) (hT : 0 < T) {p : ℕ}
    (hp : p ∈ E.selectedPrimes D n \ E.truncation n T) :
    Nat.Prime p ∧ (p : ℝ) ≤ (n : ℝ) / (T : ℝ) := by
  classical
  have hsel := (Finset.mem_sdiff.mp hp).1
  have hnot := (Finset.mem_sdiff.mp hp).2
  have hprime := E.selectedPrimes_prime hsel
  refine ⟨hprime, le_of_not_gt ?_⟩
  intro hlarge
  exact hnot ((E.mem_truncation hn hT).mpr
    ⟨hprime, (Finset.mem_filter.mp hsel).2.2, hlarge⟩)

theorem log_product_sandwich {D : ℝ} (hD : 0 < D)
    (hleft : ∀ j ∈ E.indices, 1 / D < E.left j) {n T : ℕ} (hn : 0 < n) (hT : 0 < T)
    (hlarge : D * (T : ℝ) ^ 2 ≤ (n : ℝ)) :
    (∑ p ∈ E.truncation n T, Real.log (p : ℝ)) ≤ Real.log (E.product D n : ℝ) ∧
    Real.log (E.product D n : ℝ) ≤
      (∑ p ∈ E.truncation n T, Real.log (p : ℝ)) + Chebyshev.theta ((n : ℝ) / T) := by
  have hsubset := E.truncation_subset_selectedPrimes hD hleft hn hT hlarge
  have heq := Finset.sum_sdiff (f := fun p : ℕ => Real.log (p : ℝ)) hsubset
  have hnonneg : 0 ≤ ∑ p ∈ E.selectedPrimes D n \ E.truncation n T, Real.log (p : ℝ) :=
    prime_logs_nonneg (fun _ hp => (E.selectedPrimes_sdiff_truncation_small hn hT hp).1)
  have hupper : (∑ p ∈ E.selectedPrimes D n \ E.truncation n T, Real.log (p : ℝ)) ≤
      Chebyshev.theta ((n : ℝ) / T) :=
    prime_logs_le_theta (fun _ hp => E.selectedPrimes_sdiff_truncation_small hn hT hp)
  rw [E.log_product]
  constructor <;> linarith

theorem log_product_sandwich_eventually {D : ℝ} (hD : 0 < D)
    (hleft : ∀ j ∈ E.indices, 1 / D < E.left j) {T : ℕ} (hT : 0 < T) :
    ∀ᶠ n : ℕ in atTop,
      (∑ p ∈ E.truncation n T, Real.log (p : ℝ)) / (n : ℝ) ≤
        Real.log (E.product D n : ℝ) / (n : ℝ) ∧
      Real.log (E.product D n : ℝ) / (n : ℝ) ≤
        (∑ p ∈ E.truncation n T, Real.log (p : ℝ)) / (n : ℝ) +
          Chebyshev.theta ((n : ℝ) / T) / (n : ℝ) := by
  have hg : ∀ᶠ n : ℕ in atTop, D * (T : ℝ) ^ 2 ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (0 : ℕ), hg] with n hn hlarge
  obtain ⟨hl, hu⟩ := E.log_product_sandwich hD hleft hn hT hlarge
  refine ⟨div_le_div_of_nonneg_right hl (Nat.cast_nonneg n), ?_⟩
  simpa only [add_div] using div_le_div_of_nonneg_right hu (Nat.cast_nonneg n)

/-- The finite prime partition and a theta tail bound prove Lemma 3.2. -/
theorem product_limit {D : ℝ} (hD : 1 < D)
    (hleft : ∀ j ∈ E.indices, 1 / D < E.left j) :
    Tendsto (fun n : ℕ => Real.log (E.product D n : ℝ) / (n : ℝ))
      atTop (𝓝 E.series) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  have hp : ∀ᶠ T : ℕ in atTop, |E.partialSum T - E.series| < ε / 4 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using
      E.partialSum_limit.eventually (Metric.ball_mem_nhds E.series hε4)
  have hi : Tendsto (fun T : ℕ => 1 / (T : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hi' : ∀ᶠ T : ℕ in atTop, 1 / (T : ℝ) < ε / 4 :=
    hi.eventually (gt_mem_nhds hε4)
  obtain ⟨T, hT, hpartial, hinv⟩ := ((eventually_gt_atTop (0 : ℕ)).and (hp.and hi')).exists
  have hl : ∀ᶠ n : ℕ in atTop,
      |(∑ p ∈ E.truncation n T, Real.log (p : ℝ)) / (n : ℝ) - E.partialSum T| < ε / 4 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using
      (E.truncation_log_limit T).eventually (Metric.ball_mem_nhds (E.partialSum T) hε4)
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have ht : ∀ᶠ n : ℕ in atTop,
      Chebyshev.theta ((n : ℝ) / T) / (n : ℝ) < 1 / (T : ℝ) + ε / 4 :=
    (chebyshevTheta_scaled_limit hT').eventually (gt_mem_nhds (by linarith))
  filter_upwards [hl, ht, E.log_product_sandwich_eventually (by linarith) hleft hT]
    with n hclose htheta hsand
  rw [Real.dist_eq]
  obtain ⟨hp₁, hp₂⟩ := abs_lt.mp hpartial
  obtain ⟨hl₁, hl₂⟩ := abs_lt.mp hclose
  apply abs_lt.mpr
  constructor <;> linarith [hsand.1, hsand.2]

end PeriodicPrimeIntervals
end PiIrrationality
