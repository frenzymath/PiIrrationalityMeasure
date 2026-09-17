import Formalization.PrimeNumberTheorem
import Formalization.PrimeSeries

/-! Finite prime intervals and their logarithmic asymptotics for Lemma 3.2. -/

namespace PiIrrationality

open Filter
open scoped Topology

noncomputable def primeBand (lo hi : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊hi⌋₊).filter (fun p => lo < (p : ℝ))

theorem mem_primeBand {lo hi : ℝ} {p : ℕ} (hhi : 0 ≤ hi) :
    p ∈ primeBand lo hi ↔ Nat.Prime p ∧ lo < (p : ℝ) ∧ (p : ℝ) ≤ hi := by
  simp only [primeBand, Finset.mem_filter, Nat.mem_primesLE, Nat.le_floor_iff hhi]
  tauto

theorem primeBand_eq_sdiff {lo hi : ℝ} (hlo : 0 ≤ lo) (hle : lo ≤ hi) :
    primeBand lo hi = Nat.primesLE ⌊hi⌋₊ \ Nat.primesLE ⌊lo⌋₊ := by
  ext p
  rw [mem_primeBand (hlo.trans hle)]
  simp only [Finset.mem_sdiff, Nat.mem_primesLE, Nat.le_floor_iff hlo,
    Nat.le_floor_iff (hlo.trans hle)]
  constructor
  · rintro ⟨hp, hl, hh⟩
    exact ⟨⟨hh, hp⟩, fun h => (not_le.mpr hl) h.1⟩
  · rintro ⟨⟨hh, hp⟩, h⟩
    exact ⟨hp, lt_of_not_ge (fun hl => h ⟨hl, hp⟩), hh⟩

theorem primeBand_log_sum {lo hi : ℝ} (hlo : 0 ≤ lo) (hle : lo ≤ hi) :
    ∑ p ∈ primeBand lo hi, Real.log (p : ℝ) = Chebyshev.theta hi - Chebyshev.theta lo := by
  rw [primeBand_eq_sdiff hlo hle,
    Finset.sum_sdiff_eq_sub (Nat.primesLE_mono (Nat.floor_mono hle)),
    ← Chebyshev.theta_eq_sum_primesLE, ← Chebyshev.theta_eq_sum_primesLE]

theorem prime_logs_nonneg {s : Finset ℕ} (hs : ∀ p ∈ s, Nat.Prime p) :
    0 ≤ ∑ p ∈ s, Real.log (p : ℝ) := by
  apply Finset.sum_nonneg
  intro p hp
  exact Real.log_nonneg (by exact_mod_cast (hs p hp).one_lt.le)

theorem prime_logs_le_theta {s : Finset ℕ} {x : ℝ}
    (hs : ∀ p ∈ s, Nat.Prime p ∧ (p : ℝ) ≤ x) :
    ∑ p ∈ s, Real.log (p : ℝ) ≤ Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_primesLE]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hs p hp).2, (hs p hp).1⟩
  · intro p hp _
    exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le)

theorem chebyshevTheta_scaled_limit {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => Chebyshev.theta ((n : ℝ) / a) / (n : ℝ))
      atTop (𝓝 (1 / a)) := by
  have h := (chebyshevTheta_div_self_limit.comp
    (tendsto_natCast_atTop_atTop.atTop_div_const ha)).div_const a
  simpa only [Function.comp_def, div_div, div_mul_cancel₀ _ ha.ne'] using h

theorem primeBand_reciprocal_limit {ell r : ℝ} (hℓ : 0 < ell) (hr : ell < r) (q : ℕ) :
    Tendsto (fun n : ℕ =>
      (∑ p ∈ primeBand ((n : ℝ) / ((q : ℝ) + r)) ((n : ℝ) / ((q : ℝ) + ell)),
        Real.log (p : ℝ)) / (n : ℝ)) atTop
      (𝓝 (1 / ((q : ℝ) + ell) - 1 / ((q : ℝ) + r))) := by
  have hlpos : 0 < (q : ℝ) + ell := add_pos_of_nonneg_of_pos (Nat.cast_nonneg q) hℓ
  have hrpos : 0 < (q : ℝ) + r := by linarith
  have heq (n : ℕ) :
      (∑ p ∈ primeBand ((n : ℝ) / ((q : ℝ) + r)) ((n : ℝ) / ((q : ℝ) + ell)),
        Real.log (p : ℝ)) / (n : ℝ) =
      Chebyshev.theta ((n : ℝ) / ((q : ℝ) + ell)) / (n : ℝ) -
        Chebyshev.theta ((n : ℝ) / ((q : ℝ) + r)) / (n : ℝ) := by
    rw [primeBand_log_sum (div_nonneg (Nat.cast_nonneg _) hrpos.le)
      (div_le_div_of_nonneg_left (Nat.cast_nonneg n) hlpos (by linarith)), sub_div]
  simp_rw [heq]
  exact (chebyshevTheta_scaled_limit hlpos).sub (chebyshevTheta_scaled_limit hrpos)

theorem periodicSummandReal_eq_sub_inv {ell r : ℝ} (hℓ : 0 < ell) (hr : ell < r) (q : ℕ) :
    periodicSummandReal ell r q = 1 / ((q : ℝ) + ell) - 1 / ((q : ℝ) + r) := by
  have hlpos : 0 < (q : ℝ) + ell := add_pos_of_nonneg_of_pos (Nat.cast_nonneg q) hℓ
  have hrpos : 0 < (q : ℝ) + r := by linarith
  unfold periodicSummandReal
  field_simp
  ring

theorem mem_primeBand_reciprocal {ell r : ℝ} (hℓ : 0 < ell) (hr : ell < r)
    (hr1 : r ≤ 1) {n : ℕ} (hn : 0 < n) (q p : ℕ) :
    p ∈ primeBand ((n : ℝ) / ((q : ℝ) + r)) ((n : ℝ) / ((q : ℝ) + ell)) ↔
      Nat.Prime p ∧ ⌊(n : ℝ) / p⌋ = (q : ℤ) ∧
        Int.fract ((n : ℝ) / p) ∈ Set.Ico ell r := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlpos : 0 < (q : ℝ) + ell := add_pos_of_nonneg_of_pos (Nat.cast_nonneg q) hℓ
  have hrpos : 0 < (q : ℝ) + r := by linarith
  rw [mem_primeBand (div_nonneg hn'.le hlpos.le)]
  constructor
  · rintro ⟨hp, hlow, hhigh⟩
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have h₁ : (q : ℝ) + ell ≤ (n : ℝ) / p := by
      apply (le_div_iff₀ hp').mpr
      have h := (le_div_iff₀ hlpos).mp hhigh
      linarith
    have h₂ : (n : ℝ) / p < (q : ℝ) + r := by
      apply (div_lt_iff₀ hp').mpr
      have h := (div_lt_iff₀ hrpos).mp hlow
      linarith
    have hf : ⌊(n : ℝ) / p⌋ = (q : ℤ) := by
      apply Int.floor_eq_iff.mpr
      simp only [Int.cast_natCast]
      constructor <;> linarith
    refine ⟨hp, hf, ?_⟩
    simp only [Set.mem_Ico, Int.fract, hf, Int.cast_natCast]
    constructor <;> linarith
  · rintro ⟨hp, hf, hmem⟩
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have heq : (n : ℝ) / p = (q : ℝ) + Int.fract ((n : ℝ) / p) := by
      simpa only [hf, Int.cast_natCast] using (Int.floor_add_fract ((n : ℝ) / p)).symm
    exact ⟨hp, (interval_endpoint_equiv hn' hp' (Nat.cast_nonneg q)
      (Int.fract_nonneg _) (Int.fract_lt_one _) heq hℓ hr).mp hmem⟩

end PiIrrationality
