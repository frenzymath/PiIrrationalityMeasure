import Formalization.ConstructionFiniteSeries
import Formalization.FiniteFieldTransfer

/-! Actual prime deletion (2.15) and reduced-LCM integrality for general exponent triples. -/

namespace PiIrrationality

noncomputable def constructionReducedLcmNat (a b c n : ℕ) : ℕ :=
  lcmRange (constructionDegree a b c * n) / constructionPhi a b c n

noncomputable def constructionReducedLcm (a b c n : ℕ) : ℚ :=
  (lcmRange (constructionDegree a b c * n) : ℚ) / constructionPhi a b c n

theorem constructionRemovablePrime_dvd_scaled_laurent_num {a b c n p : ℕ}
    (hbc : c < 2 * b) (habc : c ≤ a + b) (hn : 0 < n)
    (hp : constructionRemovablePrime a b c n p) (j : ℤ) (hpj : (p : ℤ) ∣ j) :
    (p : ℤ) ∣ ((10 : ℚ) ^ (-j) * constructionLaurentCoeff a b c n j).num := by
  let : Fact p.Prime := ⟨hp.1⟩
  by_cases hj : j ≤ c * (n : ℤ)
  · have hcompat := constructionFiniteField_local_coeff hbc habc hn hp.2.1 j hj
    rw [constructionRemovablePrime_local_coeff_zero hp j hpj] at hcompat
    exact int_dvd_of_zmod_mul_zpow_eq_zero _ j hp.2.1 hcompat.symm
  · rw [constructionLaurentCoeff_zero_of_outside _ _ _ _ _ (lt_of_not_ge hj)]
    simp

theorem constructionRemovablePrime_scaled_laurent_multiple {a b c n p : ℕ}
    (hbc : c < 2 * b) (habc : c ≤ a + b) (hn : 0 < n)
    (hp : constructionRemovablePrime a b c n p) (j : ℤ) (hpj : (p : ℤ) ∣ j) :
    ∃ z : ℤ, (10 : ℚ) ^ (-j) * constructionLaurentCoeff a b c n j =
      (p : ℚ) * (z : ℚ) := by
  obtain ⟨z, hz⟩ := constructionRemovablePrime_dvd_scaled_laurent_num hbc habc hn hp j hpj
  obtain ⟨q, hq⟩ := construction_scaled_laurent_integral hbc habc hn j
  rw [hq, Rat.num_intCast] at hz
  refine ⟨z, ?_⟩
  rw [hq, hz]
  push_cast
  rfl

theorem constructionPhi_pos (a b c n : ℕ) : 0 < constructionPhi a b c n := by
  classical
  unfold constructionPhi
  exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.1.pos)

theorem constructionPhi_coprime_ten (a b c n : ℕ) :
    Nat.Coprime (constructionPhi a b c n) 10 := by
  classical
  unfold constructionPhi
  apply Nat.Coprime.prod_left
  intro p hp
  have hrem : constructionRemovablePrime a b c n p := (Finset.mem_filter.mp hp).2
  have hc2 : Nat.Coprime p 2 :=
    (Nat.coprime_primes hrem.1 (by norm_num)).2 (by have := hrem.2.1; omega)
  have hc5 : Nat.Coprime p 5 :=
    (Nat.coprime_primes hrem.1 (by norm_num)).2 (by have := hrem.2.1; omega)
  simpa using hc2.mul_right hc5

theorem construction_integer_of_Phi_and_ten_power (a b c n : ℕ) (x : ℚ)
    (hPhi : ∃ u : ℤ, (constructionPhi a b c n : ℚ) * x = (u : ℚ))
    (hten : ∃ k : ℕ, ∃ v : ℤ, (10 : ℚ) ^ k * x = (v : ℚ)) :
    ∃ z : ℤ, x = (z : ℚ) := by
  obtain ⟨k, v, hv⟩ := hten
  apply rational_integer_of_coprime_multipliers x (constructionPhi a b c n) (10 ^ k)
    ((constructionPhi_coprime_ten a b c n).pow_right k) hPhi
  exact ⟨v, by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hv⟩

theorem constructionPhi_dvd_int (a b c n : ℕ) (q : ℤ)
    (hq : ∀ p : ℕ, constructionRemovablePrime a b c n p → (p : ℤ) ∣ q) :
    (constructionPhi a b c n : ℤ) ∣ q := by
  classical
  have hpair : (constructionRemovablePrimes a b c n : Set ℕ).Pairwise
      (fun p r => IsCoprime (p : ℤ) (r : ℤ)) := by
    intro p hp r hr hpr
    have hpprime := (Finset.mem_filter.mp hp).2.1
    have hrprime := (Finset.mem_filter.mp hr).2.1
    exact ((Nat.coprime_primes hpprime hrprime).2 hpr).isCoprime
  have hprod : (∏ p ∈ constructionRemovablePrimes a b c n, (p : ℤ)) ∣ q :=
    Finset.prod_dvd_of_coprime hpair
      (fun p hp => hq p (Finset.mem_filter.mp hp).2)
  simpa [constructionPhi] using hprod

theorem constructionPhi_dvd_lcm (a b c n : ℕ) :
    constructionPhi a b c n ∣ lcmRange (constructionDegree a b c * n) := by
  have h := constructionPhi_dvd_int a b c n (lcmRange (constructionDegree a b c * n))
    (fun p hp => by exact_mod_cast dvd_lcmRange _ p hp.1.one_lt.le hp.2.2.2.1)
  exact_mod_cast h

theorem constructionReducedLcmNat_mul_Phi (a b c n : ℕ) :
    constructionReducedLcmNat a b c n * constructionPhi a b c n =
      lcmRange (constructionDegree a b c * n) :=
  Nat.div_mul_cancel (constructionPhi_dvd_lcm a b c n)

theorem constructionReducedLcm_eq_natCast (a b c n : ℕ) :
    constructionReducedLcm a b c n = (constructionReducedLcmNat a b c n : ℚ) := by
  have hPhi : (constructionPhi a b c n : ℚ) ≠ 0 := by
    exact_mod_cast (constructionPhi_pos a b c n).ne'
  unfold constructionReducedLcm
  symm
  apply (eq_div_iff hPhi).2
  exact_mod_cast constructionReducedLcmNat_mul_Phi a b c n

theorem constructionReducedLcm_pos (a b c n : ℕ) : 0 < constructionReducedLcm a b c n := by
  have hL : lcmRange (constructionDegree a b c * n) ≠ 0 := by
    unfold lcmRange
    rw [Finset.lcm_ne_zero_iff]
    intro k hk
    exact Nat.ne_of_gt (Finset.mem_Icc.mp hk).1
  exact div_pos (by exact_mod_cast Nat.pos_of_ne_zero hL)
    (by exact_mod_cast constructionPhi_pos a b c n)

theorem constructionReducedLcmNat_clears {a b c n j q : ℕ}
    (hj0 : j ≠ 0) (hjbound : j ≤ constructionDegree a b c * n)
    (hq : ∀ p : ℕ, constructionRemovablePrime a b c n p → p ∣ j → p ∣ q) :
    j ∣ constructionReducedLcmNat a b c n * q := by
  classical
  have hjL : j ∣ lcmRange (constructionDegree a b c * n) :=
    dvd_lcmRange _ _ (Nat.one_le_iff_ne_zero.mpr hj0) hjbound
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).2
  intro p k hp hpkj
  by_cases hk0 : k = 0
  · simp [hk0]
  have hpj : p ∣ j := (dvd_pow_self p hk0).trans hpkj
  by_cases hrem : constructionRemovablePrime a b c n p
  · have hklt : k < 2 := by
      by_contra hk
      have hp2j : p ^ 2 ∣ j := (pow_dvd_pow p (by omega : 2 ≤ k)).trans hpkj
      have hp2le := Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) hp2j
      have hp2gt := Nat.sqrt_lt'.mp hrem.2.2.1
      omega
    have hk1 : k = 1 := by omega
    simpa [hk1] using dvd_mul_of_dvd_right (hq p hrem hpj) (constructionReducedLcmNat a b c n)
  · have hcop : Nat.Coprime (p ^ k) (constructionPhi a b c n) := by
      unfold constructionPhi
      apply Nat.Coprime.prod_right
      intro r hr
      have hrrem : constructionRemovablePrime a b c n r := (Finset.mem_filter.mp hr).2
      have hpr : p ≠ r := by
        intro heq
        exact hrem (heq ▸ hrrem)
      exact ((Nat.coprime_primes hp hrrem.1).2 hpr).pow_left k
    have hpkL : p ^ k ∣ constructionReducedLcmNat a b c n * constructionPhi a b c n := by
      rw [constructionReducedLcmNat_mul_Phi]
      exact hpkj.trans hjL
    exact dvd_mul_of_dvd_left (hcop.dvd_of_dvd_mul_right hpkL) q

theorem constructionReducedLcm_mul_div_integral {a b c n : ℕ} (j q : ℤ)
    (hj0 : j ≠ 0) (hjbound : j.natAbs ≤ constructionDegree a b c * n)
    (hq : ∀ p : ℕ, constructionRemovablePrime a b c n p → (p : ℤ) ∣ j → (p : ℤ) ∣ q) :
    ∃ z : ℤ, constructionReducedLcm a b c n * (q : ℚ) / (j : ℚ) = (z : ℚ) := by
  have hnat : j.natAbs ∣ constructionReducedLcmNat a b c n * q.natAbs := by
    apply constructionReducedLcmNat_clears (Int.natAbs_ne_zero.mpr hj0) hjbound
    intro p hp hpj
    exact Int.natCast_dvd.mp (hq p hp (Int.natCast_dvd.mpr hpj))
  have hint : j ∣ (constructionReducedLcmNat a b c n : ℤ) * q := by
    apply Int.natAbs_dvd_natAbs.mp
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    exact hnat
  obtain ⟨z, hz⟩ := hint
  refine ⟨z, ?_⟩
  rw [constructionReducedLcm_eq_natCast]
  apply (div_eq_iff (by exact_mod_cast hj0 : (j : ℚ) ≠ 0)).2
  exact_mod_cast (hz.trans (mul_comm j z))

theorem construction_reduced_laurent_integrality {a b c n : ℕ}
    (hbc : c < 2 * b) (habc : c ≤ a + b) (hn : 0 < n) :
    (∃ L : ℤ, constructionReducedLcm a b c n = (L : ℚ)) ∧
      (∀ j : ℤ, j.natAbs ≤ constructionDegree a b c * n → j ≠ 0 →
        ∃ z : ℤ, constructionReducedLcm a b c n *
          ((10 : ℚ) ^ (-j) * constructionLaurentCoeff a b c n j) / (j : ℚ) = (z : ℚ)) ∧
      (∃ z : ℤ, constructionLaurentCoeff a b c n 0 / (constructionPhi a b c n : ℚ) =
        (z : ℚ)) := by
  refine ⟨⟨(constructionReducedLcmNat a b c n : ℤ), ?_⟩, ?_, ?_⟩
  · simpa only [Int.cast_natCast] using constructionReducedLcm_eq_natCast a b c n
  · intro j hj hj0
    obtain ⟨q, hq⟩ := construction_scaled_laurent_integral hbc habc hn j
    rw [hq]
    apply constructionReducedLcm_mul_div_integral j q hj0 hj
    intro p hp hpj
    simpa only [hq, Rat.num_intCast] using
      constructionRemovablePrime_dvd_scaled_laurent_num hbc habc hn hp j hpj
  · obtain ⟨q, hq⟩ := construction_scaled_laurent_integral hbc habc hn 0
    have hc0 : constructionLaurentCoeff a b c n 0 = (q : ℚ) := by simpa using hq
    have hd := constructionPhi_dvd_int a b c n q (fun p hp => by
      simpa [hc0] using
        constructionRemovablePrime_dvd_scaled_laurent_num hbc habc hn hp 0 (dvd_zero _))
    obtain ⟨z, hz⟩ := hd
    refine ⟨z, ?_⟩
    rw [hc0]
    apply (div_eq_iff (by exact_mod_cast (constructionPhi_pos a b c n).ne' :
      (constructionPhi a b c n : ℚ) ≠ 0)).2
    exact_mod_cast (hz.trans (mul_comm (constructionPhi a b c n : ℤ) z))

end PiIrrationality
