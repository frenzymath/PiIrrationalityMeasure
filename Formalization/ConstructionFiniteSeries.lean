import Formalization.ConstructionFiniteField
import Formalization.ConstructionScaledLaurent
import Formalization.FiniteFieldScaledSeries

/-! Coefficient comparison between the actual scaled integers and finite-field local series. -/

namespace PiIrrationality

noncomputable def constructionFiniteSeries (a b c n p : ℕ) [Fact p.Prime] :
    PowerSeries (ZMod p) :=
  PowerSeries.map (Int.castRingHom (ZMod p))
    (Polynomial.toPowerSeries (constructionScaledNumerator a b n)) *
      (PowerSeries.invOneSubPow (ZMod p) (c * n + 1)).val

theorem constructionFiniteSeries_coeff (a b c n p k : ℕ) [Fact p.Prime] :
    (constructionFiniteSeries a b c n p).coeff k =
      (constructionScaledCoreInt a b c n k : ZMod p) := by
  unfold constructionFiniteSeries constructionScaledCoreInt
  rw [PowerSeries.coeff_mul]
  have hsum := Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j : ℕ =>
      (PowerSeries.coeff i)
          (PowerSeries.map (Int.castRingHom (ZMod p))
            (Polynomial.toPowerSeries (constructionScaledNumerator a b n))) *
        (PowerSeries.coeff j) (PowerSeries.invOneSubPow (ZMod p) (c * n + 1)).val) k
  rw [hsum]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [PowerSeries.coeff_map, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
    Polynomial.coeff_coe]
  simp only [PowerSeries.coeff_mk]
  rw [Nat.choose_symm_add]
  have heval : (Polynomial.hasseDeriv i (constructionScaledNumerator a b n)).eval 0 =
      (constructionScaledNumerator a b n).coeff i := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    simp [Polynomial.hasseDeriv_coeff]
  rw [heval]
  rfl

theorem constructionFiniteSeries_rescale (a b c n p : ℕ) [Fact p.Prime] (s : ZMod p) :
    HahnSeries.ofPowerSeries ℤ (ZMod p)
        (PowerSeries.rescale s (constructionFiniteSeries a b c n p)) =
      let x : LaurentSeries (ZMod p) := HahnSeries.single 1 s
      (2 * x - 1) ^ (2 * a * n) *
        (5 * x ^ 2 - 4 * x + 1) ^ (b * n) *
        (5 * x ^ 2 - 6 * x + 2) ^ (b * n) * ((1 - x) ^ (c * n + 1))⁻¹ := by
  let f : PowerSeries (ZMod p) →+* LaurentSeries (ZMod p) :=
    (HahnSeries.ofPowerSeries ℤ (ZMod p)).comp (PowerSeries.rescale s)
  have hX : f PowerSeries.X = HahnSeries.single 1 s := by
    dsimp [f]
    rw [PowerSeries.rescale_X, map_mul, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_X]
    simp [HahnSeries.C_apply, HahnSeries.single_mul_single]
  have hinv : f (PowerSeries.invOneSubPow (ZMod p) (c * n + 1)).val =
      ((1 - HahnSeries.single 1 s) ^ (c * n + 1))⁻¹ := by
    have h := congrArg f (PowerSeries.invOneSubPow (ZMod p) (c * n + 1)).val_inv
    rw [PowerSeries.invOneSubPow_inv_eq_one_sub_pow, map_mul, map_pow,
      map_sub, map_one, hX] at h
    exact eq_inv_of_mul_eq_one_left h
  change f (constructionFiniteSeries a b c n p) = _
  unfold constructionFiniteSeries
  rw [map_mul, hinv]
  congr 1
  change f (PowerSeries.map (Int.castRingHom (ZMod p))
    (Polynomial.coeToPowerSeries.ringHom (constructionScaledNumerator a b n))) = _
  simp only [constructionScaledNumerator, Polynomial.coe_X,
    map_mul, map_pow, map_sub, map_add, map_one, map_ofNat,
    Polynomial.coeToPowerSeries.ringHom_apply, PowerSeries.map_X, hX]

theorem construction_scaled_constant_int {a b c n : ℕ}
    (hbc : c < 2 * b) (habc : c ≤ a + b) (hn : 0 < n) :
    (5 : ℤ) * 5 ^ (2 * a * n) * 20 ^ (2 * (b * n)) =
      10 ^ (2 * (c * n) + 1) *
        (2 ^ ((4 * b - 2 * c) * n - 1) * 5 ^ (2 * (a + b - c) * n)) := by
  have h := (div_eq_iff (by positivity : (10 : ℝ) ^ (c * n + 1) ≠ 0)).1
    (construction_scaled_constant hbc habc hn)
  have h' : (5 : ℝ) * 5 ^ (2 * a * n) * 20 ^ (2 * (b * n)) =
      10 ^ (2 * (c * n) + 1) *
        (2 ^ ((4 * b - 2 * c) * n - 1) * 5 ^ (2 * (a + b - c) * n)) := by
    rw [h, show 2 * (c * n) + 1 = c * n + (c * n + 1) by omega, pow_add]
    ring
  exact_mod_cast h'

theorem construction_scaled_numerator_identity {K : Type*} [CommRing K]
    {a b c n : ℕ} (hbc : c < 2 * b) (habc : c ≤ a + b) (hn : 0 < n) (x : K) :
    5 * (5 * (2 * x - 1)) ^ (2 * a * n) *
        ((5 * (2 * x - 1)) ^ 4 + 6 * (5 * (2 * x - 1)) ^ 2 + 25) ^ (b * n) =
      10 ^ (2 * (c * n) + 1) *
        (2 ^ ((4 * b - 2 * c) * n - 1) * 5 ^ (2 * (a + b - c) * n)) *
        ((2 * x - 1) ^ (2 * a * n) *
          (5 * x ^ 2 - 4 * x + 1) ^ (b * n) *
          (5 * x ^ 2 - 6 * x + 2) ^ (b * n)) := by
  have hc := congrArg (Int.castRingHom K) (construction_scaled_constant_int hbc habc hn)
  simp only [map_mul, map_pow, map_ofNat] at hc
  rw [show (5 * (2 * x - 1)) ^ 4 + 6 * (5 * (2 * x - 1)) ^ 2 + 25 =
      (20 * (5 * x ^ 2 - 4 * x + 1)) * (20 * (5 * x ^ 2 - 6 * x + 2)) by ring]
  simp only [mul_pow]
  calc
    _ = (5 * 5 ^ (2 * a * n) * 20 ^ (2 * (b * n))) *
        ((2 * x - 1) ^ (2 * a * n) *
          (5 * x ^ 2 - 4 * x + 1) ^ (b * n) *
          (5 * x ^ 2 - 6 * x + 2) ^ (b * n)) := by
      rw [show 2 * (b * n) = b * n + b * n by omega, pow_add]
      ring
    _ = _ := by rw [hc]

theorem constructionFiniteField_local_series {a b c n p : ℕ} [Fact p.Prime]
    (hbc : c < 2 * b) (habc : c ≤ a + b) (hn : 0 < n) (hp : 5 < p) :
    localLaurent (-5 : ZMod p) (constructionFiniteFieldRational a b c n p) =
      HahnSeries.single (-(c * n + 1 : ℕ) : ℤ)
        ((10 : ZMod p) ^ (c * n) *
          (2 ^ ((4 * b - 2 * c) * n - 1) * 5 ^ (2 * (a + b - c) * n))) *
      HahnSeries.ofPowerSeries ℤ (ZMod p)
        (PowerSeries.rescale (10 : ZMod p)⁻¹ (constructionFiniteSeries a b c n p)) := by
  let X : LaurentSeries (ZMod p) := HahnSeries.single 1 1
  let x : LaurentSeries (ZMod p) := HahnSeries.single 1 (10 : ZMod p)⁻¹
  have h10 : (10 : LaurentSeries (ZMod p)) ≠ 0 := by
    have h := (algebraMap (ZMod p) (LaurentSeries (ZMod p))).injective.ne
      (zmod_ten_ne_zero hp)
    simpa only [map_ofNat, map_zero] using h
  have hx : X = 10 * x := by
    dsimp [X, x]
    have h10C : (10 : LaurentSeries (ZMod p)) = HahnSeries.single 0 (10 : ZMod p) := by
      simpa using (map_ofNat (HahnSeries.C : ZMod p →+* LaurentSeries (ZMod p)) 10).symm
    rw [h10C, HahnSeries.single_mul_single, zero_add, mul_inv_cancel₀ (zmod_ten_ne_zero hp)]
  have ht : X - 5 = 5 * (2 * x - 1) := by rw [hx]; ring
  have hden : 25 - (X - 5) ^ 2 = X * (10 * (1 - x)) := by rw [hx]; ring
  have hnum := construction_scaled_numerator_identity hbc habc hn x
  rw [← ht] at hnum
  rw [constructionFiniteSeries_rescale]
  unfold constructionFiniteFieldRational
  rw [localLaurent_div]
  simp only [localPolynomial, deletionNumerator, deletionDenominator, map_mul, map_pow,
    map_add, map_sub, Polynomial.aeval_X, map_ofNat, map_neg,
    ← sub_eq_add_neg, show 2 * (a * n) = 2 * a * n by ring]
  change (5 * (X - 5) ^ (2 * a * n) *
      ((X - 5) ^ 4 + 6 * (X - 5) ^ 2 + 25) ^ (b * n)) /
      (25 - (X - 5) ^ 2) ^ (c * n + 1) = _
  rw [hnum, hden]
  have hsingle : HahnSeries.single (-(c * n + 1 : ℕ) : ℤ)
      ((10 : ZMod p) ^ (c * n) *
        (2 ^ ((4 * b - 2 * c) * n - 1) * 5 ^ (2 * (a + b - c) * n))) =
      (10 : LaurentSeries (ZMod p)) ^ (c * n) *
        (2 ^ ((4 * b - 2 * c) * n - 1) * 5 ^ (2 * (a + b - c) * n)) *
          (X ^ (c * n + 1))⁻¹ := by
    rw [← zpow_natCast X (c * n + 1), ← zpow_neg]
    dsimp [X]
    rw [← RatFunc.single_zpow]
    have hC : (10 : LaurentSeries (ZMod p)) ^ (c * n) *
        (2 ^ ((4 * b - 2 * c) * n - 1) * 5 ^ (2 * (a + b - c) * n)) =
        HahnSeries.C ((10 : ZMod p) ^ (c * n) *
          (2 ^ ((4 * b - 2 * c) * n - 1) * 5 ^ (2 * (a + b - c) * n))) := by
      simp only [map_mul, map_pow, map_ofNat]
    rw [hC, HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
  rw [hsingle]
  simp only [mul_pow, div_eq_mul_inv, mul_inv]
  rw [show 2 * (c * n) + 1 = c * n + (c * n + 1) by omega, pow_add]
  have hcancel : (10 : LaurentSeries (ZMod p)) ^ (c * n + 1) *
      (10 ^ (c * n + 1))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ h10)
  calc
    _ = (10 ^ (c * n + 1) * (10 ^ (c * n + 1))⁻¹) *
        (10 ^ (c * n) *
          (2 ^ ((4 * b - 2 * c) * n - 1) * 5 ^ (2 * (a + b - c) * n)) *
        (X ^ (c * n + 1))⁻¹ *
        ((2 * x - 1) ^ (2 * a * n) *
          (5 * x ^ 2 - 4 * x + 1) ^ (b * n) *
          (5 * x ^ 2 - 6 * x + 2) ^ (b * n) *
          ((1 - x) ^ (c * n + 1))⁻¹)) := by ring
    _ = _ := by rw [hcancel, one_mul]

theorem constructionFiniteField_local_coeff {a b c n p : ℕ} [Fact p.Prime]
    (hbc : c < 2 * b) (habc : c ≤ a + b) (hn : 0 < n) (hp : 5 < p)
    (j : ℤ) (hj : j ≤ c * (n : ℤ)) :
    (localLaurent (-5 : ZMod p) (constructionFiniteFieldRational a b c n p)).coeff
      (-j - 1) =
      (((10 : ℚ) ^ (-j) * constructionLaurentCoeff a b c n j).num : ZMod p) *
        (10 : ZMod p) ^ j := by
  let k := (c * (n : ℤ) - j).toNat
  have hk : (k : ℤ) = c * (n : ℤ) - j := Int.toNat_of_nonneg (by omega)
  rw [constructionFiniteField_local_series hbc habc hn hp, HahnSeries.coeff_single_mul]
  have hindex : -j - 1 - (-(c * n + 1 : ℕ) : ℤ) = (k : ℤ) := by push_cast; omega
  rw [hindex, LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_rescale,
    constructionFiniteSeries_coeff, ← constructionScaledCoeffInt_eq_actual hbc habc hn j hj,
    Rat.num_intCast]
  change (10 : ZMod p) ^ (c * n) *
      (2 ^ ((4 * b - 2 * c) * n - 1) * 5 ^ (2 * (a + b - c) * n)) *
      ((10⁻¹) ^ k * (constructionScaledCoreInt a b c n k : ZMod p)) =
        (constructionScaledCoeffInt a b c n k : ZMod p) * 10 ^ j
  have hpow : (10 : ZMod p) ^ (c * n) * (10⁻¹) ^ k = (10 : ZMod p) ^ j := by
    rw [inv_pow, ← zpow_natCast (10 : ZMod p) (c * n),
      ← zpow_natCast (10 : ZMod p) k, ← zpow_neg,
      ← zpow_add₀ (zmod_ten_ne_zero hp)]
    congr 1
    push_cast
    omega
  unfold constructionScaledCoeffInt
  push_cast
  calc
    _ = ((10 : ZMod p) ^ (c * n) * (10⁻¹) ^ k) *
        (2 ^ ((4 * b - 2 * c) * n - 1) * 5 ^ (2 * (a + b - c) * n) *
          (constructionScaledCoreInt a b c n k : ZMod p)) := by ring
    _ = _ := by rw [hpow]; ring

end PiIrrationality
