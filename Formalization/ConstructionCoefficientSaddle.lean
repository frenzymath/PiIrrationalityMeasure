import Formalization.ConstructionCoefficientData
import Formalization.ParameterCoefficientSaddle
import Formalization.ParameterChamber

/-! The general positive coefficient saddle is precisely the real root of (6.7). -/

namespace PiIrrationality

open Filter
open scoped Topology

set_option maxHeartbeats 0 in
-- Clearing the Mobius denominators expands the general cubic identity.
theorem constructionMean_cubic_identity {a b c : ℕ} (hc : 0 < c)
    (hd : 2 * c ≤ 2 * a + 4 * b) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    (1 - z ^ 2) * PReal z *
      (PositivePower.mean (2 * a) b (constructionDegree a b c) z - c) =
        (c : ℝ) / 10000 * (1 - z) ^ 6 *
          parameterStationary (constructionParameter a b c)
            (25 * (1 + z) ^ 2 / (1 - z) ^ 2) := by
  have hp : 1 + z ≠ 0 := by linarith
  have hm : 1 - z ≠ 0 := by linarith
  have hP := (PReal_strictPositive z hz0).ne'
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  unfold PositivePower.mean
  rw [constructionDegree_cast hd]
  dsimp [parameterStationary, constructionParameter]
  push_cast
  field_simp [hp, hm, hP, hc']
  dsimp [PReal, PRealPrime]
  ring

theorem constructionMean_cubic_zero_iff {a b c : ℕ} (hc : 0 < c)
    (hd : 2 * c ≤ 2 * a + 4 * b) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    PositivePower.mean (2 * a) b (constructionDegree a b c) z = c ↔
      parameterStationary (constructionParameter a b c)
        (25 * (1 + z) ^ 2 / (1 - z) ^ 2) = 0 := by
  have h := constructionMean_cubic_identity hc hd hz0.le hz1
  have hleft : (1 - z ^ 2) * PReal z ≠ 0 :=
    mul_ne_zero (by nlinarith) (PReal_strictPositive z hz0.le).ne'
  have hright : (c : ℝ) / 10000 * (1 - z) ^ 6 ≠ 0 := by
    have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
    exact mul_ne_zero (div_ne_zero hc' (by norm_num)) (pow_ne_zero _ (by linarith))
  constructor
  · intro hm
    rw [hm, sub_self, mul_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hright
  · intro hp
    rw [hp, mul_zero] at h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hleft)

theorem construction_coefficient_saddle_near_candidate : ∀ᶠ p in 𝓝 candidate,
    ∀ a b c : ℕ, 0 < c → constructionParameter a b c = p →
      Admissible p ∧
      parameterCoefficientSaddle p ∈ Set.Ioo 0 1 ∧
      PositivePower.mean (2 * a) b (constructionDegree a b c)
        (parameterCoefficientSaddle p) = c ∧
      0 < PositivePower.saddleVariance (2 * a) b (constructionDegree a b c)
        (parameterCoefficientSaddle p) ∧
      ∀ z ∈ Set.Ioo (0 : ℝ) 1,
        PositivePower.mean (2 * a) b (constructionDegree a b c) z = c →
          z = parameterCoefficientSaddle p := by
  have hopen : IsOpen {p : ℝ × ℝ | Admissible p} := by
    exact (isOpen_lt continuous_const (continuous_fst.add continuous_snd)).inter
      ((isOpen_lt continuous_const (continuous_snd.const_mul 2)).inter
        ((isOpen_lt (continuous_snd.const_mul 7) continuous_const).inter
          (isOpen_lt continuous_const
            (((continuous_fst.const_mul 2).add (continuous_snd.const_mul 4)).sub
              continuous_const))))
  have hnear : ∀ᶠ p in 𝓝 candidate, Admissible p := hopen.mem_nhds candidate_admissible
  filter_upwards [parameterCoefficientSaddle_near_candidate,
    parameterRealSaddle_near_candidate, hnear] with p hz hy hp
  intro a b c hc he
  have ha : Admissible (constructionParameter a b c) := he ▸ hp
  have hd := constructionDegree_pos hc ha
  have hdc : 2 * c ≤ 2 * a + 4 * b := by
    have hh := (construction_admissible_inequalities hc ha).2.2.2
    omega
  have hm : PositivePower.mean (2 * a) b (constructionDegree a b c)
      (parameterCoefficientSaddle p) = c := by
    apply (constructionMean_cubic_zero_iff hc hdc hz.1.1 hz.1.2).mpr
    rw [he, ← hz.2.1]
    exact hy.1
  refine ⟨hp, hz.1, hm, PositivePower.saddleVariance_pos (2 * a) b hd hz.1.1 hz.1.2, ?_⟩
  intro z hzin hzm
  exact (PositivePower.mean_strictMono (2 * a) b hd).injOn
    ⟨hzin.1.le, hzin.2⟩ ⟨hz.1.1.le, hz.1.2⟩ (hzm.trans hm.symm)

end PiIrrationality
