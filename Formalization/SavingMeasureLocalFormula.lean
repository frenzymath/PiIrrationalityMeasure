import Formalization.SavingMeasureOpenAffine
import Formalization.SavingPartitionJumpValues
import Formalization.EndpointSectorCounts
import Formalization.EndpointSectorVariation

/-! The actual one-period measure has the uniform local variation from the certified sector table. -/

set_option maxRecDepth 100000

namespace PiIrrationality

open Filter Set
open scoped Topology

theorem eventually_smul_parameterNormOne_lt (v : ℝ × ℝ) {rho : ℝ} (hrho : 0 < rho) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, parameterNormOne (s • v) < rho := by
  have hc : ContinuousAt (fun s : ℝ => parameterNormOne (s • v)) 0 := by
    unfold parameterNormOne
    fun_prop
  exact (hc.eventually_lt_const (by simpa [parameterNormOne] using hrho)).filter_mono
    nhdsWithin_le_nhds

theorem candidatePartitionLinear_eq_sector_form {i : Fin 12}
    (e : CandidateEndpointEnumeration) (w : ℝ × ℝ)
    (hwi : CandidateOpenSector i w) (hw : CandidateOrderedEndpoints e w)
    (hwn : parameterNormOne w ≤ 1 / 100)
    (hscaled : ∀ᶠ s : ℝ in 𝓝[>] 0,
      CandidateOrderedEndpoints e (s • w) ∧ parameterNormOne (s • w) ≤ 1 / 100) :
    ∀ z : ℝ × ℝ,
      candidatePartitionLinear e (candidatePartitionIndicator e w) z = candidateSectorLinearForm i z := by
  have hweight := candidatePartitionLinear_eq_actual_weighted_eventually e w w hw hwn hscaled
  have hcount := candidateOpenSector_counts_certified hwi
  obtain ⟨s, hs, hcounts⟩ := (hweight.and hcount).exists
  intro z
  rw [hs z, hcounts .A, hcounts .B, hcounts .C, hcounts .Q]
  exact candidateSectorLinearForm_counts i z

theorem translatedSavingMeasure_uniform_open_formula :
    ∃ rho : ℝ, 0 < rho ∧ ∀ (i : Fin 12) (z : ℝ × ℝ),
      CandidateOpenSector i z → parameterNormOne z < rho →
        translatedSavingMeasure 1857 3714 5570 z =
          translatedSavingMeasure 1857 3714 5570 0 + candidateSectorLinearForm i z := by
  obtain ⟨rho, hrho, hrho100, hmodel⟩ := translatedSavingMeasure_uniform_open_affine
  refine ⟨rho, hrho, ?_⟩
  intro i
  obtain ⟨e, w, hwi, hwn, hw, hall⟩ := hmodel i
  have hscaled : ∀ᶠ s : ℝ in 𝓝[>] 0,
      CandidateOrderedEndpoints e (s • w) ∧ parameterNormOne (s • w) ≤ 1 / 100 := by
    filter_upwards [self_mem_nhdsWithin, eventually_smul_parameterNormOne_lt w hrho]
      with s hs hsn
    exact ⟨(hall (s • w) (hwi.smul hs) hsn).1, le_trans hsn.le hrho100⟩
  have hlinear := candidatePartitionLinear_eq_sector_form e w hwi hw
    (le_trans hwn.le hrho100) hscaled
  intro z hzi hzn
  rw [(hall z hzi hzn).2, hlinear z]

theorem CandidateOpenSector.toClosed {i : Fin 12} {z : ℝ × ℝ}
    (hz : CandidateOpenSector i z) : CandidateClosedSector i z := by
  rcases hz with ⟨u, t, hu, ht, hz⟩
  exact ⟨u, t, hu.le, ht.le, hz⟩

theorem CandidateClosedSector.add_ray_sum {i : Fin 12} {z : ℝ × ℝ}
    (hz : CandidateClosedSector i z) {s : ℝ} (hs : 0 < s) :
    CandidateOpenSector i
      (z + s • (candidateSectorRayReal i + candidateSectorRayReal (candidateSectorNext i))) := by
  rcases hz with ⟨u, t, hu, ht, rfl⟩
  refine ⟨u + s, t + s, by linarith, by linarith, ?_⟩
  rw [smul_add, add_smul, add_smul]
  abel

theorem translatedSavingMeasure_local_formula :
    ∃ rho : ℝ, 0 < rho ∧ ∀ z : ℝ × ℝ, parameterNormOne z < rho →
      translatedSavingMeasure 1857 3714 5570 z =
        translatedSavingMeasure 1857 3714 5570 0 + candidateSectorVariation z := by
  obtain ⟨rho, hrho, hopen⟩ := translatedSavingMeasure_uniform_open_formula
  refine ⟨rho, hrho, ?_⟩
  intro z hzn
  obtain ⟨i, hi⟩ := candidateClosedSector_cover z
  let d := candidateSectorRayReal i + candidateSectorRayReal (candidateSectorNext i)
  have hpath : Tendsto (fun s : ℝ => z + s • d) (𝓝[>] 0) (𝓝 z) := by
    have hc : ContinuousAt (fun s : ℝ => z + s • d) 0 := by fun_prop
    simpa only [zero_smul, add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, parameterNormOne (z + s • d) < rho := by
    have hc : ContinuousAt (fun s : ℝ => parameterNormOne (z + s • d)) 0 := by
      unfold parameterNormOne
      fun_prop
    exact (hc.eventually_lt_const (by simpa only [zero_smul, add_zero] using hzn)).filter_mono
      nhdsWithin_le_nhds
  have heq : (fun s : ℝ => translatedSavingMeasure 1857 3714 5570 (z + s • d)) =ᶠ[𝓝[>] 0]
      (fun s => translatedSavingMeasure 1857 3714 5570 0 + candidateSectorVariation (z + s • d)) := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with s hs hsn
    have hsi := hi.add_ray_sum hs
    rw [hopen i (z + s • d) hsi hsn, candidateSectorVariation_eq_form hsi.toClosed]
  have hm : Continuous (translatedSavingMeasure 1857 3714 5570) :=
    continuous_translatedSavingMeasure (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd : Continuous (fun x : ℝ × ℝ =>
      translatedSavingMeasure 1857 3714 5570 0 + candidateSectorVariation x) :=
    continuous_const.add continuous_candidateSectorVariation
  exact tendsto_nhds_unique ((hm.tendsto z).comp hpath)
    ((tendsto_congr' heq).mpr ((hd.tendsto z).comp hpath))

theorem translatedSavingMeasure_directional_formula :
    ∃ rho : ℝ, 0 < rho ∧ ∀ v : ℝ × ℝ, parameterNormOne v = 1 →
      ∀ s : ℝ, 0 ≤ s → s ≤ rho →
        translatedSavingMeasure 1857 3714 5570 (s • v) -
          translatedSavingMeasure 1857 3714 5570 0 = s * candidateSectorVariation v := by
  obtain ⟨rho, hrho, hlocal⟩ := translatedSavingMeasure_local_formula
  refine ⟨rho / 2, by positivity, ?_⟩
  intro v hv s hs0 hs
  have hsn : parameterNormOne (s • v) < rho := by
    rw [parameterNormOne_smul, abs_of_nonneg hs0, hv, mul_one]
    linarith
  rw [hlocal (s • v) hsn, candidateSectorVariation_smul v hs0]
  ring

theorem translatedSavingMeasure_local_decrease :
    ∃ rho : ℝ, 0 < rho ∧ ∀ z : ℝ × ℝ, parameterNormOne z < rho →
      translatedSavingMeasure 1857 3714 5570 z ≤
        translatedSavingMeasure 1857 3714 5570 0 -
          (557 : ℝ) / 4139253 * parameterNormOne z := by
  obtain ⟨rho, hrho, hlocal⟩ := translatedSavingMeasure_local_formula
  refine ⟨rho, hrho, ?_⟩
  intro z hz
  rw [hlocal z hz]
  have h := candidateSectorVariation_bound z
  linarith

end PiIrrationality
