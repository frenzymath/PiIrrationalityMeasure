import Formalization.EndpointCountCertificate
import Formalization.EndpointCountTransfer
import Formalization.EndpointSectorForms

/-! The twelve certified rows are actual endpoint jump sums in every open sector. -/

namespace PiIrrationality

open Filter Set
open scoped Topology

theorem candidateOpenSector_counts_certified {i : Fin 12} {v : ℝ × ℝ}
    (hv : CandidateOpenSector i v) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ T : SavingEndpointType,
      candidateActualJumpCount v T s = (candidateExpectedCount i T : ℝ) := by
  apply eventually_all.mpr
  intro T
  filter_upwards [candidateOpenSector_actualJumpCount hv T] with s hs
  rw [hs, candidateEndpointCounts_certified]

theorem candidateOpenSector_weighted_counts {i : Fin 12} {v : ℝ × ℝ}
    (hv : CandidateOpenSector i v) :
    ∀ᶠ s : ℝ in 𝓝[>] 0,
      candidateActualJumpCount v .A s * savingEndpointVelocity 1857 3714 5570 v .A +
      candidateActualJumpCount v .B s * savingEndpointVelocity 1857 3714 5570 v .B +
      candidateActualJumpCount v .C s * savingEndpointVelocity 1857 3714 5570 v .C +
      candidateActualJumpCount v .Q s * savingEndpointVelocity 1857 3714 5570 v .Q =
        candidateSectorLinearForm i v := by
  filter_upwards [candidateOpenSector_counts_certified hv] with s hs
  simp only [hs, candidateSectorLinearForm_counts]

end PiIrrationality
