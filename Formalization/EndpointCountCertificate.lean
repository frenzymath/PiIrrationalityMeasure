import Formalization.EndpointCountData

/-! Kernel-checked counts of the actual endpoint germs in twelve interior directions. -/

namespace PiIrrationality

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem count_sector0 : ∀ T : SavingEndpointType,
    candidateEndpointCount (candidateSectorDirection 0) T = candidateExpectedCount 0 T := by
  decide +kernel

private theorem count_sector1 : ∀ T : SavingEndpointType,
    candidateEndpointCount (candidateSectorDirection 1) T = candidateExpectedCount 1 T := by
  decide +kernel

private theorem count_sector2 : ∀ T : SavingEndpointType,
    candidateEndpointCount (candidateSectorDirection 2) T = candidateExpectedCount 2 T := by
  decide +kernel

private theorem count_sector3 : ∀ T : SavingEndpointType,
    candidateEndpointCount (candidateSectorDirection 3) T = candidateExpectedCount 3 T := by
  decide +kernel

private theorem count_sector4 : ∀ T : SavingEndpointType,
    candidateEndpointCount (candidateSectorDirection 4) T = candidateExpectedCount 4 T := by
  decide +kernel

private theorem count_sector5 : ∀ T : SavingEndpointType,
    candidateEndpointCount (candidateSectorDirection 5) T = candidateExpectedCount 5 T := by
  decide +kernel

private theorem count_sector6 : ∀ T : SavingEndpointType,
    candidateEndpointCount (candidateSectorDirection 6) T = candidateExpectedCount 6 T := by
  decide +kernel

private theorem count_sector7 : ∀ T : SavingEndpointType,
    candidateEndpointCount (candidateSectorDirection 7) T = candidateExpectedCount 7 T := by
  decide +kernel

private theorem count_sector8 : ∀ T : SavingEndpointType,
    candidateEndpointCount (candidateSectorDirection 8) T = candidateExpectedCount 8 T := by
  decide +kernel

private theorem count_sector9 : ∀ T : SavingEndpointType,
    candidateEndpointCount (candidateSectorDirection 9) T = candidateExpectedCount 9 T := by
  decide +kernel

private theorem count_sector10 : ∀ T : SavingEndpointType,
    candidateEndpointCount (candidateSectorDirection 10) T = candidateExpectedCount 10 T := by
  decide +kernel

private theorem count_sector11 : ∀ T : SavingEndpointType,
    candidateEndpointCount (candidateSectorDirection 11) T = candidateExpectedCount 11 T := by
  decide +kernel

theorem candidateEndpointCounts_certified (i : Fin 12) (T : SavingEndpointType) :
    candidateEndpointCount (candidateSectorDirection i) T = candidateExpectedCount i T := by
  fin_cases i <;> first
    | exact count_sector0 T
    | exact count_sector1 T
    | exact count_sector2 T
    | exact count_sector3 T
    | exact count_sector4 T
    | exact count_sector5 T
    | exact count_sector6 T
    | exact count_sector7 T
    | exact count_sector8 T
    | exact count_sector9 T
    | exact count_sector10 T
    | exact count_sector11 T

end PiIrrationality
