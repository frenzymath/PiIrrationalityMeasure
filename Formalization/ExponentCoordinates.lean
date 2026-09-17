import Formalization.LocalOptimality

/-! Strict local minimality in the original exponent coordinates of Theorem 1.2. -/

namespace PiIrrationality

noncomputable def exponentToParameter (a : ℝ × ℝ) : ℝ × ℝ := (a.1 / 2, a.2)

noncomputable def exponentCandidate : ℝ × ℝ :=
  ((1857 : ℝ) / 2785, (1857 : ℝ) / 2785)

theorem exponentToParameter_candidate : exponentToParameter exponentCandidate = candidate := by
  norm_num [exponentToParameter, exponentCandidate, candidate]

theorem exponentToParameter_injective : Function.Injective exponentToParameter := by
  intro a b h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext
  · dsimp [exponentToParameter] at hx
    linarith
  · exact hy

theorem exponentToParameter_norm_sub_le (a b : ℝ × ℝ) :
    ‖exponentToParameter a - exponentToParameter b‖ ≤ ‖a - b‖ := by
  change max |a.1 / 2 - b.1 / 2| |a.2 - b.2| ≤ max |a.1 - b.1| |a.2 - b.2|
  have hx : |a.1 / 2 - b.1 / 2| = |a.1 - b.1| / 2 := by
    rw [← sub_div, abs_div]
    norm_num
  rw [hx]
  exact max_le ((by linarith [abs_nonneg (a.1 - b.1)] :
    |a.1 - b.1| / 2 ≤ |a.1 - b.1|).trans (le_max_left _ _)) (le_max_right _ _)

theorem theorem12_exponent_coordinates :
    StrictLocalMinimizer (parameterAuxiliaryBound ∘ exponentToParameter)
      (Admissible ∘ exponentToParameter) exponentCandidate := by
  obtain ⟨delta, hd, hmin⟩ := parameterAuxiliaryBound_strictLocalMinimizer
  refine ⟨delta, hd, ?_⟩
  intro a ha hne hdist
  change parameterAuxiliaryBound (exponentToParameter exponentCandidate) <
    parameterAuxiliaryBound (exponentToParameter a)
  rw [exponentToParameter_candidate]
  apply hmin _ ha
  · intro h
    apply hne
    apply exponentToParameter_injective
    exact h.trans exponentToParameter_candidate.symm
  · rw [← exponentToParameter_candidate]
    exact (exponentToParameter_norm_sub_le _ _).trans_lt hdist

end PiIrrationality
