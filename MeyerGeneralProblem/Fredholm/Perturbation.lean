module

public import MeyerGeneralProblem.Fredholm.UpperSemiFredholm

@[expose] public section

/-!
# Local stability of upper semi-Fredholmness

A strict lower bound on a fixed finite-codimension subspace survives a smaller
operator-norm perturbation.  The argument never imposes a finite cokernel.
Transport of the extended index along a path is a separate obligation.
-/

namespace MeyerGeneralProblem

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Quantitative lower-bound loss under an operator-norm perturbation. -/
theorem finiteCodimension_lowerBound_perturbation
    (T U : E →L[ℂ] F) (M : ClosedSubmodule ℂ E) {c : ℝ}
    (hbound : ∀ x : M.toSubmodule, c * ‖x‖ ≤ ‖T (x : E)‖) :
    ∀ x : M.toSubmodule,
      (c - ‖U - T‖) * ‖x‖ ≤ ‖U (x : E)‖ := by
  intro x
  have htriangle : ‖T (x : E)‖ ≤ ‖U (x : E)‖ + ‖(U - T) (x : E)‖ := by
    have h := norm_sub_le (U (x : E)) ((U - T) (x : E))
    simpa only [sub_apply, sub_sub_cancel] using h
  have hop := (U - T).le_opNorm (x : E)
  have hb := hbound x
  change ‖(U - T) (x : E)‖ ≤ ‖U - T‖ * ‖x‖ at hop
  nlinarith

/-- Every upper semi-Fredholm operator has an operator-norm neighbourhood
consisting of upper semi-Fredholm operators. -/
theorem IsUpperSemiFredholm.exists_norm_neighbourhood
    {T : E →L[ℂ] F} (hT : IsUpperSemiFredholm T) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ U : E →L[ℂ] F, ‖U - T‖ < ε → IsUpperSemiFredholm U := by
  obtain ⟨M, hM, c, hc, hbound⟩ :=
    hT.exists_finiteCodimension_lowerBound
  refine ⟨c, hc, fun U hU => ?_⟩
  exact isUpperSemiFredholm_of_finiteCodimension_lowerBound U M hM
    (sub_pos.mpr hU) (finiteCodimension_lowerBound_perturbation T U M hbound)

/-- Upper semi-Fredholmness is open in the operator norm topology, without
a finite-dimensional cokernel hypothesis. -/
theorem isOpen_setOf_isUpperSemiFredholm :
    IsOpen {T : E →L[ℂ] F | IsUpperSemiFredholm T} := by
  apply Metric.isOpen_iff.mpr
  intro T hT
  obtain ⟨ε, hε, hball⟩ := hT.exists_norm_neighbourhood
  refine ⟨ε, hε, fun U hU => ?_⟩
  exact hball U (by simpa only [Metric.mem_ball, dist_eq_norm] using hU)

end

end MeyerGeneralProblem
