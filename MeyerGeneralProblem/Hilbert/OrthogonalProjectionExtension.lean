module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

@[expose] public section

/-!
# Square extension from an orthogonally complemented domain

A continuous linear map whose domain is a Hilbert subspace can be extended to
the ambient space by precomposing with the orthogonal projection.  This file
records the exact operator-norm preservation needed to pass from rectangular
reduced operators to square fixed-space operators.
-/

namespace MeyerGeneralProblem

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Extend an operator from an orthogonally complemented subspace to the
ambient space by making it zero on the orthogonal complement. -/
def orthogonalProjectionExtension
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (A : K →L[ℂ] F) : E →L[ℂ] F :=
  A.comp K.orthogonalProjectionOnto

@[simp]
theorem orthogonalProjectionExtension_apply_mem
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (A : K →L[ℂ] F) (x : K) :
    orthogonalProjectionExtension K A (x : E) = A x := by
  simp [orthogonalProjectionExtension]

/-- Orthogonal-projection extension preserves the operator norm exactly. -/
theorem orthogonalProjectionExtension_norm_eq
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (A : K →L[ℂ] F) :
    ‖orthogonalProjectionExtension K A‖ = ‖A‖ := by
  apply le_antisymm
  · calc
      ‖orthogonalProjectionExtension K A‖ ≤
          ‖A‖ * ‖K.orthogonalProjectionOnto‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖A‖ * 1 :=
        mul_le_mul_of_nonneg_left K.orthogonalProjectionOnto_norm_le
          (norm_nonneg A)
      _ = ‖A‖ := mul_one _
  · apply ContinuousLinearMap.opNorm_le_bound _
      (ContinuousLinearMap.opNorm_nonneg _)
    intro x
    calc
      ‖A x‖ = ‖orthogonalProjectionExtension K A (x : E)‖ := by
        rw [orthogonalProjectionExtension_apply_mem]
      _ ≤ ‖orthogonalProjectionExtension K A‖ * ‖(x : E)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖orthogonalProjectionExtension K A‖ * ‖x‖ := by
        rw [Submodule.coe_norm]

end

end MeyerGeneralProblem
