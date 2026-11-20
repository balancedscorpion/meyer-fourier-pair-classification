module

public import MeyerGeneralProblem.Carrier.CoefficientTail
public import MeyerGeneralProblem.Cross.CompactRemainder

@[expose] public section

/-!
# Norm-controlled extensions of actual coefficient kernels

An injective coordinate inclusion has an isometric synthesis. Extending
an operator by this synthesis preserves its original kernel entries and
does not increase its norm. The final compactness adapter uses genuine
two-sided finite-tail restrictions and does not assume self-adjointness.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped lp

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- The genuine extension-by-zero synthesis for an injective coordinate map. -/
def coefficientInjection (e : ι ↪ κ) : CoefficientSpace ι →L[ℂ] CoefficientSpace κ :=
  ((coefficientBesselAnalysis (ι := κ)).reindex e).synthesis

/-- Injective synthesis retains each exact original coordinate atom. -/
theorem coefficientInjection_coefficientAtom (e : ι ↪ κ) (i : ι) :
    coefficientInjection e (coefficientAtom i)=coefficientAtom (e i) :=
  BesselAnalysis.synthesis_coefficientAtom _ i

/-- Restriction after an injective synthesis is exactly the identity. -/
theorem coefficientInjection_adjoint_comp_self (e : ι ↪ κ) :
    (coefficientInjection e).adjoint ∘L coefficientInjection e=1 := by
  apply ContinuousLinearMap.ext_on
  · rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact coefficientAtom_dense_span
  · rintro _ ⟨i,rfl⟩
    apply (coefficientHilbertBasis ι).repr.injective
    apply lp.ext
    funext j
    rw [(coefficientHilbertBasis ι).repr_apply_apply,
      (coefficientHilbertBasis ι).repr_apply_apply]
    change inner ℂ (coefficientAtom j)
      ((coefficientInjection e).adjoint (coefficientInjection e (coefficientAtom i))) =
      inner ℂ (coefficientAtom j) (coefficientAtom i)
    rw [ContinuousLinearMap.adjoint_inner_right,
      coefficientInjection_coefficientAtom,coefficientInjection_coefficientAtom]
    exact (orthonormal_iff_ite.mp (coefficientHilbertBasis κ).orthonormal (e j) (e i)).trans
      (by simpa only [e.injective.eq_iff,coefficientAtom] using
        (orthonormal_iff_ite.mp (coefficientHilbertBasis ι).orthonormal j i).symm)

/-- Restriction sends an included ambient atom back to its actual atom. -/
theorem coefficientInjection_adjoint_coefficientAtom (e : ι ↪ κ) (i : ι) :
    (coefficientInjection e).adjoint (coefficientAtom (e i))=coefficientAtom i := by
  rw [← coefficientInjection_coefficientAtom e i]
  exact congrArg (fun A : CoefficientSpace ι →L[ℂ] CoefficientSpace ι => A (coefficientAtom i))
    (coefficientInjection_adjoint_comp_self e)

/-- The actual coordinate injection is norm preserving. -/
theorem coefficientInjection_norm (e : ι ↪ κ) (x : CoefficientSpace ι) :
    ‖coefficientInjection e x‖=‖x‖ :=
  (coefficientInjection e).norm_map_iff_adjoint_comp_self.mpr
    (coefficientInjection_adjoint_comp_self e) x

/-- The inclusion operator has norm at most one, also in the empty case. -/
theorem norm_coefficientInjection_le_one (e : ι ↪ κ) : ‖coefficientInjection e‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [coefficientInjection_norm,one_mul]

/-- Extend an actual coefficient operator by zero along an injective index map. -/
def extendCoefficientKernel (e : ι ↪ κ)
    (A : CoefficientSpace ι →L[ℂ] CoefficientSpace ι) :
    CoefficientSpace κ →L[ℂ] CoefficientSpace κ :=
  coefficientInjection e ∘L A ∘L (coefficientInjection e).adjoint

/-- Genuine extension by zero does not enlarge the source ceiling. -/
theorem norm_extendCoefficientKernel_le (e : ι ↪ κ)
    (A : CoefficientSpace ι →L[ℂ] CoefficientSpace ι) : ‖extendCoefficientKernel e A‖ ≤ ‖A‖ := by
  have he := norm_coefficientInjection_le_one e
  have he' : ‖(coefficientInjection e).adjoint‖ ≤ 1 := by simpa using he
  calc
    _ ≤ (‖coefficientInjection e‖*‖A‖)*‖(coefficientInjection e).adjoint‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (1*‖A‖)*1 := mul_le_mul
      (mul_le_mul_of_nonneg_right he (norm_nonneg _)) he' (norm_nonneg _) (by positivity)
    _ = ‖A‖ := by ring

/-- Every included entry of the extended operator is the original entry. -/
theorem extendCoefficientKernel_entry (e : ι ↪ κ)
    (A : CoefficientSpace ι →L[ℂ] CoefficientSpace ι) (i j : ι) :
    inner ℂ (coefficientAtom (e i)) (extendCoefficientKernel e A (coefficientAtom (e j))) =
      inner ℂ (coefficientAtom i) (A (coefficientAtom j)) := by
  simp only [extendCoefficientKernel,ContinuousLinearMap.comp_apply,
    coefficientInjection_adjoint_coefficientAtom]
  rw [← ContinuousLinearMap.adjoint_inner_left,coefficientInjection_adjoint_coefficientAtom]

/-- Inverse-small genuine cofinite restrictions make an arbitrary bounded
coefficient operator compact; no symmetry or adjoint estimate is required. -/
theorem isCompactOperator_of_inverse_tailRestriction_bound
    (A : CoefficientSpace ι →L[ℂ] CoefficientSpace ι)
    (F : ℕ → Finset ι) {C : ℝ} (hC : 0 ≤ C)
    (htail : ∀ n, ‖(tailCoefficientEmbedding (F n)).adjoint ∘L A ∘L
        tailCoefficientEmbedding (F n)‖ ≤ C/((n:ℝ)+1)) : IsCompactOperator A := by
  apply compact_of_inverse_tail_bound A (fun n => finiteCentralTruncation A (F n)) C hC
    (fun n => finiteCentralTruncation_isCompact A (F n))
  intro n
  rw [norm_finiteCentralTruncation_sub]
  have heq : cofiniteCoordinateCompression A (F n) =
      extendTailOperator (F n) ((tailCoefficientEmbedding (F n)).adjoint ∘L A ∘L
        tailCoefficientEmbedding (F n)) := by
    unfold cofiniteCoordinateCompression cofiniteCoordinateProjection extendTailOperator
    rw [← tailCoefficientEmbedding_comp_adjoint]
    simp only [ContinuousLinearMap.comp_assoc]
  rw [heq,← div_eq_mul_one_div]
  exact (norm_extendTailOperator_le _ _).trans (htail n)

end

end MeyerGeneralProblem
