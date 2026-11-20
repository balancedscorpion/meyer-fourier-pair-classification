module

public import MeyerGeneralProblem.Atomic.BesselSynthesis
public import MeyerGeneralProblem.Hilbert.FiniteCoordinateProjection

@[expose] public section

/-!
# Finite-tail decomposition of coefficient space

Deleting finitely many coordinates from the canonical `ℓ²` basis gives an
isometric synthesis into the original coefficient space.  Its range is
exactly the kernel of the corresponding finite coordinate projection.  This
packages the finite-codimensional bridge needed to transfer a closed-range
estimate from a separated tail back to the full coefficient synthesis.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped lp

variable {ι : Type*} [DecidableEq ι]

/-- Regard the part of a finite ambient coordinate set that survives a
finite deletion as a finite set in the tail index type. -/
def tailFinsetOfFinset (F E : Finset ι) : Finset {i : ι // i ∉ F} :=
  E.subtype fun i ↦ i ∉ F

@[simp]
theorem mem_tailFinsetOfFinset (F E : Finset ι) (i : {i : ι // i ∉ F}) :
    i ∈ tailFinsetOfFinset F E ↔ i.1 ∈ E := by
  simp [tailFinsetOfFinset]

/-- The canonical coefficient basis, bundled as Bessel data with identity
analysis. -/
def coefficientBesselAnalysis :
    BesselAnalysis (coefficientAtom : ι → CoefficientSpace ι) where
  toContinuousLinearMap := 1
  coefficient := by
    intro x i
    change x i = inner ℂ (coefficientAtom i) x
    exact (coefficientHilbertBasis ι).repr_apply_apply x i

/-- Extension by zero from the complement of a finite coordinate set.  It is
defined intrinsically as synthesis of the corresponding canonical basis
subfamily. -/
def tailCoefficientEmbedding (F : Finset ι) :
    CoefficientSpace {i : ι // i ∉ F} →L[ℂ] CoefficientSpace ι :=
  ((coefficientBesselAnalysis (ι := ι)).reindex
    ⟨Subtype.val, Subtype.val_injective⟩).synthesis

@[simp]
theorem tailCoefficientEmbedding_coefficientAtom (F : Finset ι)
    (i : {i : ι // i ∉ F}) :
    tailCoefficientEmbedding F (coefficientAtom i) = coefficientAtom i.val := by
  exact BesselAnalysis.synthesis_coefficientAtom _ i

/-- Extension by zero preserves the `ℓ²` inner product. -/
theorem tailCoefficientEmbedding_adjoint_comp_self (F : Finset ι) :
    (tailCoefficientEmbedding F).adjoint.comp (tailCoefficientEmbedding F) = 1 := by
  apply ContinuousLinearMap.ext_on
  · rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact coefficientAtom_dense_span
  · rintro _ ⟨i, rfl⟩
    apply (coefficientHilbertBasis {i : ι // i ∉ F}).repr.injective
    apply lp.ext
    funext j
    simp only [ContinuousLinearMap.comp_apply, one_apply_eq_self]
    rw [(coefficientHilbertBasis {i : ι // i ∉ F}).repr_apply_apply,
      (coefficientHilbertBasis {i : ι // i ∉ F}).repr_apply_apply]
    rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ
        (tailCoefficientEmbedding F (coefficientAtom j))
        (tailCoefficientEmbedding F (coefficientAtom i)) =
      inner ℂ (coefficientAtom j) (coefficientAtom i)
    rw [tailCoefficientEmbedding_coefficientAtom,
      tailCoefficientEmbedding_coefficientAtom]
    change inner ℂ ((coefficientHilbertBasis ι) j.val)
        ((coefficientHilbertBasis ι) i.val) =
      inner ℂ ((coefficientHilbertBasis {i : ι // i ∉ F}) j)
        ((coefficientHilbertBasis {i : ι // i ∉ F}) i)
    rw [orthonormal_iff_ite.mp
        (coefficientHilbertBasis ι).orthonormal j.val i.val,
      orthonormal_iff_ite.mp
        (coefficientHilbertBasis {i : ι // i ∉ F}).orthonormal j i]
    simp only [Subtype.coe_injective.eq_iff]

/-- The adjoint of extension by zero restricts a canonical ambient atom to
the tail, and kills a deleted coordinate. -/
theorem tailCoefficientEmbedding_adjoint_coefficientAtom
    (F : Finset ι) (j : ι) :
    (tailCoefficientEmbedding F).adjoint (coefficientAtom j) =
      if hj : j ∉ F then coefficientAtom (⟨j, hj⟩ : {i : ι // i ∉ F})
      else 0 := by
  apply (coefficientHilbertBasis {i : ι // i ∉ F}).repr.injective
  apply lp.ext
  funext i
  rw [(coefficientHilbertBasis {i : ι // i ∉ F}).repr_apply_apply,
    (coefficientHilbertBasis {i : ι // i ∉ F}).repr_apply_apply,
    ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (tailCoefficientEmbedding F (coefficientAtom i))
      (coefficientAtom j) =
    inner ℂ (coefficientAtom i)
      (if hj : j ∉ F then coefficientAtom ⟨j, hj⟩ else 0)
  rw [tailCoefficientEmbedding_coefficientAtom]
  by_cases hj : j ∉ F
  · rw [dite_eq_left hj]
    unfold coefficientAtom
    rw [orthonormal_iff_ite.mp
        (coefficientHilbertBasis ι).orthonormal i.1 j,
      orthonormal_iff_ite.mp
        (coefficientHilbertBasis {i : ι // i ∉ F}).orthonormal i ⟨j, hj⟩]
    simp only [Subtype.ext_iff]
  · rw [dite_eq_right hj, inner_zero_right]
    unfold coefficientAtom
    rw [orthonormal_iff_ite.mp
      (coefficientHilbertBasis ι).orthonormal i.1 j]
    have hij : i.1 ≠ j := by
      intro h
      apply hj
      simpa [h] using i.2
    simp [hij]

/-- Extension followed by restriction is exactly the orthogonal projection
onto the complement of the deleted coordinates. -/
theorem tailCoefficientEmbedding_comp_adjoint
    (F : Finset ι) :
    tailCoefficientEmbedding F ∘L (tailCoefficientEmbedding F).adjoint =
      1 - finiteCoordinateProjection F := by
  apply ContinuousLinearMap.ext_on
  · rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact coefficientAtom_dense_span
  · rintro _ ⟨j, rfl⟩
    rw [ContinuousLinearMap.comp_apply,
      tailCoefficientEmbedding_adjoint_coefficientAtom,
      sub_apply, one_apply_eq_self,
      finiteCoordinateProjection_coefficientAtom]
    by_cases hj : j ∈ F
    · simp [hj]
    · simp [hj]

/-- Extension by zero preserves norms. -/
theorem tailCoefficientEmbedding_norm (F : Finset ι)
    (c : CoefficientSpace {i : ι // i ∉ F}) :
    ‖tailCoefficientEmbedding F c‖ = ‖c‖ := by
  exact (tailCoefficientEmbedding F).norm_map_iff_adjoint_comp_self.mpr
    (tailCoefficientEmbedding_adjoint_comp_self F) c

/-- Extend a bounded tail operator by zero across the finitely many deleted
ambient coordinates. -/
def extendTailOperator (F : Finset ι)
    (T : CoefficientSpace {i : ι // i ∉ F} →L[ℂ]
      CoefficientSpace {i : ι // i ∉ F}) :
    CoefficientSpace ι →L[ℂ] CoefficientSpace ι :=
  tailCoefficientEmbedding F ∘L T ∘L
    (tailCoefficientEmbedding F).adjoint

/-- Extension by zero does not increase operator norm. -/
theorem norm_extendTailOperator_le (F : Finset ι)
    (T : CoefficientSpace {i : ι // i ∉ F} →L[ℂ]
      CoefficientSpace {i : ι // i ∉ F}) :
    ‖extendTailOperator F T‖ ≤ ‖T‖ := by
  let E : CoefficientSpace {i : ι // i ∉ F} →L[ℂ]
      CoefficientSpace ι := tailCoefficientEmbedding F
  have hE : ‖E‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
    intro c
    simpa only [E, one_mul] using
      le_of_eq (tailCoefficientEmbedding_norm F c)
  have hEadj : ‖E.adjoint‖ ≤ 1 := by
    simpa using hE
  have hET : ‖E ∘L T‖ ≤ ‖E‖ * ‖T‖ :=
    ContinuousLinearMap.opNorm_comp_le E T
  have hETE : ‖(E ∘L T) ∘L E.adjoint‖ ≤
      ‖E ∘L T‖ * ‖E.adjoint‖ :=
    ContinuousLinearMap.opNorm_comp_le (E ∘L T) E.adjoint
  calc
    ‖extendTailOperator F T‖ ≤
        ‖E‖ * ‖T‖ * ‖E.adjoint‖ := by
      change ‖(E ∘L T) ∘L E.adjoint‖ ≤ _
      exact hETE.trans
        (mul_le_mul_of_nonneg_right hET (norm_nonneg E.adjoint))
    _ ≤ 1 * ‖T‖ * 1 := by gcongr
    _ = ‖T‖ := by ring

/-- Adjoint commutes with extension by zero. -/
theorem extendTailOperator_adjoint (F : Finset ι)
    (T : CoefficientSpace {i : ι // i ∉ F} →L[ℂ]
      CoefficientSpace {i : ι // i ∉ F}) :
    (extendTailOperator F T).adjoint = extendTailOperator F T.adjoint := by
  unfold extendTailOperator
  rw [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]
  rw [ContinuousLinearMap.comp_assoc]

/-- Extending a compact tail operator by zero preserves compactness. -/
theorem extendTailOperator_isCompact (F : Finset ι)
    (T : CoefficientSpace {i : ι // i ∉ F} →L[ℂ]
      CoefficientSpace {i : ι // i ∉ F})
    (hT : IsCompactOperator T) :
    IsCompactOperator (extendTailOperator F T) := by
  unfold extendTailOperator
  exact (hT.comp_clm (tailCoefficientEmbedding F).adjoint).clm_comp
    (tailCoefficientEmbedding F)

/-- Extension by zero is injective. -/
theorem tailCoefficientEmbedding_injective (F : Finset ι) :
    Function.Injective (tailCoefficientEmbedding F) := by
  intro c d hcd
  apply sub_eq_zero.mp
  have hzero : tailCoefficientEmbedding F (c - d) = 0 := by
    rw [map_sub, hcd, sub_self]
  have hnorm := tailCoefficientEmbedding_norm F (c - d)
  rw [hzero, norm_zero] at hnorm
  exact norm_eq_zero.mp hnorm.symm

/-- Extension by zero has closed range. -/
theorem tailCoefficientEmbedding_isClosed_range (F : Finset ι) :
    IsClosed (Set.range (tailCoefficientEmbedding F)) := by
  let e : CoefficientSpace {i : ι // i ∉ F} →ₗᵢ[ℂ] CoefficientSpace ι :=
    LinearIsometry.mk (tailCoefficientEmbedding F).toLinearMap
      (tailCoefficientEmbedding_norm F)
  exact e.isometry.antilipschitz.isClosed_range
    (tailCoefficientEmbedding F).uniformContinuous

/-- The finite coordinate projection vanishes after extension by zero. -/
theorem finiteCoordinateProjection_comp_tailCoefficientEmbedding
    (F : Finset ι) :
    finiteCoordinateProjection F ∘L tailCoefficientEmbedding F = 0 := by
  apply ContinuousLinearMap.ext_on
  · rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact coefficientAtom_dense_span
  · rintro _ ⟨i, rfl⟩
    simp [ContinuousLinearMap.comp_apply, i.property]

/-- Every extended tail coefficient vector has zero deleted coordinates. -/
theorem tailCoefficientEmbedding_mem_ker (F : Finset ι)
    (c : CoefficientSpace {i : ι // i ∉ F}) :
    tailCoefficientEmbedding F c ∈
    (finiteCoordinateProjection F).toLinearMap.ker := by
  rw [LinearMap.mem_ker]
  have h := congrArg
    (fun T : CoefficientSpace {i : ι // i ∉ F} →L[ℂ]
      CoefficientSpace ι => T c)
    (finiteCoordinateProjection_comp_tailCoefficientEmbedding F)
  change finiteCoordinateProjection F (tailCoefficientEmbedding F c) = 0
  simpa only [ContinuousLinearMap.comp_apply, zero_apply] using h

/-- The extension-by-zero range is exactly the subspace on which all deleted
coordinates vanish. -/
theorem tailCoefficientEmbedding_range_eq_ker (F : Finset ι) :
    (tailCoefficientEmbedding F).range =
      (finiteCoordinateProjection F).ker := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    exact tailCoefficientEmbedding_mem_ker F c
  · intro c hc
    refine ⟨(tailCoefficientEmbedding F).adjoint c, ?_⟩
    apply (coefficientHilbertBasis ι).repr.injective
    apply lp.ext
    funext i
    rw [(coefficientHilbertBasis ι).repr_apply_apply,
      (coefficientHilbertBasis ι).repr_apply_apply]
    change inner ℂ (coefficientAtom i)
        (tailCoefficientEmbedding F
          ((tailCoefficientEmbedding F).adjoint c)) =
      inner ℂ (coefficientAtom i) c
    by_cases hi : i ∈ F
    · have hcZero : inner ℂ (coefficientAtom i) c = 0 := by
        have hPc : finiteCoordinateProjection F c = 0 :=
          LinearMap.mem_ker.mp hc
        have hentry := inner_finiteCoordinateProjection F i c
        rw [hPc, inner_zero_right, ite_eq_left hi] at hentry
        exact hentry.symm
      have hEcKer : tailCoefficientEmbedding F
          ((tailCoefficientEmbedding F).adjoint c) ∈
          (finiteCoordinateProjection F).ker := by
        exact tailCoefficientEmbedding_mem_ker F _
      have hEcZero : inner ℂ (coefficientAtom i)
          (tailCoefficientEmbedding F
            ((tailCoefficientEmbedding F).adjoint c)) = 0 := by
        have hPec : finiteCoordinateProjection F
            (tailCoefficientEmbedding F
              ((tailCoefficientEmbedding F).adjoint c)) = 0 :=
          LinearMap.mem_ker.mp hEcKer
        have hentry := inner_finiteCoordinateProjection F i
          (tailCoefficientEmbedding F
            ((tailCoefficientEmbedding F).adjoint c))
        rw [hPec, inner_zero_right, ite_eq_left hi] at hentry
        exact hentry.symm
      rw [hEcZero, hcZero]
    · let j : {i : ι // i ∉ F} := ⟨i, hi⟩
      let e : CoefficientSpace {i : ι // i ∉ F} →ₗᵢ[ℂ]
          CoefficientSpace ι :=
        LinearIsometry.mk (tailCoefficientEmbedding F).toLinearMap
          (tailCoefficientEmbedding_norm F)
      calc
        inner ℂ (coefficientAtom i)
            (tailCoefficientEmbedding F
              ((tailCoefficientEmbedding F).adjoint c)) =
            inner ℂ (tailCoefficientEmbedding F (coefficientAtom j))
              (tailCoefficientEmbedding F
                ((tailCoefficientEmbedding F).adjoint c)) := by
          rw [tailCoefficientEmbedding_coefficientAtom]
        _ = inner ℂ (coefficientAtom j)
              ((tailCoefficientEmbedding F).adjoint c) := by
          exact e.inner_map_map _ _
        _ = inner ℂ (tailCoefficientEmbedding F (coefficientAtom j)) c :=
          ContinuousLinearMap.adjoint_inner_right _ _ _
        _ = inner ℂ (coefficientAtom i) c := by
          rw [tailCoefficientEmbedding_coefficientAtom]

end

end MeyerGeneralProblem
