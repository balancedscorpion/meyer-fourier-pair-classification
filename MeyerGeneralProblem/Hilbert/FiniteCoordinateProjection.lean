module

public import MeyerGeneralProblem.Atomic.RieszSynthesis
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Perturbation.StrictByFinite

@[expose] public section

/-!
# Finite coordinate projections on canonical coefficient space

This module collects the generic finite-dimensional compactness facts and the
finite-coordinate projection on `ℓ²`. It sits below both the carrier-tail and
cross-operator layers.
-/

namespace MeyerGeneralProblem

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Every bounded operator into a finite-dimensional complex normed space is
compact. -/
theorem isCompactOperator_of_finiteDimensional_codomain
    [FiniteDimensional ℂ F] (T : E →L[ℂ] F) :
    IsCompactOperator T := by
  have hid : IsCompactOperator (id : F → F) :=
    (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℂ) (E := F)).mpr
      (by infer_instance)
  simpa only [Function.id_comp] using hid.comp_clm T

/-- An operator factoring through a finite-dimensional space is compact. -/
theorem isCompactOperator_of_factors_through_finiteDimensional
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [CompleteSpace G] [FiniteDimensional ℂ G]
    (A : E →L[ℂ] G) (B : G →L[ℂ] F) :
    IsCompactOperator (B.comp A) :=
  (isCompactOperator_of_finiteDimensional_codomain A).clm_comp B

section CoefficientProjection

variable {ι : Type*} [DecidableEq ι]

/-- Orthogonal projection onto a finite set of canonical coefficient atoms. -/
def finiteCoordinateProjection (F : Finset ι) :
    CoefficientSpace ι →L[ℂ] CoefficientSpace ι :=
  ∑ i ∈ F, InnerProductSpace.rankOne ℂ (coefficientAtom i) (coefficientAtom i)

@[simp]
theorem finiteCoordinateProjection_coefficientAtom (F : Finset ι) (j : ι) :
    finiteCoordinateProjection F (coefficientAtom j) =
      if j ∈ F then coefficientAtom j else 0 := by
  simp only [finiteCoordinateProjection, _root_.sum_apply,
    InnerProductSpace.rankOne_apply]
  change (∑ i ∈ F, inner ℂ (coefficientAtom i) (coefficientAtom j) •
    coefficientAtom i) = _
  simp_rw [show ∀ i, inner ℂ (coefficientAtom i) (coefficientAtom j) =
      if i = j then 1 else 0 from fun i =>
    orthonormal_iff_ite.mp (coefficientHilbertBasis ι).orthonormal i j]
  by_cases hj : j ∈ F
  · simp [hj]
  · simp [hj]

omit [DecidableEq ι] in
theorem finiteCoordinateProjection_isSelfAdjoint (F : Finset ι) :
    IsSelfAdjoint (finiteCoordinateProjection F) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  simp [finiteCoordinateProjection]

/-- Finite coordinate projections have finite rank and hence are compact. -/
theorem finiteCoordinateProjection_isCompact (F : Finset ι) :
    IsCompactOperator (finiteCoordinateProjection F) := by
  induction F using Finset.induction_on with
  | empty => simp [finiteCoordinateProjection, isCompactOperator_zero]
  | @insert i F hi ih =>
      have hrank : IsCompactOperator
          (InnerProductSpace.rankOne ℂ
            (coefficientAtom i) (coefficientAtom i)) := by
        rw [InnerProductSpace.rankOne_def']
        exact isCompactOperator_of_factors_through_finiteDimensional _ _
      simpa [finiteCoordinateProjection, Finset.sum_insert, hi] using
        hrank.add ih

theorem inner_finiteCoordinateProjection (F : Finset ι)
    (i : ι) (x : CoefficientSpace ι) :
    inner ℂ (coefficientAtom i) (finiteCoordinateProjection F x) =
      if i ∈ F then inner ℂ (coefficientAtom i) x else 0 := by
  calc
    inner ℂ (coefficientAtom i) (finiteCoordinateProjection F x) =
        inner ℂ (finiteCoordinateProjection F (coefficientAtom i)) x :=
      ((finiteCoordinateProjection_isSelfAdjoint F).isSymmetric
        (coefficientAtom i) x).symm
    _ = if i ∈ F then inner ℂ (coefficientAtom i) x else 0 := by
      rw [finiteCoordinateProjection_coefficientAtom]
      split <;> simp_all

/-- A finite coordinate projection has algebraically finite range. -/
theorem finiteCoordinateProjection_hasFiniteRange (F : Finset ι) :
    (finiteCoordinateProjection F).toLinearMap.HasFiniteRange := by
  induction F using Finset.induction_on with
  | empty => simp [finiteCoordinateProjection]
  | @insert i F hi ih =>
      have hrank :
          (InnerProductSpace.rankOne ℂ (coefficientAtom i)
            (coefficientAtom i)).toLinearMap.HasFiniteRange := by
        rw [InnerProductSpace.rankOne_def',
          ContinuousLinearMap.toLinearMap_comp]
        exact LinearMap.HasFiniteRange.comp_left
          (LinearMap.HasFiniteRange.of_isNoetherian_rng)
          (ContinuousLinearMap.toSpanSingleton ℂ
            (coefficientAtom i)).toLinearMap
      rw [finiteCoordinateProjection, Finset.sum_insert hi,
        ContinuousLinearMap.toLinearMap_add]
      exact hrank.add ih

/-- The subspace obtained by deleting finitely many coordinates has finite
codimension. -/
theorem finiteCoordinateProjection_ker_coFG (F : Finset ι) :
    (finiteCoordinateProjection F).toLinearMap.ker.CoFG :=
  (finiteCoordinateProjection_hasFiniteRange F).cofg_ker

end CoefficientProjection

end

end MeyerGeneralProblem
