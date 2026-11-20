module

public import MeyerGeneralProblem.Hilbert.FiniteCoordinateProjection
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

@[expose] public section

/-!
# Infinite deficiency from injectivity after finite coordinate deletion

The algebraic endpoint argument of the retained separated-supercritical
proof, Lemma 7.1, projects finite coordinate vectors to the orthogonal
complement of the sampling range. Finite-deletion injectivity makes these
projections linearly independent. Closed range is used explicitly; no
infinite-dimensional cokernel is assumed.

This module does not prove the analytic KNS finite-deletion sampling bound.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- The actual bounded operator deleting a finite collection of coordinates. -/
def finiteCoordinateDeletion (F : Finset ι) :
    CoefficientSpace ι →L[ℂ] CoefficientSpace ι :=
  ContinuousLinearMap.id ℂ _ - finiteCoordinateProjection F

/-- Finite deletion kills precisely the selected canonical atoms. -/
@[simp]
theorem finiteCoordinateDeletion_coefficientAtom (F : Finset ι) (j : ι) :
    finiteCoordinateDeletion F (coefficientAtom j) =
      if j ∈ F then 0 else coefficientAtom j := by
  simp only [finiteCoordinateDeletion, _root_.sub_apply,
    ContinuousLinearMap.id_apply, finiteCoordinateProjection_coefficientAtom]
  split <;> simp

omit [DecidableEq ι] in
/-- Deleting the empty set of coordinates changes no vector. -/
@[simp]
theorem finiteCoordinateDeletion_empty :
    finiteCoordinateDeletion (∅ : Finset ι) = ContinuousLinearMap.id ℂ _ := by
  simp [finiteCoordinateDeletion, finiteCoordinateProjection]

/-- The range of a finite coordinate projection is exactly the span of
the selected canonical atoms, not merely an abstract finite-rank space. -/
theorem finiteCoordinateProjection_range_eq_span (F : Finset ι) :
    (finiteCoordinateProjection F).range =
      Submodule.span ℂ (coefficientAtom '' (F : Set ι)) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    change finiteCoordinateProjection F x ∈ _
    simp only [finiteCoordinateProjection, _root_.sum_apply, InnerProductSpace.rankOne_apply]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨i, hi, rfl⟩
  · apply Submodule.span_le.mpr
    rintro y ⟨i, hi, rfl⟩
    change i ∈ F at hi
    exact ⟨coefficientAtom i, by simp [hi]⟩

/-- Every vector in the finite coordinate span is fixed by its projection. -/
theorem finiteCoordinateProjection_eq_self_of_mem_span (F : Finset ι)
    {x : CoefficientSpace ι} (hx : x ∈ Submodule.span ℂ (coefficientAtom '' (F : Set ι))) :
    finiteCoordinateProjection F x = x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨i, hi, rfl⟩
      change i ∈ F at hi
      simp [hi]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx => simp only [map_smul, hx]

/-- A vector is killed by finite deletion exactly when it belongs to the
span of the deleted canonical atoms. -/
theorem finiteCoordinateDeletion_eq_zero_iff (F : Finset ι) (x : CoefficientSpace ι) :
    finiteCoordinateDeletion F x = 0 ↔
      x ∈ Submodule.span ℂ (coefficientAtom '' (F : Set ι)) := by
  change x - finiteCoordinateProjection F x = 0 ↔ _
  rw [sub_eq_zero]
  constructor
  · intro hx
    rw [← finiteCoordinateProjection_range_eq_span, hx]
    exact ⟨x, rfl⟩
  · exact fun hx => (finiteCoordinateProjection_eq_self_of_mem_span F hx).symm

section Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Injectivity after every finite deletion is exactly injectivity of the
original operator together with trivial intersection of its range and every
finite coordinate span. The separate injectivity condition is essential. -/
theorem forall_finiteCoordinateDeletion_injective_iff
    (T : E →L[ℂ] CoefficientSpace ι) :
    (∀ F : Finset ι, Function.Injective ((finiteCoordinateDeletion F).comp T)) ↔
      Function.Injective T ∧ ∀ F : Finset ι,
        Disjoint T.range (Submodule.span ℂ (coefficientAtom '' (F : Set ι))) := by
  constructor
  · intro h
    refine ⟨?_, fun F => Submodule.disjoint_def.mpr ?_⟩
    · simpa using h ∅
    · intro y hy hspan
      rcases hy with ⟨x, rfl⟩
      have hx : x = 0 := h F (by
        simpa only [ContinuousLinearMap.comp_apply, map_zero] using
          (finiteCoordinateDeletion_eq_zero_iff F (T x)).mpr hspan)
      simp [hx]
  · rintro ⟨hT, hdisjoint⟩ F
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply hT
    rw [map_zero]
    exact Submodule.disjoint_def.mp (hdisjoint F) (T x) ⟨x, rfl⟩
      ((finiteCoordinateDeletion_eq_zero_iff F (T x)).mp hx)

/-- Under finite-deletion injectivity, the projections of all canonical
atoms to the orthogonal complement of the closed range are genuinely
linearly independent. This proves deficiency rather than assuming it. -/
theorem linearIndependent_projected_atoms_of_finiteDeletion_injective
    (T : E →L[ℂ] CoefficientSpace ι) (hclosed : IsClosed (T.range : Set (CoefficientSpace ι)))
    (hdelete : ∀ F : Finset ι, Function.Injective ((finiteCoordinateDeletion F).comp T)) :
    LinearIndependent ℂ (fun i : ι => T.rangeᗮ.orthogonalProjectionOnto (coefficientAtom i)) := by
  let : IsClosed (T.range : Set (CoefficientSpace ι)) := hclosed
  let : CompleteSpace T.range := hclosed.completeSpace_coe
  have hdisjoint := ((forall_finiteCoordinateDeletion_injective_iff T).mp hdelete).2
  apply linearIndependent_iff'.mpr
  intro F g hsum i hi
  have hproj : T.rangeᗮ.orthogonalProjectionOnto (∑ j ∈ F, g j • coefficientAtom j) = 0 := by
    simpa only [map_sum, map_smul] using hsum
  have hrange : (∑ j ∈ F, g j • coefficientAtom j) ∈ T.range := by
    have hmem := Submodule.orthogonalProjectionOnto_eq_zero_iff.mp hproj
    rwa [Submodule.orthogonal_orthogonal] at hmem
  have hspan : (∑ j ∈ F, g j • coefficientAtom j) ∈
      Submodule.span ℂ (coefficientAtom '' (F : Set ι)) := by
    apply Submodule.sum_mem
    intro j hj
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  have hzero := Submodule.disjoint_def.mp (hdisjoint F) _ hrange hspan
  exact linearIndependent_iff'.mp (coefficientHilbertBasis ι).orthonormal.linearIndependent F g hzero i hi

/-- A closed-range operator on an infinite coordinate set whose every
finite deletion is injective has infinite-dimensional orthogonal deficiency. -/
theorem not_finiteDimensional_orthogonal_range_of_finiteDeletion_injective
    [Infinite ι] (T : E →L[ℂ] CoefficientSpace ι)
    (hclosed : IsClosed (T.range : Set (CoefficientSpace ι)))
    (hdelete : ∀ F : Finset ι, Function.Injective ((finiteCoordinateDeletion F).comp T)) :
    ¬ FiniteDimensional ℂ T.rangeᗮ := by
  intro hfinite
  let := hfinite
  have : Finite ι :=
    (linearIndependent_projected_atoms_of_finiteDeletion_injective T hclosed hdelete).finite
  exact Infinite.false (inferInstance : Infinite ι)

end Operator

/-- The exact Hilbert consequence of finite-deletion coercivity, in the
squared-norm form used by KNS. Constants may depend on the finite deletion;
no common positive bound over all deletions is needed. -/
theorem infiniteDeficiency_of_finiteDeletion_coercivity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [Infinite ι] (T : E →L[ℂ] CoefficientSpace ι)
    (hbound : ∀ F : Finset ι, ∃ c : ℝ, 0 < c ∧
      ∀ x : E, c * ‖x‖ ^ 2 ≤ ‖finiteCoordinateDeletion F (T x)‖ ^ 2) :
    Function.Injective T ∧ IsClosed (T.range : Set (CoefficientSpace ι)) ∧
      ¬ FiniteDimensional ℂ T.rangeᗮ := by
  have hdelete (F : Finset ι) : Function.Injective ((finiteCoordinateDeletion F).comp T) := by
    obtain ⟨c, hc, hF⟩ := hbound F
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have h := hF x
    change finiteCoordinateDeletion F (T x) = 0 at hx
    rw [hx, norm_zero, zero_pow (by omega : 2 ≠ 0)] at h
    have hs : ‖x‖ ^ 2 ≤ 0 := nonpos_of_mul_nonpos_left (by simpa only [mul_comm] using h) hc
    have hnorm : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
    exact norm_eq_zero.mp hnorm
  have hinj : Function.Injective T := by simpa using hdelete ∅
  obtain ⟨c, hc, hbase⟩ := hbound ∅
  simp only [finiteCoordinateDeletion_empty, ContinuousLinearMap.id_apply] at hbase
  have hsqrt : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hlower (x : E) : Real.sqrt c * ‖x‖ ≤ ‖T x‖ := by
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
    simpa only [mul_pow, Real.sq_sqrt hc.le] using hbase x
  have hanti : AntilipschitzWith ⟨(Real.sqrt c)⁻¹, by positivity⟩ T := by
    apply T.antilipschitz_of_bound
    intro x
    change ‖x‖ ≤ (Real.sqrt c)⁻¹ * ‖T x‖
    calc
      ‖x‖ = (Real.sqrt c)⁻¹ * (Real.sqrt c * ‖x‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ hsqrt.ne', one_mul]
      _ ≤ (Real.sqrt c)⁻¹ * ‖T x‖ :=
        mul_le_mul_of_nonneg_left (hlower x) (by positivity)
  have hclosed : IsClosed (T.range : Set (CoefficientSpace ι)) :=
    hanti.isClosed_range T.uniformContinuous
  exact ⟨hinj, hclosed,
    not_finiteDimensional_orthogonal_range_of_finiteDeletion_injective T hclosed hdelete⟩

end

end MeyerGeneralProblem
