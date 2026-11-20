module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.Perturbation.StrictByFinite
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

/-!
# Hilbert-space upper semi-Fredholm operators

Upper semi-Fredholmness means closed range and finite-dimensional kernel.
No finiteness of the cokernel is assumed.  A lower bound on a closed
finite-codimension subspace is an equivalent quantitative criterion.
-/

namespace MeyerGeneralProblem

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Closed range and finite-dimensional kernel, with no cokernel condition. -/
structure IsUpperSemiFredholm (T : E →L[ℂ] F) : Prop where
  isClosed_range : IsClosed (Set.range T)
  finite_ker : FiniteDimensional ℂ T.ker

omit [CompleteSpace F] in
/-- A positive lower bound on a closed finite-codimension subspace forces
upper semi-Fredholmness. -/
theorem isUpperSemiFredholm_of_finiteCodimension_lowerBound
    (T : E →L[ℂ] F) (M : ClosedSubmodule ℂ E)
    (hM : M.toSubmodule.CoFG) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x : M.toSubmodule, c * ‖x‖ ≤ ‖T (x : E)‖) :
    IsUpperSemiFredholm T := by
  let : M.toSubmodule.CoFG := hM
  let : CompleteSpace M.toSubmodule := M.isClosed'.completeSpace_coe
  let A := T.domRestrict M.toSubmodule
  have hanti : AntilipschitzWith ⟨c⁻¹, inv_nonneg.mpr hc.le⟩ A := by
    apply A.antilipschitz_of_bound
    intro x
    change ‖x‖ ≤ c⁻¹ * ‖T (x : E)‖
    calc
      ‖x‖ = c⁻¹ * (c * ‖x‖) := by rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      _ ≤ c⁻¹ * ‖T (x : E)‖ :=
        mul_le_mul_of_nonneg_left (hbound x) (inv_nonneg.mpr hc.le)
  have hclosedA := hanti.isClosed_range A.uniformContinuous
  have hclosed : IsClosed (Set.range T) := by
    change IsClosed (T.toLinearMap.range : Set F)
    apply LinearMap.isClosed_range_of_isClosed_map_of_finiteDimensional_quotient
      (s := M.toSubmodule)
    have heq : (M.toSubmodule.map T.toLinearMap : Set F) = Set.range A := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨x, x.property, rfl⟩
    rw [heq]
    exact hclosedA
  have hdisj : Disjoint T.ker M.toSubmodule := by
    apply Submodule.disjoint_def.mpr
    intro x hx hMx
    change T x = 0 at hx
    have hz : A ⟨x, hMx⟩ = A 0 := by
      change T x = T 0
      simpa only [map_zero] using hx
    exact congrArg Subtype.val (hanti.injective hz)
  exact ⟨hclosed, (T.ker.fg_iff_finiteDimensional).mp (hM.fg_of_disjoint hdisj)⟩

/-- An upper semi-Fredholm map is bounded below on the orthogonal complement
of its kernel.  This complement has finite codimension even if the cokernel
is infinite-dimensional. -/
theorem IsUpperSemiFredholm.exists_finiteCodimension_lowerBound
    {T : E →L[ℂ] F} (hT : IsUpperSemiFredholm T) :
    ∃ M : ClosedSubmodule ℂ E, M.toSubmodule.CoFG ∧
      ∃ c : ℝ, 0 < c ∧ ∀ x : M.toSubmodule, c * ‖x‖ ≤ ‖T (x : E)‖ := by
  let : FiniteDimensional ℂ T.ker := hT.finite_ker
  let M : ClosedSubmodule ℂ E := ⟨T.kerᗮ, T.ker.isClosed_orthogonal⟩
  have hM : M.toSubmodule.CoFG :=
    ((T.ker.fg_iff_finiteDimensional).mpr hT.finite_ker).cofg_of_isCompl
      T.ker.isCompl_orthogonal
  let A := T.domRestrict M.toSubmodule
  have hinj : Function.Injective A := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply (Submodule.disjoint_def.mp T.ker.isCompl_orthogonal.disjoint)
    · change T ((x : E) - (y : E)) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hxy
    · exact M.sub_mem x.property y.property
  have hrange : Set.range A = Set.range T := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro y ⟨x, rfl⟩
      refine ⟨⟨x - T.ker.starProjection x,
        T.ker.sub_starProjection_mem_orthogonal x⟩, ?_⟩
      change T (x - T.ker.starProjection x) = T x
      rw [map_sub]
      have hz : T (T.ker.starProjection x) = 0 :=
        T.ker.starProjection_apply_mem x
      rw [hz, sub_zero]
  obtain ⟨K, hK⟩ := A.antilipschitz_of_injective_of_isClosed_range
    hinj (hrange ▸ hT.isClosed_range)
  refine ⟨M, hM, ((K : ℝ) + 1)⁻¹, inv_pos.mpr (by positivity), ?_⟩
  intro x
  have hb := hK.le_mul_dist x 0
  simp only [dist_zero_right, map_zero] at hb
  have hk : 0 < (K : ℝ) + 1 := by positivity
  calc
    ((K : ℝ) + 1)⁻¹ * ‖x‖ ≤
        ((K : ℝ) + 1)⁻¹ * (((K : ℝ) + 1) * ‖A x‖) := by
      gcongr
      nlinarith [norm_nonneg (A x)]
    _ = ‖T (x : E)‖ := by
      rw [← mul_assoc, inv_mul_cancel₀ hk.ne', one_mul]
      rfl

/-- Exact finite-codimension lower-bound criterion. -/
theorem isUpperSemiFredholm_iff_finiteCodimension_lowerBound
    (T : E →L[ℂ] F) :
    IsUpperSemiFredholm T ↔
      ∃ M : ClosedSubmodule ℂ E, M.toSubmodule.CoFG ∧
        ∃ c : ℝ, 0 < c ∧ ∀ x : M.toSubmodule, c * ‖x‖ ≤ ‖T (x : E)‖ := by
  constructor
  · exact IsUpperSemiFredholm.exists_finiteCodimension_lowerBound
  · rintro ⟨M, hM, c, hc, hbound⟩
    exact isUpperSemiFredholm_of_finiteCodimension_lowerBound T M hM hc hbound

end

end MeyerGeneralProblem
