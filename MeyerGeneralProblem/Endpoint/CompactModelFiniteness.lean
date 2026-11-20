module

public import MeyerGeneralProblem.Endpoint.WhitenedReducedCross
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Banach

@[expose] public section

/-!
# Finite intersections from compact contraction models

An isometric map cannot differ compactly from a strict contraction on an
infinite-dimensional complete space. Applied to the norm-preserving part of
a genuine whitened cross, this gives intersection finiteness independently
of the reduced endpoint gap.
-/

namespace MeyerGeneralProblem

noncomputable section

variable {E F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A compact operator bounded below has finite-dimensional complete domain. -/
theorem finiteDimensional_of_compact_boundedBelow
    (K : E →L[ℂ] F) (hK : IsCompactOperator K)
    {c : ℝ} (hc : 0 < c) (hbound : ∀ x, c * ‖x‖ ≤ ‖K x‖) :
    FiniteDimensional ℂ E := by
  have hanti : AntilipschitzWith ⟨c⁻¹, inv_nonneg.mpr hc.le⟩ K := by
    apply K.antilipschitz_of_bound
    intro x
    change ‖x‖ ≤ c⁻¹ * ‖K x‖
    rw [mul_comm c⁻¹, ← div_eq_mul_inv]
    exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hbound x)
  have hclosed : IsClosed (Set.range K) :=
    (hanti.isClosedEmbedding K.uniformContinuous).isClosed_range
  let e := K.equivRange hanti.injective hclosed
  have hKr : IsCompactOperator (fun x : E => (e x : K.range)) := by
    exact hK.codRestrict (fun x => K.mem_range_self x) hclosed
  have hid := hKr.clm_comp e.symm.toContinuousLinearMap
  have hid' : IsCompactOperator (id : E → E) := by
    have heq : e.symm.toContinuousLinearMap ∘ (fun x : E => (e x : K.range)) =
        (id : E → E) := by
      funext x
      exact e.symm_apply_apply x
    rw [heq] at hid
    exact hid
  exact FiniteDimensional.of_isCompactOperator_id hid'

/-- Norm preservation together with a compact strict-contraction model forces
finite dimension. -/
theorem finiteDimensional_of_isometric_compact_contraction_model
    (T C : E →L[ℂ] F) (hT : ∀ x, ‖T x‖ = ‖x‖)
    (hcompact : IsCompactOperator (T - C)) (hC : ‖C‖ < 1) :
    FiniteDimensional ℂ E := by
  apply finiteDimensional_of_compact_boundedBelow (T - C) hcompact
    (sub_pos.mpr hC)
  intro x
  have hrev := norm_sub_le (T x - C x) (-C x)
  have hnorm := C.le_opNorm x
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at hrev
  rw [hT x] at hrev
  change (1 - ‖C‖) * ‖x‖ ≤ ‖T x - C x‖
  nlinarith

/-- A compact strict-contraction model for a genuine globally whitened cross
forces the physical intersection itself to be finite-dimensional. -/
theorem coefficientAtomicSupport_inf_finiteDimensional_of_compact_model
    {ι : Type*} [DecidableEq ι]
    (S T : CoefficientSpace ι →L[ℂ] H)
    (hS : IsStrictlyPositive (coefficientGram S))
    (hT : IsStrictlyPositive (coefficientGram T))
    (C : CoefficientSpace ι →L[ℂ] CoefficientSpace ι)
    (hcompact : IsCompactOperator (whitenedCoefficientCross S T - C))
    (hC : ‖C‖ < 1) :
    FiniteDimensional ℂ
      ↥((coefficientAtomicSupport S).toSubmodule ⊓
        (coefficientAtomicSupport T).toSubmodule) := by
  let X := coefficientAtomicSupport S
  let Y := coefficientAtomicSupport T
  let V := X.toSubmodule ⊓ Y.toSubmodule
  have hV : IsClosed (V : Set H) := X.isClosed.inter Y.isClosed
  let : CompleteSpace V := hV.completeSpace_coe
  let e := whitenedSynthesisEquivAtomicSupport T hT
  let I : V →ₗᵢ[ℂ] CoefficientSpace ι :=
    { toLinearMap := e.symm.toLinearMap.comp (Submodule.inclusion inf_le_right)
      norm_map' := fun x => by
        change ‖e.symm ⟨(x : H), x.property.2⟩‖ = ‖x‖
        rw [e.symm.norm_map]
        rfl }
  let R := I.toContinuousLinearMap
  let U := (whitenedCoefficientCross S T).comp R
  let C₀ := C.comp R
  have hU : ∀ x : V, ‖U x‖ = ‖x‖ := by
    intro x
    have he : ((e (I x) : Y.toSubmodule) : H) = (x : H) := by
      change ((e (e.symm ⟨(x : H), x.property.2⟩) : Y.toSubmodule) : H) = _
      rw [e.apply_symm_apply]
    have hp := whitenedCoefficientCross_eq_projection S T hS hT (I x)
    change whitenedSynthesisEquivAtomicSupport S hS
      (whitenedCoefficientCross S T (I x)) = X.orthogonalProjectionOnto _ at hp
    rw [he] at hp
    calc
      ‖U x‖ = ‖whitenedSynthesisEquivAtomicSupport S hS (U x)‖ :=
        ((whitenedSynthesisEquivAtomicSupport S hS).norm_map _).symm
      _ = ‖X.orthogonalProjectionOnto (x : H)‖ := by exact congrArg norm hp
      _ = ‖(x : H)‖ := X.toSubmodule.norm_orthogonalProjectionOnto_apply x.property.1
      _ = ‖x‖ := rfl
  have hcompact' : IsCompactOperator (U - C₀) := by
    have heq : U - C₀ = (whitenedCoefficientCross S T - C).comp R := by
      ext x
      rfl
    rw [heq]
    exact hcompact.comp_clm R
  have hC₀ : ‖C₀‖ < 1 := by
    have hR : ‖R‖ ≤ 1 := I.norm_toContinuousLinearMap_le
    calc
      ‖C₀‖ ≤ ‖C‖ * ‖R‖ := ContinuousLinearMap.opNorm_comp_le C R
      _ ≤ ‖C‖ * 1 := mul_le_mul_of_nonneg_left hR (norm_nonneg C)
      _ < 1 := by simpa only [mul_one] using hC
  exact finiteDimensional_of_isometric_compact_contraction_model U C₀ hU hcompact' hC₀

end

end MeyerGeneralProblem
