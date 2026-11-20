module

public import MeyerGeneralProblem.Endpoint.CarrierCoefficientModel
public import MeyerGeneralProblem.Gram.CarrierUniversalCompactness
public import MeyerGeneralProblem.Gram.CompactPositivePerturbation
public import MeyerGeneralProblem.Cross.RemainderOperator

@[expose] public section

/-!
# Full carrier Gram and cross models

The analytic Gram and cross estimates are naturally proved after deleting a
finite central set.  This module restores those coordinates.  The tail Gram
is supplemented by its positive scalar floor on the finite central block;
the leading cross is extended by zero.  Both changes are finite-rank, so the
full genuine models retain the required compact differences.
-/

namespace MeyerGeneralProblem

noncomputable section

namespace CarrierUniversalTailData

variable {Λ : TwoSidedCarrier} (D : CarrierUniversalTailData Λ)

/-- Universal Gram tail model extended to all carrier coefficients, with the
same positive floor placed on the deleted finite central block. -/
def fullGramModel (m : ℕ) (hm : 1 ≤ m) :
    CoefficientSpace ℤ →L[ℂ] CoefficientSpace ℤ :=
  extendTailOperator D.F (D.gramOperator m hm) +
    universalGramLowerConstant m D.a D.d •
      finiteCoordinateProjection D.F

/-- The full Gram model retains the exact universal scalar floor. -/
theorem fullGramModel_lowerBound (m : ℕ) (hm : 1 ≤ m) :
    universalGramLowerConstant m D.a D.d •
        (1 : CoefficientSpace ℤ →L[ℂ] CoefficientSpace ℤ) ≤
      D.fullGramModel m hm := by
  let A := universalGramLowerConstant m D.a D.d
  let H := D.gramOperator m hm
  let E : CoefficientSpace {j : ℤ // j ∉ D.F} →L[ℂ]
      CoefficientSpace ℤ := tailCoefficientEmbedding D.F
  let P := finiteCoordinateProjection D.F
  have htail : A •
      (1 : CoefficientSpace {j : ℤ // j ∉ D.F} →L[ℂ]
        CoefficientSpace {j : ℤ // j ∉ D.F}) ≤ H := by
    simpa only [A, H] using D.gramOperator_lowerBound m hm
  have htailpos : (H - A •
      (1 : CoefficientSpace {j : ℤ // j ∉ D.F} →L[ℂ]
        CoefficientSpace {j : ℤ // j ∉ D.F})).IsPositive := by
    exact (ContinuousLinearMap.nonneg_iff_isPositive).mp
      (sub_nonneg.mpr htail)
  have hconj : (E ∘L (H - A •
      (1 : CoefficientSpace {j : ℤ // j ∉ D.F} →L[ℂ]
        CoefficientSpace {j : ℤ // j ∉ D.F})) ∘L E.adjoint).IsPositive :=
    htailpos.conj_adjoint E
  have hproj : E ∘L E.adjoint = 1 - P := by
    simpa only [E, P] using tailCoefficientEmbedding_comp_adjoint D.F
  have heq : D.fullGramModel m hm - A •
        (1 : CoefficientSpace ℤ →L[ℂ] CoefficientSpace ℤ) =
      E ∘L (H - A •
        (1 : CoefficientSpace {j : ℤ // j ∉ D.F} →L[ℂ]
          CoefficientSpace {j : ℤ // j ∉ D.F})) ∘L E.adjoint := by
    apply ContinuousLinearMap.ext
    intro x
    have hprojx := congrArg
      (fun Q : CoefficientSpace ℤ →L[ℂ] CoefficientSpace ℤ ↦ Q x) hproj
    simp only [ContinuousLinearMap.comp_apply, sub_apply, one_apply_eq_self]
      at hprojx
    simp only [fullGramModel, extendTailOperator, A, H, E,
      ContinuousLinearMap.comp_apply, add_apply, sub_apply, smul_apply,
      one_apply_eq_self, map_sub]
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
    rw [hprojx]
    module
  apply sub_nonneg.mp
  rw [heq]
  exact (ContinuousLinearMap.nonneg_iff_isPositive).mpr hconj

/-- The chosen scalar floor is strictly positive. -/
theorem fullGramModel_strictlyPositive (m : ℕ) (hm : 1 ≤ m) :
    IsStrictlyPositive (D.fullGramModel m hm) := by
  let _ : Nontrivial (CoefficientSpace ℤ) :=
    nontrivial_of_ne (coefficientAtom (0 : ℤ)) 0 (by
      apply norm_ne_zero_iff.mp
      rw [coefficientAtom_norm]
      norm_num)
  exact strictlyPositive_of_positive_scalar_floor
    (D.fullGramModel m hm)
    (universalGramLowerConstant_pos hm D.ha D.had)
    (D.fullGramModel_lowerBound m hm)

/-- The genuine carrier tail Gram is the two-sided compression of the full
genuine coefficient Gram. -/
theorem carrierGramOperator_eq_tailCompression
    (m : ℕ) (hm : 1 ≤ m)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    D.carrierGramOperator m hm B =
      (tailCoefficientEmbedding D.F).adjoint ∘L
        carrierCoefficientGram m hm Λ B ∘L
          tailCoefficientEmbedding D.F := by
  rw [carrierGramOperator, carrierCoefficientGram, coefficientGram,
    coefficientGram, ← D.carrierPointMassSynthesis_comp_tailCoefficientEmbedding
      m hm B,
    ContinuousLinearMap.adjoint_comp]
  simp only [ContinuousLinearMap.comp_assoc]

/-- The full genuine carrier Gram differs compactly from the restored full
universal model. -/
theorem carrierCoefficientGram_sub_fullGramModel_isCompact
    (m : ℕ) (hm : 1 ≤ m)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    IsCompactOperator
      (carrierCoefficientGram m hm Λ B - D.fullGramModel m hm) := by
  let G := carrierCoefficientGram m hm Λ B
  let H := D.carrierGramOperator m hm B
  let H₀ := D.gramOperator m hm
  let A := universalGramLowerConstant m D.a D.d
  let E : CoefficientSpace {j : ℤ // j ∉ D.F} →L[ℂ]
      CoefficientSpace ℤ := tailCoefficientEmbedding D.F
  let P := finiteCoordinateProjection D.F
  let Q : CoefficientSpace ℤ →L[ℂ] CoefficientSpace ℤ := E ∘L E.adjoint
  let C := finiteCentralTruncation G D.F
  have hQ : Q = cofiniteCoordinateProjection D.F := by
    simpa only [Q, E, cofiniteCoordinateProjection] using
      tailCoefficientEmbedding_comp_adjoint D.F
  have hH : H = E.adjoint ∘L G ∘L E := by
    simpa only [H, G, E] using
      D.carrierGramOperator_eq_tailCompression m hm B
  have hExtH : extendTailOperator D.F H = Q ∘L G ∘L Q := by
    rw [hH]
    apply ContinuousLinearMap.ext
    intro x
    simp only [extendTailOperator, Q, E, ContinuousLinearMap.comp_apply]
  have hcentral : C + Q ∘L G ∘L Q = G := by
    have hdecomp : finiteCentralTruncation G D.F +
        cofiniteCoordinateCompression G D.F = G := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [finiteCentralTruncation, finiteCoordinateCompression,
        cofiniteCoordinateCompression, cofiniteCoordinateProjection,
        ContinuousLinearMap.comp_apply, add_apply, sub_apply,
        one_apply_eq_self, map_sub]
      abel
    simpa only [C, hQ, cofiniteCoordinateCompression] using hdecomp
  have hfull : G - D.fullGramModel m hm =
      C + extendTailOperator D.F (H - H₀) - A • P := by
    rw [show D.fullGramModel m hm =
        extendTailOperator D.F H₀ + A • P by
      rfl]
    rw [show extendTailOperator D.F (H - H₀) =
        extendTailOperator D.F H - extendTailOperator D.F H₀ by
      apply ContinuousLinearMap.ext
      intro x
      simp [extendTailOperator]]
    rw [hExtH]
    calc
      G - (extendTailOperator D.F H₀ + A • P) =
          (C + Q ∘L G ∘L Q) -
            (extendTailOperator D.F H₀ + A • P) :=
        congrArg
          (fun X : CoefficientSpace ℤ →L[ℂ] CoefficientSpace ℤ ↦
            X - (extendTailOperator D.F H₀ + A • P)) hcentral.symm
      _ = C + (Q ∘L G ∘L Q - extendTailOperator D.F H₀) - A • P := by
        abel
  have hC : IsCompactOperator C := finiteCentralTruncation_isCompact G D.F
  have htail : IsCompactOperator (H - H₀) := by
    simpa only [H, H₀, CarrierUniversalTailData.carrierGramDifference] using
      D.carrierGramDifference_isCompact m hm B
  have hExt : IsCompactOperator (extendTailOperator D.F (H - H₀)) :=
    extendTailOperator_isCompact D.F (H - H₀) htail
  have hP : IsCompactOperator (A • P) :=
    (finiteCoordinateProjection_isCompact D.F).smul A
  rw [hfull]
  exact (hC.add hExt).sub hP

include D in
/-- One carrier constant, chosen before the Hermite order, controls full
leading cross models on the same finite complement as the universal Gram
model.  Both the genuine raw-cross error and its adjoint are compact. -/
theorem exists_uniform_fullLeadingCrossModel
    (B : ∀ (m : ℕ) (hm : 1 ≤ m), CarrierHermiteBesselAnalysis m hm Λ) :
    ∃ CΛ : NNReal, ∀ (m : ℕ) (hm : 1 ≤ m),
      ∃ B₀ : CoefficientSpace ℤ →L[ℂ] CoefficientSpace ℤ,
        ‖B₀‖ ≤ (CΛ : ℝ) * gramNormalization m * (m + 1 : ℝ) *
            (4 : ℝ)⁻¹ ^ m ∧
        IsCompactOperator
          (carrierRawCoefficientCross m hm Λ (B m hm) - B₀) ∧
        IsCompactOperator
          ((carrierRawCoefficientCross m hm Λ (B m hm)).adjoint -
            B₀.adjoint) := by
  have hsepOne : ∀ i j, i ∉ D.F → j ∉ D.F → i ≠ j →
      1 ≤ |signedSquare (Λ i) - signedSquare (Λ j)| := by
    intro i j hi hj hij
    exact D.hd.le.trans (D.separated i j hi hj hij)
  obtain ⟨CΛ, hleading⟩ :=
    MeyerGeneralProblem.exists_uniform_boundedLeadingTailOperator
      (Λ := Λ) (F := D.F) D.outside hsepOne
  refine ⟨CΛ, ?_⟩
  intro m hm
  obtain ⟨T, hTentry, hTnorm⟩ := hleading m hm
  let B₀ : CoefficientSpace ℤ →L[ℂ] CoefficientSpace ℤ :=
    extendTailOperator D.F T
  have hfull :=
    carrierRawCrossOperator_sub_extendTailOperator_isCompact_and_adjoint
      m hm Λ (B m hm) D.F T hTentry D.hd
        D.outside D.separated
  refine ⟨B₀, (norm_extendTailOperator_le D.F T).trans hTnorm, ?_, ?_⟩
  · simpa only [B₀, carrierRawCoefficientCross, carrierRawCrossOperator]
      using hfull.1
  · simpa only [B₀, carrierRawCoefficientCross, carrierRawCrossOperator]
      using hfull.2

set_option linter.style.haveILetI false in
/-- A strict full whitened model controls the exact rectangular reduced
carrier cross.  Restricting both genuine and model operators to the transported
reduced domain preserves the compact error and cannot increase the model
norm. -/
theorem carrierWhitenedReducedCross_norm_lt_one_of_fullModels
    (m : ℕ) (hm : 1 ≤ m)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (hG : IsStrictlyPositive (carrierCoefficientGram m hm Λ B))
    (G₀ B₀ : CoefficientSpace ℤ →L[ℂ] CoefficientSpace ℤ)
    (hG₀ : IsStrictlyPositive G₀)
    (hGram : IsCompactOperator
      (carrierCoefficientGram m hm Λ B - G₀))
    (hCross : IsCompactOperator
      (carrierRawCoefficientCross m hm Λ B - B₀))
    (hCrossAdjoint : IsCompactOperator
      ((carrierRawCoefficientCross m hm Λ B).adjoint - B₀.adjoint))
    {A β : ℝ} (hA : 0 < A)
    (hfloor : A • (1 : CoefficientSpace ℤ →L[ℂ]
      CoefficientSpace ℤ) ≤ G₀)
    (hB₀ : ‖B₀‖ ≤ β) (hgap : β / A < 1) :
    ‖carrierWhitenedReducedCross m hm Λ B hG‖ < 1 := by
  let _ : Nontrivial (CoefficientSpace ℤ) :=
    nontrivial_of_ne (coefficientAtom (0 : ℤ)) 0 (by
      apply norm_ne_zero_iff.mp
      rw [coefficientAtom_norm]
      norm_num)
  let K := carrierCoefficientReducedDomain m hm Λ B hG
  letI : K.HasOrthogonalProjection := by
    dsimp only [K, carrierCoefficientReducedDomain]
    exact coefficientReducedDomain_hasOrthogonalProjection
      (carrierInverseFourierPointMassSynthesis m hm Λ B)
      (carrierPointMassSynthesis m hm Λ B)
      (carrierInverseFourierCoefficientGram_strictlyPositive m hm Λ B hG)
      (carrierCoefficientGram_strictlyPositive_unfold m hm Λ B hG)
  letI : CompleteSpace K := by
    have hclosed : IsClosed (K : Set (CoefficientSpace ℤ)) := by
      rw [← K.range_starProjection]
      exact ContinuousLinearMap.IsIdempotentElem.isClosed_range
        K.isIdempotentElem_starProjection
    exact hclosed.completeSpace_coe
  let R : K →L[ℂ] CoefficientSpace ℤ := K.subtypeL
  let W := gramWhitener (carrierCoefficientGram m hm Λ B)
  let W₀ := gramWhitener G₀
  let Ξ := carrierRawCoefficientCross m hm Λ B
  let T := carrierWhitenedReducedCross m hm Λ B hG
  let Cglobal : CoefficientSpace ℤ →L[ℂ] CoefficientSpace ℤ :=
    W₀ * B₀ * W₀
  let C : K →L[ℂ] CoefficientSpace ℤ := Cglobal.comp R
  rcases subsingleton_or_nontrivial K with hK | hK
  · have hTzero : T = 0 := by
      apply ContinuousLinearMap.ext
      intro x
      rw [show x = 0 from Subsingleton.elim x 0]
      simp
    change ‖T‖ < 1
    exact hTzero ▸ (show ‖(0 : K →L[ℂ] CoefficientSpace ℤ)‖ < 1 by
      norm_num)
  · let hKInst : Nontrivial K := hK
    have hActual : T = (W * Ξ * W).comp R := by
      apply ContinuousLinearMap.ext
      intro x
      rw [show T x = carrierWhitenedCoefficientCross m hm Λ B
          (x : CoefficientSpace ℤ) by
        exact carrierWhitenedReducedCross_apply m hm Λ B hG x]
      rw [carrierWhitenedCoefficientCross_eq]
      rfl
    have hW : IsCompactOperator (W - W₀) := by
      exact compact_gramWhitener_sub
        (carrierCoefficientGram m hm Λ B) G₀ hG hG₀ hGram
    have hWAdjoint : IsCompactOperator (W.adjoint - W₀.adjoint) := by
      exact compact_gramWhitener_adjoint_sub
        (carrierCoefficientGram m hm Λ B) G₀ hG hG₀ hGram
    have hglobal : IsCompactOperator
        (W * Ξ * W - Cglobal) := by
      exact compact_whitenedCross_sub_model W W₀ Ξ B₀ hW hCross
    have hglobalAdjoint : IsCompactOperator
        ((W * Ξ * W).adjoint - Cglobal.adjoint) := by
      exact compact_adjoint_whitenedCross_sub_model
        W W₀ Ξ B₀ hWAdjoint hCrossAdjoint
    have hrestricted : IsCompactOperator (T - C) := by
      have heq : T - C = (W * Ξ * W - Cglobal).comp R := by
        rw [hActual]
        apply ContinuousLinearMap.ext
        intro x
        simp only [C, ContinuousLinearMap.comp_apply, sub_apply]
      rw [heq]
      exact hglobal.comp_clm R
    have hrestrictedAdjoint : IsCompactOperator (T.adjoint - C.adjoint) := by
      have heq : T.adjoint - C.adjoint =
          R.adjoint.comp ((W * Ξ * W).adjoint - Cglobal.adjoint) := by
        rw [hActual]
        simp only [C, ContinuousLinearMap.adjoint_comp]
        apply ContinuousLinearMap.ext
        intro x
        simp only [ContinuousLinearMap.comp_apply, sub_apply, map_sub]
      rw [heq]
      exact hglobalAdjoint.clm_comp R.adjoint
    have hmodelGlobal : ‖Cglobal‖ < 1 := by
      exact norm_whitenedModel_lt_one_of_gram_le W₀ B₀ hA
        (gramWhitener_gram_le_inv_floor G₀ hA hfloor) hB₀ hgap
    have hmodel : ‖C‖ < 1 := by
      calc
        ‖C‖ ≤ ‖Cglobal‖ * ‖R‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖Cglobal‖ * 1 := mul_le_mul_of_nonneg_left
          (Submodule.norm_subtypeL_le K) (norm_nonneg Cglobal)
        _ < 1 := by simpa using hmodelGlobal
    apply operator_norm_lt_one_of_compact_model T C
    · simpa only [T, ← carrierSquareWhitenedReducedCross_norm_eq
          m hm Λ B hG] using
        carrierSquareWhitenedReducedCross_norm_le_one m hm Λ B hG
    · intro x hx
      have hsquare := carrierSquareWhitenedReducedCross_apply_norm_lt_one
        m hm Λ B hG (x : CoefficientSpace ℤ) (by simpa using hx)
      simpa only [T, carrierSquareWhitenedReducedCross_apply_mem]
        using hsquare
    · exact hrestricted
    · exact hrestrictedAdjoint
    · exact hmodel

end CarrierUniversalTailData

end

end MeyerGeneralProblem
