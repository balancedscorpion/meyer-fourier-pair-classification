module

public import MeyerGeneralProblem.Carrier.CoefficientTail
public import MeyerGeneralProblem.Carrier.HermiteCross
public import MeyerGeneralProblem.Gram.CoefficientModel
public import MeyerGeneralProblem.Cross.LeadingOperator
public import MeyerGeneralProblem.Cross.NormalizedRemainder
public import MeyerGeneralProblem.Cross.CompactRemainder
public import MeyerGeneralProblem.Sampling.SeparatedDecay

@[expose] public section

/-!
# Concrete carrier tail cross remainder

This module restricts the genuine raw physical/Fourier carrier cross operator
to a finite-codimensional coefficient tail and subtracts a bounded operator
whose canonical entries are the normalized spatial leading kernel.  The
resulting remainder therefore has exactly the corrected normalized-kernel
remainder as its canonical matrix.

The raw cross is deliberately assembled here from the lower-level carrier
synthesis maps.  In particular, the cross-analysis layer does not import the
endpoint coefficient model that later consumes this operator.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- On a noncentral signed-square-separated carrier tail, the squared
separable remainder weight is summable. -/
theorem summable_tail_signedSquare_rpow_neg_three_halves
    {Λ : TwoSidedCarrier} {F : Finset ℤ} {d : ℝ}
    (houtside : ∀ j, j ∉ F → 1 < (Λ j) ^ 2)
    (hd : 1 < d)
    (hsep : ∀ i j, i ∉ F → j ∉ F → i ≠ j →
      d ≤ |signedSquare (Λ i) - signedSquare (Λ j)|) :
    Summable (fun i : FineLogTailIndex F ↦
      |signedSquare (Λ i.1)| ^ (-(3 / 2 : ℝ))) := by
  apply summable_abs_rpow_of_separated_away
    (fun i : FineLogTailIndex F ↦ signedSquare (Λ i.1))
    hd (by norm_num : (1 : ℝ) < 3 / 2)
  · intro i j hij
    apply hsep i.1 j.1 i.property j.property
    intro hval
    exact hij (Subtype.ext hval)
  · intro i
    rw [abs_signedSquare, sq_abs]
    exact (houtside i.1 i.property).le

/-- Genuine raw physical/Fourier carrier cross, assembled below the endpoint
coefficient model from the two concrete synthesis maps. -/
def carrierRawCrossOperator
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    CoefficientSpace ℤ →L[ℂ] CoefficientSpace ℤ :=
  rawCoefficientCross
    (carrierPointMassSynthesis m hm Λ B)
    (carrierFourierPointMassSynthesis m hm Λ B)

/-- Restriction of the genuine raw carrier cross to the complement of a
finite coordinate set.  It is defined directly from the physical and
Fourier carrier synthesis maps, below the endpoint coefficient model. -/
def carrierTailRawCoefficientCross
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) (F : Finset ℤ) :
    CoefficientSpace (FineLogTailIndex F) →L[ℂ]
      CoefficientSpace (FineLogTailIndex F) :=
  (tailCoefficientEmbedding F).adjoint ∘L
    carrierRawCrossOperator m hm Λ B ∘L
        tailCoefficientEmbedding F

/-- Every canonical entry of the tail restriction is the genuine normalized
Hermite cross kernel. -/
theorem carrierTailRawCoefficientCross_entry
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) (F : Finset ℤ)
    (i j : FineLogTailIndex F) :
    inner ℂ (coefficientAtom i)
        (carrierTailRawCoefficientCross m hm Λ B F (coefficientAtom j)) =
      normalizedHermiteCrossKernel m hm (Λ i.1) (Λ j.1) := by
  rw [carrierTailRawCoefficientCross,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right,
    tailCoefficientEmbedding_coefficientAtom,
    tailCoefficientEmbedding_coefficientAtom,
    carrierRawCrossOperator, rawCoefficientCross,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right,
    carrierPointMassSynthesis_coefficientAtom,
    carrierFourierPointMassSynthesis_coefficientAtom]
  exact inner_carrierHermitePointMass_hermiteFourier_eq_crossKernel
    m hm Λ i.1 j.1

/-- Difference between the genuine raw tail cross and a chosen bounded
leading-tail operator. -/
def carrierTailCrossRemainder
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) (F : Finset ℤ)
    (T : CoefficientSpace (FineLogTailIndex F) →L[ℂ]
      CoefficientSpace (FineLogTailIndex F)) :
    CoefficientSpace (FineLogTailIndex F) →L[ℂ]
      CoefficientSpace (FineLogTailIndex F) :=
  carrierTailRawCoefficientCross m hm Λ B F - T

/-- If the chosen leading operator has the exact spatial-leading entries,
then the concrete tail remainder has exactly the corrected normalized-kernel
remainder entries. -/
theorem carrierTailCrossRemainder_entry
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) (F : Finset ℤ)
    (T : CoefficientSpace (FineLogTailIndex F) →L[ℂ]
      CoefficientSpace (FineLogTailIndex F))
    (hT : ∀ i j,
      inner ℂ (coefficientAtom i) (T (coefficientAtom j)) =
        normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1))
    (i j : FineLogTailIndex F) :
    inner ℂ (coefficientAtom i)
        (carrierTailCrossRemainder m hm Λ B F T (coefficientAtom j)) =
      normalizedHermiteCrossKernel m hm (Λ i.1) (Λ j.1) -
        normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1) := by
  rw [carrierTailCrossRemainder, sub_apply,
    inner_sub_right, carrierTailRawCoefficientCross_entry, hT]

/-- A two-sided cofinite compression masks exactly the rows and columns in
the selected finite central set and leaves every deep-tail remainder entry
unchanged. -/
theorem cofiniteCarrierTailCrossRemainder_entry
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) (F : Finset ℤ)
    (T : CoefficientSpace (FineLogTailIndex F) →L[ℂ]
      CoefficientSpace (FineLogTailIndex F))
    (hT : ∀ i j,
      inner ℂ (coefficientAtom i) (T (coefficientAtom j)) =
        normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1))
    (E : Finset (FineLogTailIndex F)) (i j : FineLogTailIndex F) :
    inner ℂ (coefficientAtom i)
        (cofiniteCoordinateCompression
          (carrierTailCrossRemainder m hm Λ B F T) E
          (coefficientAtom j)) =
      if i ∉ E ∧ j ∉ E then
        normalizedHermiteCrossKernel m hm (Λ i.1) (Λ j.1) -
          normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1)
      else 0 := by
  rw [cofiniteCoordinateCompression_entry]
  split
  · rw [carrierTailCrossRemainder_entry m hm Λ B F T hT]
  · rfl

/-- The finite set of tail coordinates whose physical locations have not yet
reached the normalized-kernel threshold for a fixed Hermite order. -/
def carrierTailNaturalScaleCentralSet
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ) :
    Finset (FineLogTailIndex F) :=
  let R := normalizedCrossNaturalScaleThreshold m + 1
  tailFinsetOfFinset F
    (Λ.finite_indices_in_Icc (-R) R).toFinset

/-- Outside the order-dependent finite central set, the physical square is
beyond the normalized-kernel threshold. -/
theorem threshold_le_sq_of_not_mem_carrierTailNaturalScaleCentralSet
    (Λ : TwoSidedCarrier) (F : Finset ℤ) (m : ℕ)
    (i : FineLogTailIndex F)
    (hi : i ∉ carrierTailNaturalScaleCentralSet Λ F m) :
    normalizedCrossNaturalScaleThreshold m ≤ (Λ i.1) ^ 2 := by
  let R := normalizedCrossNaturalScaleThreshold m + 1
  have hnot : Λ i.1 ∉ Set.Icc (-R) R := by
    intro hmem
    apply hi
    rw [carrierTailNaturalScaleCentralSet, mem_tailFinsetOfFinset]
    exact (Λ.finite_indices_in_Icc (-R) R).mem_toFinset.mpr hmem
  have habs : R < |Λ i.1| := by
    apply lt_of_not_ge
    intro hle
    exact hnot (abs_le.mp hle)
  have hthreshold := normalizedCrossNaturalScaleThreshold_nonneg m
  dsimp only [R] at habs
  nlinarith [sq_abs (Λ i.1)]

/-- The concrete tail remainder is compact once the chosen tail retains a
strict signed-square separation constant.  Deep-tail entries are dominated
by a separable square-summable weight; the finitely many central rows and
columns are then restored by a compact finite-rank truncation. -/
theorem carrierTailCrossRemainder_isCompact_and_adjoint
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) (F : Finset ℤ)
    (T : CoefficientSpace (FineLogTailIndex F) →L[ℂ]
      CoefficientSpace (FineLogTailIndex F))
    (hT : ∀ i j,
      inner ℂ (coefficientAtom i) (T (coefficientAtom j)) =
        normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1))
    {d : ℝ} (hd : 1 < d)
    (houtside : ∀ j, j ∉ F → 1 < (Λ j) ^ 2)
    (hsep : ∀ i j, i ∉ F → j ∉ F → i ≠ j →
      d ≤ |signedSquare (Λ i) - signedSquare (Λ j)|) :
    IsCompactOperator (carrierTailCrossRemainder m hm Λ B F T) ∧
      IsCompactOperator
        (carrierTailCrossRemainder m hm Λ B F T).adjoint := by
  let R := carrierTailCrossRemainder m hm Λ B F T
  let E := carrierTailNaturalScaleCentralSet Λ F m
  let Q := cofiniteCoordinateCompression R E
  let w : FineLogTailIndex F → ℝ := fun i ↦
    inverseThreeQuarterSignedSquareWeight (Λ i.1)
  have hthree := summable_tail_signedSquare_rpow_neg_three_halves
    houtside hd hsep
  have hw : Summable (fun i : FineLogTailIndex F ↦ w i ^ 2) := by
    apply hthree.congr
    intro i
    dsimp only [w, inverseThreeQuarterSignedSquareWeight]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    ring
  have hw0 (i : FineLogTailIndex F) : 0 ≤ w i := by
    exact Real.rpow_nonneg (abs_nonneg _) _
  have hprod : Summable (fun z : FineLogTailIndex F × FineLogTailIndex F ↦
      w z.1 ^ 2 * w z.2 ^ 2) :=
    hw.mul_of_nonneg hw (fun i ↦ sq_nonneg _) (fun j ↦ sq_nonneg _)
  have hmajorant : Summable
      (fun z : FineLogTailIndex F × FineLogTailIndex F ↦
        normalizedCrossSquareSummableConstant m ^ 2 *
          (w z.1 ^ 2 * w z.2 ^ 2)) :=
    hprod.mul_left _
  have hQcoeff : Summable
      (fun z : FineLogTailIndex F × FineLogTailIndex F ↦
        ‖inner ℂ (coefficientAtom z.1) (Q (coefficientAtom z.2))‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun _ ↦ sq_nonneg _) _ hmajorant
    intro z
    rw [show inner ℂ (coefficientAtom z.1) (Q (coefficientAtom z.2)) =
        if z.1 ∉ E ∧ z.2 ∉ E then
          normalizedHermiteCrossKernel m hm (Λ z.1.1) (Λ z.2.1) -
            normalizedCrossSpatialLeadingTerm m (Λ z.1.1) (Λ z.2.1)
        else 0 by
      simpa only [R, Q, E] using
        cofiniteCarrierTailCrossRemainder_entry m hm Λ B F T hT E z.1 z.2]
    split_ifs with hz
    · have hentry :=
        norm_normalizedHermiteCrossKernel_sub_gramLeading_le_separable
          m hm
          (threshold_le_sq_of_not_mem_carrierTailNaturalScaleCentralSet
            Λ F m z.1 hz.1)
          (threshold_le_sq_of_not_mem_carrierTailNaturalScaleCentralSet
            Λ F m z.2 hz.2)
      have hright : 0 ≤ normalizedCrossSquareSummableConstant m *
          w z.1 * w z.2 := by
        exact mul_nonneg
          (mul_nonneg
            (normalizedCrossSquareSummableConstant_nonneg m hm) (hw0 z.1))
          (hw0 z.2)
      calc
        ‖normalizedHermiteCrossKernel m hm (Λ z.1.1) (Λ z.2.1) -
            normalizedCrossSpatialLeadingTerm m (Λ z.1.1) (Λ z.2.1)‖ ^ 2 ≤
            (normalizedCrossSquareSummableConstant m *
              w z.1 * w z.2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hentry 2
        _ = normalizedCrossSquareSummableConstant m ^ 2 *
            (w z.1 ^ 2 * w z.2 ^ 2) := by ring
    · simp only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      positivity
  change IsCompactOperator R ∧ IsCompactOperator R.adjoint
  exact isCompactOperator_and_adjoint_of_cofinite_summable_matrixCoeff_sq
    R E hQcoeff

/-- Compactness of the concrete carrier tail remainder. -/
theorem carrierTailCrossRemainder_isCompact
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) (F : Finset ℤ)
    (T : CoefficientSpace (FineLogTailIndex F) →L[ℂ]
      CoefficientSpace (FineLogTailIndex F))
    (hT : ∀ i j,
      inner ℂ (coefficientAtom i) (T (coefficientAtom j)) =
        normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1))
    {d : ℝ} (hd : 1 < d)
    (houtside : ∀ j, j ∉ F → 1 < (Λ j) ^ 2)
    (hsep : ∀ i j, i ∉ F → j ∉ F → i ≠ j →
      d ≤ |signedSquare (Λ i) - signedSquare (Λ j)|) :
    IsCompactOperator (carrierTailCrossRemainder m hm Λ B F T) :=
  (carrierTailCrossRemainder_isCompact_and_adjoint
    m hm Λ B F T hT hd houtside hsep).1

/-- Compactness of the adjoint of the concrete carrier tail remainder. -/
theorem carrierTailCrossRemainder_adjoint_isCompact
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) (F : Finset ℤ)
    (T : CoefficientSpace (FineLogTailIndex F) →L[ℂ]
      CoefficientSpace (FineLogTailIndex F))
    (hT : ∀ i j,
      inner ℂ (coefficientAtom i) (T (coefficientAtom j)) =
        normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1))
    {d : ℝ} (hd : 1 < d)
    (houtside : ∀ j, j ∉ F → 1 < (Λ j) ^ 2)
    (hsep : ∀ i j, i ∉ F → j ∉ F → i ≠ j →
      d ≤ |signedSquare (Λ i) - signedSquare (Λ j)|) :
    IsCompactOperator
      (carrierTailCrossRemainder m hm Λ B F T).adjoint :=
  (carrierTailCrossRemainder_isCompact_and_adjoint
    m hm Λ B F T hT hd houtside hsep).2

/-- Extending the leading tail operator by zero gives a compact model of the
full genuine raw carrier cross; the same is proved separately for the
adjoint difference. -/
theorem carrierRawCrossOperator_sub_extendTailOperator_isCompact_and_adjoint
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) (F : Finset ℤ)
    (T : CoefficientSpace (FineLogTailIndex F) →L[ℂ]
      CoefficientSpace (FineLogTailIndex F))
    (hT : ∀ i j,
      inner ℂ (coefficientAtom i) (T (coefficientAtom j)) =
        normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1))
    {d : ℝ} (hd : 1 < d)
    (houtside : ∀ j, j ∉ F → 1 < (Λ j) ^ 2)
    (hsep : ∀ i j, i ∉ F → j ∉ F → i ≠ j →
      d ≤ |signedSquare (Λ i) - signedSquare (Λ j)|) :
    IsCompactOperator
        (carrierRawCrossOperator m hm Λ B - extendTailOperator F T) ∧
      IsCompactOperator
        ((carrierRawCrossOperator m hm Λ B).adjoint -
          (extendTailOperator F T).adjoint) := by
  let E : CoefficientSpace (FineLogTailIndex F) →L[ℂ]
      CoefficientSpace ℤ := tailCoefficientEmbedding F
  let P : CoefficientSpace ℤ →L[ℂ] CoefficientSpace ℤ := E ∘L E.adjoint
  let Ξ := carrierRawCrossOperator m hm Λ B
  let Rt := carrierTailCrossRemainder m hm Λ B F T
  let C := finiteCentralTruncation Ξ F
  have hRt := carrierTailCrossRemainder_isCompact_and_adjoint
    m hm Λ B F T hT hd houtside hsep
  have hP : P = cofiniteCoordinateProjection F := by
    simpa only [P, E, cofiniteCoordinateProjection] using
      tailCoefficientEmbedding_comp_adjoint F
  have hExt : extendTailOperator F Rt =
      P ∘L Ξ ∘L P - extendTailOperator F T := by
    dsimp only [Rt, Ξ]
    unfold carrierTailCrossRemainder carrierTailRawCoefficientCross
      extendTailOperator
    change E ∘L ((E.adjoint ∘L Ξ ∘L E) - T) ∘L E.adjoint =
      (E ∘L E.adjoint) ∘L Ξ ∘L (E ∘L E.adjoint) -
        E ∘L T ∘L E.adjoint
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, sub_apply, map_sub]
  have hcentral : C + (P ∘L Ξ ∘L P) = Ξ := by
    have hdecomp : finiteCentralTruncation Ξ F +
        cofiniteCoordinateCompression Ξ F = Ξ := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [finiteCentralTruncation, finiteCoordinateCompression,
        cofiniteCoordinateCompression, cofiniteCoordinateProjection,
        ContinuousLinearMap.comp_apply, add_apply, sub_apply,
        one_apply_eq_self, map_sub]
      abel
    simpa only [C, hP, cofiniteCoordinateCompression] using hdecomp
  have hfull : Ξ - extendTailOperator F T =
      C + extendTailOperator F Rt := by
    calc
      Ξ - extendTailOperator F T =
          (C + (P ∘L Ξ ∘L P)) - extendTailOperator F T := by rw [hcentral]
      _ = C + ((P ∘L Ξ ∘L P) - extendTailOperator F T) := by abel
      _ = C + extendTailOperator F Rt := by rw [hExt]
  have hC : IsCompactOperator C := finiteCentralTruncation_isCompact Ξ F
  have hExtRt : IsCompactOperator (extendTailOperator F Rt) :=
    extendTailOperator_isCompact F Rt hRt.1
  have hCadj : IsCompactOperator C.adjoint := by
    rw [show C.adjoint = finiteCentralTruncation Ξ.adjoint F by
      exact finiteCentralTruncation_adjoint Ξ F]
    exact finiteCentralTruncation_isCompact Ξ.adjoint F
  have hExtRtAdj : IsCompactOperator (extendTailOperator F Rt).adjoint := by
    rw [extendTailOperator_adjoint]
    exact extendTailOperator_isCompact F Rt.adjoint hRt.2
  constructor
  · change IsCompactOperator (Ξ - extendTailOperator F T)
    rw [hfull]
    exact hC.add hExtRt
  · have hfullAdj : (Ξ - extendTailOperator F T).adjoint =
        C.adjoint + (extendTailOperator F Rt).adjoint := by
      rw [hfull, map_add]
    rw [← map_sub]
    rw [hfullAdj]
    exact hCadj.add hExtRtAdj

/-- Strict subcriticality supplies one finite tail and one leading-operator
constant, chosen before the Hermite order, such that every genuine raw tail
cross is the sum of the exact bounded leading operator and a compact
remainder. -/
theorem TwoSidedCarrier.StrictSubcritical.exists_uniform_boundedLeadingTailOperator_with_compactRemainder
    {Λ : TwoSidedCarrier} (hΛ : Λ.StrictSubcritical) :
    ∃ (F : Finset ℤ) (CΛ : NNReal),
      (∀ j, j ∉ F → 1 < (Λ j) ^ 2) ∧
      (∀ i j, i ∉ F → j ∉ F → i ≠ j →
        1 ≤ |signedSquare (Λ i) - signedSquare (Λ j)|) ∧
      ∀ (m : ℕ) (hm : 1 ≤ m),
        ∃ T : CoefficientSpace (FineLogTailIndex F) →L[ℂ]
            CoefficientSpace (FineLogTailIndex F),
          (∀ i j,
            inner ℂ (coefficientAtom i) (T (coefficientAtom j)) =
              normalizedCrossSpatialLeadingTerm m (Λ i.1) (Λ j.1)) ∧
          ‖T‖ ≤ (CΛ : ℝ) * gramNormalization m * (m + 1 : ℝ) *
            (4 : ℝ)⁻¹ ^ m ∧
          IsCompactOperator
            (carrierTailRawCoefficientCross m hm Λ
              hΛ.carrierHermiteBesselAnalysis F - T) := by
  obtain ⟨d, hd, F, hsep, houtside⟩ :=
    hΛ.exists_strictSeparated_noncentral_tail
  have hsepOne : ∀ i j, i ∉ F → j ∉ F → i ≠ j →
      1 ≤ |signedSquare (Λ i) - signedSquare (Λ j)| := by
    intro i j hi hj hij
    exact hd.le.trans (hsep i j hi hj hij)
  obtain ⟨CΛ, hlead⟩ :=
    MeyerGeneralProblem.exists_uniform_boundedLeadingTailOperator
      (Λ := Λ) (F := F) houtside hsepOne
  refine ⟨F, CΛ, houtside, hsepOne, ?_⟩
  intro m hm
  obtain ⟨T, hT, hnorm⟩ := hlead m hm
  refine ⟨T, hT, hnorm, ?_⟩
  change IsCompactOperator
    (carrierTailCrossRemainder m hm Λ
      hΛ.carrierHermiteBesselAnalysis F T)
  exact carrierTailCrossRemainder_isCompact m hm Λ
    hΛ.carrierHermiteBesselAnalysis F T hT hd houtside hsep

end

end MeyerGeneralProblem
