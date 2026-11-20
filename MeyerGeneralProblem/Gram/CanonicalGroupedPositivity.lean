module

public import MeyerGeneralProblem.Carrier.GroupedSynthesisInjectivity
public import MeyerGeneralProblem.Gram.GroupedUniversalPositivity
public import MeyerGeneralProblem.Gram.CompactPositivePerturbation

@[expose] public section

/-!
# Coercivity of the full canonical grouped Gram

The genuine full synthesis is injective by cluster-dual Schwartz tests.
Its Gram is a compact perturbation of the density-derived coercive universal
Gram. The Fredholm alternative therefore gives strict positivity, a lower
Riesz bound, and an actual trace presentation of intrinsic physical support.
All central groups remain present and the physical Hermite order is unchanged.
-/

namespace MeyerGeneralProblem

noncomputable section

namespace BoundedClusterOrder

variable {S : LocallyFiniteCarrier} {d : ℝ} {q : ℕ}
  (horder : BoundedClusterOrder S.signedSquareImage d q)

/-- Genuine full canonical grouped synthesis is injective, including every
finite central group and every original initial-prefix coordinate. -/
theorem actualGroupedSynthesis_injective (hd : 0 < d) (m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) :
    Function.Injective (horder.actualGroupedBesselAnalysis hd m hm).synthesis :=
  horder.signedGrouping.groupedSynthesis_injective m _
    (horder.actualGroupedBesselAnalysis hd m hm)

/-- The actual full grouped Gram has trivial kernel, without a lower-bound
assumption. -/
theorem actualGroupedGramOperator_injective (hd : 0 < d) (m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) :
    Function.Injective (horder.actualGroupedGramOperator hd m hm) :=
  horder.signedGrouping.groupedCoefficientGram_injective m _
    (horder.actualGroupedBesselAnalysis hd m hm)

/-- The actual universal grouped Gram is strictly positive under its genuine
upper-density hypothesis; this also covers an empty carrier. -/
theorem universalGroupedGramOperator_strictlyPositive (hd : 0 < d) (m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) {W : ℝ} (hW : 0 < W)
    (hS : upperUniformBeurlingDensity S.signedSquareImage < ENNReal.ofReal (2*W)) :
    IsStrictlyPositive (horder.universalGroupedGramOperator hd m hm) := by
  obtain ⟨a, ha, hfloor⟩ :=
    horder.exists_universalGroupedGramOperator_lowerBound hd m hm hW hS
  rcases subsingleton_or_nontrivial (CoefficientSpace horder.signedGrouping.Index) with h | h
  · let := h
    rw [Subsingleton.elim (horder.universalGroupedGramOperator hd m hm) 1]
    exact isStrictlyPositive_one
  · let := h
    exact strictlyPositive_of_positive_scalar_floor _ ha hfloor

/-- Injectivity eliminates the possible finite-dimensional kernel in the
full actual-minus-universal compact comparison. -/
theorem actualGroupedGramOperator_strictlyPositive (hd : 0 < d) (m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) {W : ℝ} (hW : 0 < W)
    (hS : upperUniformBeurlingDensity S.signedSquareImage < ENNReal.ofReal (2*W)) :
    IsStrictlyPositive (horder.actualGroupedGramOperator hd m hm) := by
  apply strictlyPositive_of_compact_perturbation_of_injective
    (horder.actualGroupedGramOperator hd m hm) (horder.universalGroupedGramOperator hd m hm)
  · exact (ContinuousLinearMap.nonneg_iff_isPositive).mpr
      (ContinuousLinearMap.isPositive_adjoint_comp_self
        (horder.actualGroupedBesselAnalysis hd m hm).synthesis)
  · exact horder.universalGroupedGramOperator_strictlyPositive hd m hm hW hS
  · exact horder.actualGroupedGram_sub_universal_isCompact hd m hm
  · exact horder.actualGroupedGramOperator_injective hd m hm

/-- The original full grouped synthesis has closed range. -/
theorem actualGroupedSynthesis_isClosed_range (hd : 0 < d) (m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) {W : ℝ} (hW : 0 < W)
    (hS : upperUniformBeurlingDensity S.signedSquareImage < ENNReal.ofReal (2*W)) :
    IsClosed (Set.range (horder.actualGroupedBesselAnalysis hd m hm).synthesis) :=
  isClosed_range_of_coefficientGram_strictlyPositive _
    (horder.actualGroupedGramOperator_strictlyPositive hd m hm hW hS)

/-- A genuine lower Riesz bound for all square-summable original grouped
coordinates. The positive constant is independent of the coefficient vector. -/
theorem exists_actualGrouped_synthesis_lower (hd : 0 < d) (m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) {W : ℝ} (hW : 0 < W)
    (hS : upperUniformBeurlingDensity S.signedSquareImage < ENNReal.ofReal (2*W)) :
    ∃ a : ℝ, 0 < a ∧ ∀ c : CoefficientSpace horder.signedGrouping.Index,
      a*‖c‖^2 ≤ ‖(horder.actualGroupedBesselAnalysis hd m hm).synthesis c‖^2 := by
  let B := horder.actualGroupedBesselAnalysis hd m hm
  obtain ⟨K, hK⟩ := B.synthesis.antilipschitz_of_injective_of_isClosed_range
    (horder.actualGroupedSynthesis_injective hd m hm)
    (horder.actualGroupedSynthesis_isClosed_range hd m hm hW hS)
  have hpos : 0 < (K : ℝ)+1 := by positivity
  refine ⟨(((K : ℝ)+1)^2)⁻¹, inv_pos.mpr (sq_pos_of_pos hpos), ?_⟩
  intro c
  have hbound := hK.le_mul_dist c 0
  simp only [dist_zero_right, map_zero] at hbound
  have hbound' : ‖c‖ ≤ ((K : ℝ)+1)*‖B.synthesis c‖ := by
    nlinarith [norm_nonneg (B.synthesis c)]
  have hsquare : ‖c‖^2 ≤ (((K : ℝ)+1)*‖B.synthesis c‖)^2 := by
    nlinarith [norm_nonneg c, norm_nonneg (B.synthesis c)]
  calc
    (((K : ℝ)+1)^2)⁻¹*‖c‖^2 ≤
        (((K : ℝ)+1)^2)⁻¹*(((K : ℝ)+1)*‖B.synthesis c‖)^2 :=
      mul_le_mul_of_nonneg_left hsquare (by positivity)
    _ = ‖B.synthesis c‖^2 := by field_simp

/-- The density-derived actual grouped family is a trace presentation of
the intrinsic physical support, not merely a presentation of a tail. -/
def actualGroupedTracePresentation (hd : 0 < d) (m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) {W : ℝ} (hW : 0 < W)
    (hS : upperUniformBeurlingDensity S.signedSquareImage < ENNReal.ofReal (2*W)) :
    TracePresentation (fixedOrderPhysicalSupport S m
      (by have := (le_max_left _ _).trans hm; omega)) horder.signedGrouping.Index :=
  horder.signedGrouping.tracePresentation m _ (horder.actualGroupedBesselAnalysis hd m hm)
    (horder.actualGroupedGramOperator_strictlyPositive hd m hm hW hS)

/-- The resulting synthesis range is exactly the full intrinsic physical
support, with all original cluster coordinates retained. -/
theorem actualGroupedSynthesis_range (hd : 0 < d) (m : ℕ)
    (hm : groupedHermiteDifferentiationOrder (q+1) ≤ m) {W : ℝ} (hW : 0 < W)
    (hS : upperUniformBeurlingDensity S.signedSquareImage < ENNReal.ofReal (2*W)) :
    (horder.actualGroupedBesselAnalysis hd m hm).synthesis.range =
      (fixedOrderPhysicalSupport S m
        (by have := (le_max_left _ _).trans hm; omega)).toSubmodule :=
  (horder.actualGroupedTracePresentation hd m hm hW hS).synthesis_range_eq

end BoundedClusterOrder

end

end MeyerGeneralProblem
