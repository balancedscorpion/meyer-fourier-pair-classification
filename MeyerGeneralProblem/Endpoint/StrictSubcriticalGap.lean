module

public import MeyerGeneralProblem.Endpoint.CarrierModelAssembly
public import MeyerGeneralProblem.Endpoint.ExponentialSqueeze

@[expose] public section

/-!
# Unrestricted strict-subcritical endpoint gap

This module closes the concrete carrier argument.  One finite carrier tail and
one cross constant are selected before the Hermite order.  At every order the
full universal Gram model and restored leading cross model differ compactly
from the genuine operators.  Their common Gram normalization cancels, and the
remaining linear-geometric ratio is eventually below one.
-/

namespace MeyerGeneralProblem

open Filter

noncomputable section

/-- The universal Gram lower constant is exactly the floor used by the final
endpoint squeeze; the two definitions deliberately retain their independent
analytic origins. -/
theorem universalGramLowerConstant_eq_universalGramFloor
    (m : ℕ) (a d : ℝ) :
    universalGramLowerConstant m a d =
      universalGramFloor m (gramNormalization m) a d := by
  unfold universalGramLowerConstant universalGramFloor
    cosineInghamFloorFactor inghamFloorFactor
  rfl

/-- Unrestricted Hypothesis A for an arbitrary two-sided strictly
subcritical carrier: at every sufficiently large Hermite order, the exact
reduced endpoint radius is strictly below one.  The positive-order proof is
kept explicit because the concrete Hermite coefficient model is normalized
only for `1 ≤ m`. -/
theorem strictSubcritical_endpointGap
    (Λ : TwoSidedCarrier) (hΛ : Λ.StrictSubcritical) :
    ∀ᶠ m : ℕ in atTop, ∀ hm : 1 ≤ m,
      hΛ.carrierEndpointRadius m hm < 1 := by
  let D := hΛ.universalTailData
  obtain ⟨CΛ, hcrossModel⟩ :=
    D.exists_uniform_fullLeadingCrossModel
      (fun m hm ↦ hΛ.carrierHermiteBesselAnalysis)
  have hI : 0 < inghamFloorFactor D.a D.d := by
    simpa only [inghamFloorFactor, cosineInghamFloorFactor] using
      cosineInghamFloorFactor_pos D.ha D.had
  have hratio := eventually_endpointSqueezeRatio_lt_one
    CΛ.coe_nonneg hI D.ha.le D.ha_lt_half
  filter_upwards [hratio] with m hratioM
  intro hm
  obtain ⟨B₀, hB₀, hCross, hCrossAdjoint⟩ := hcrossModel m hm
  let G₀ : CoefficientSpace ℤ →L[ℂ] CoefficientSpace ℤ :=
    D.fullGramModel m hm
  have hG := hΛ.carrierCoefficientGram_strictlyPositive m hm
  have hG₀ : IsStrictlyPositive G₀ := by
    simpa only [G₀] using D.fullGramModel_strictlyPositive m hm
  have hGram : IsCompactOperator
      (carrierCoefficientGram m hm Λ hΛ.carrierHermiteBesselAnalysis - G₀) := by
    simpa only [G₀] using
      D.carrierCoefficientGram_sub_fullGramModel_isCompact
        m hm hΛ.carrierHermiteBesselAnalysis
  have hfloor : universalGramLowerConstant m D.a D.d •
        (1 : CoefficientSpace ℤ →L[ℂ] CoefficientSpace ℤ) ≤ G₀ := by
    simpa only [G₀] using D.fullGramModel_lowerBound m hm
  have hBceiling : ‖B₀‖ ≤
      leadingCrossCeiling m (CΛ : ℝ) (gramNormalization m) := by
    simpa only [leadingCrossCeiling, Nat.cast_add, Nat.cast_one] using hB₀
  have hgap : leadingCrossCeiling m (CΛ : ℝ) (gramNormalization m) /
        universalGramLowerConstant m D.a D.d < 1 := by
    calc
      leadingCrossCeiling m (CΛ : ℝ) (gramNormalization m) /
          universalGramLowerConstant m D.a D.d =
          endpointSqueezeRatio m (CΛ : ℝ) D.a D.d := by
        rw [universalGramLowerConstant_eq_universalGramFloor]
        exact leadingCrossCeiling_div_floor m
          (gramNormalization_pos hm).ne' hI.ne'
      _ < 1 := hratioM
  have hnorm :=
    CarrierUniversalTailData.carrierWhitenedReducedCross_norm_lt_one_of_fullModels
    m hm hΛ.carrierHermiteBesselAnalysis hG G₀ B₀ hG₀ hGram hCross
      hCrossAdjoint (universalGramLowerConstant_pos hm D.ha D.had)
      hfloor hBceiling hgap
  change carrierReducedEndpointRadius
      m hm Λ hΛ.carrierHermiteBesselAnalysis < 1
  rw [carrierReducedEndpointRadius_eq_whitenedReducedCross_norm_sq
    m hm Λ hΛ.carrierHermiteBesselAnalysis hG]
  nlinarith [norm_nonneg
    (carrierWhitenedReducedCross m hm Λ
      hΛ.carrierHermiteBesselAnalysis hG)]

end

end MeyerGeneralProblem
