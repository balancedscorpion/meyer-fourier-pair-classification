module

public import MeyerGeneralProblem.Trace.Presentation
public import MeyerGeneralProblem.Endpoint.IntrinsicFixedOrder
public import MeyerGeneralProblem.Endpoint.StrictSubcriticalGap

@[expose] public section

/-!
# Exact point-trace interfaces for the extensional endpoint

The legacy ordered carrier and the extensional carrier generate the same
genuine Dirac spans. The endpoint radius is therefore independent of the
chosen Bessel analysis data. A point-trace presentation is constructed only
after a genuine strictly positive Gram bound closes its synthesis range.
This identification concerns the Hilbert vanishing ideal, not the still
separate arbitrary-carrier same-order Schwartz-density theorem.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- Continuous linear equivalences transport the actual closed atomic span. -/
theorem atomicSupportSubspace_map_continuousLinearEquiv
    {ι H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (e : H ≃L[ℂ] K) (v : ι → H) :
    (atomicSupportSubspace v).map e.toLinearMap =
      atomicSupportSubspace (fun i => e (v i)) := by
  have hclosure : (Submodule.span ℂ (Set.range v)).topologicalClosure.map e.toLinearMap =
      ((Submodule.span ℂ (Set.range v)).map e.toLinearMap).topologicalClosure := by
    apply SetLike.ext'
    exact e.toHomeomorph.image_closure _
  unfold atomicSupportSubspace
  rw [hclosure, Submodule.map_span, ← Set.range_comp]
  rfl

/-- Integer-indexed and subtype-indexed normalized Dirac families have exactly
the same range, with no enumeration-dependent multiplicity. -/
theorem range_carrierHermitePointMass_eq_extensional
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier) :
    Set.range (carrierHermitePointMass m hm Λ) =
      Set.range (locallyFiniteCarrierHermitePointMass m hm Λ.toLocallyFinite) := by
  ext u
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨⟨Λ j, ⟨j, rfl⟩⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨j, hj⟩ := x.property
    exact ⟨j, by simp only [carrierHermitePointMass,
      locallyFiniteCarrierHermitePointMass, hj]⟩

/-- The extensional intrinsic physical support is the legacy ordered closed
Dirac span. No Bessel or Riesz assumption is needed for this span equality. -/
theorem fixedOrderPhysicalSupport_eq_carrierAtomicSpan
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier) :
    (fixedOrderPhysicalSupport Λ.toLocallyFinite m hm).toSubmodule =
      atomicSupportSubspace (carrierHermitePointMass m hm Λ) := by
  rw [fixedOrderPhysicalSupport,
    ← locallyFiniteAtomicSupportSubspace_eq_supportedHermiteMeasureSubspace]
  unfold atomicSupportSubspace
  rw [range_carrierHermitePointMass_eq_extensional]

/-- The legacy endpoint's physical support is exactly the extensional support,
independently of the Bessel witness. -/
theorem carrierPhysicalAtomicSupport_eq_fixedOrderPhysicalSupport
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    carrierPhysicalAtomicSupport m hm Λ B =
      fixedOrderPhysicalSupport Λ.toLocallyFinite m hm := by
  apply SetLike.ext
  intro u
  change u ∈ (carrierPhysicalAtomicSupport m hm Λ B).toSubmodule ↔
    u ∈ (fixedOrderPhysicalSupport Λ.toLocallyFinite m hm).toSubmodule
  rw [carrierPhysicalAtomicSupport_toSubmodule, fixedOrderPhysicalSupport_eq_carrierAtomicSpan]

/-- The inverse-Fourier atomic support is exactly the extensional inverse-
Fourier support, using an actual continuous equivalence of closed spans. -/
theorem carrierInverseFourierAtomicSupport_eq_fixedOrderInverseFourierSupport
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    carrierInverseFourierAtomicSupport m hm Λ B =
      fixedOrderInverseFourierSupport Λ.toLocallyFinite m hm := by
  apply SetLike.ext
  intro u
  change u ∈ (carrierInverseFourierAtomicSupport m hm Λ B).toSubmodule ↔
    u ∈ (fixedOrderInverseFourierSupport Λ.toLocallyFinite m hm).toSubmodule
  rw [carrierInverseFourierAtomicSupport_toSubmodule, fixedOrderInverseFourierSupport,
    ClosedSubmodule.mapEquiv_apply, fixedOrderPhysicalSupport_eq_carrierAtomicSpan,
    atomicSupportSubspace_map_continuousLinearEquiv]
  rfl

/-- The genuine carrier endpoint radius is precisely the extensional intrinsic
radius. This removes Bessel-witness and enumeration dependence. -/
theorem carrierReducedEndpointRadius_eq_fixedOrderReducedRadius
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    carrierReducedEndpointRadius m hm Λ B =
      fixedOrderReducedRadius Λ.toLocallyFinite m hm := by
  simp only [carrierReducedEndpointRadius, fixedOrderReducedRadius,
    carrierPhysicalAtomicSupport_eq_fixedOrderPhysicalSupport,
    carrierInverseFourierAtomicSupport_eq_fixedOrderInverseFourierSupport]

/-- Exact point-trace presentation of the intrinsic physical layer, requiring
both genuine Bessel synthesis and a strictly positive actual coefficient Gram. -/
def carrierPointTracePresentation
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (hG : IsStrictlyPositive (carrierCoefficientGram m hm Λ B)) :
    TracePresentation (fixedOrderPhysicalSupport Λ.toLocallyFinite m hm) ℤ where
  system := ⟨carrierHermitePointMass m hm Λ, B⟩
  gram_strictlyPositive := hG
  synthesis_range_eq := by
    change (carrierPointMassSynthesis m hm Λ B).range = _
    rw [carrierPointMassSynthesis_range_eq_atomicSupportSubspace m hm Λ B hG,
      fixedOrderPhysicalSupport_eq_carrierAtomicSpan]

/-- The preserved strict-subcritical theorem also holds for the extensional
intrinsic radius. This is a correspondence regression, not the new
density-sharp no-separation theorem. -/
theorem strictSubcritical_intrinsicEndpointGap
    (Λ : TwoSidedCarrier) (hΛ : Λ.StrictSubcritical) :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ hm : 1 ≤ m,
      fixedOrderReducedRadius Λ.toLocallyFinite m hm < 1 := by
  filter_upwards [strictSubcritical_endpointGap Λ hΛ] with m hm
  intro hpositive
  have h := hm hpositive
  change carrierReducedEndpointRadius m hpositive Λ hΛ.carrierHermiteBesselAnalysis < 1 at h
  rwa [carrierReducedEndpointRadius_eq_fixedOrderReducedRadius] at h

end

end MeyerGeneralProblem
