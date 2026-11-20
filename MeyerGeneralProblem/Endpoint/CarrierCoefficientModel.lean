module

public import MeyerGeneralProblem.Carrier.HermiteMeasureSupport
public import MeyerGeneralProblem.Carrier.HermiteCross
public import MeyerGeneralProblem.Endpoint.SquareWhitenedReducedCross
public import MeyerGeneralProblem.Gram.CarrierGramStrictPositivity

@[expose] public section

/-!
# Concrete carrier coefficient model

This module instantiates the abstract Gram, cross, and whitening operators with
the genuine normalized Hermite point-mass synthesis on a two-sided carrier.
Its matrix-entry theorems identify those operators with actual physical and
Fourier atomic inner products. In particular, exact diagonal normalization is
proved rather than postulated.
-/

namespace MeyerGeneralProblem

noncomputable section

/-- Same-side Gram operator of the genuine normalized carrier point masses. -/
def carrierCoefficientGram
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    CoefficientSpace ℤ →L[ℂ] CoefficientSpace ℤ :=
  coefficientGram (carrierPointMassSynthesis m hm Λ B)

/-- Re-expose strict positivity at the unfolded physical coefficient-Gram
type expected by the generic whitening interface. -/
theorem carrierCoefficientGram_strictlyPositive_unfold
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (hG : IsStrictlyPositive (carrierCoefficientGram m hm Λ B)) :
    IsStrictlyPositive
      (coefficientGram (carrierPointMassSynthesis m hm Λ B)) := by
  simpa only [carrierCoefficientGram] using hG

/-- Strict subcriticality unconditionally supplies strict positivity of the
full genuine carrier coefficient Gram used by global whitening. -/
theorem TwoSidedCarrier.StrictSubcritical.carrierCoefficientGram_strictlyPositive
    {Λ : TwoSidedCarrier} (hΛ : Λ.StrictSubcritical)
    (m : ℕ) (hm : 1 ≤ m) :
    IsStrictlyPositive
      (carrierCoefficientGram m hm Λ
        hΛ.carrierHermiteBesselAnalysis) := by
  simpa only [carrierCoefficientGram] using
    hΛ.universalTailData.carrierCoefficientGram_strictlyPositive
      m hm hΛ.carrierHermiteBesselAnalysis

/-- Raw physical/Fourier cross operator of the genuine normalized carrier
point-mass systems. -/
def carrierRawCoefficientCross
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    CoefficientSpace ℤ →L[ℂ] CoefficientSpace ℤ :=
  rawCoefficientCross
    (carrierPointMassSynthesis m hm Λ B)
    (carrierFourierPointMassSynthesis m hm Λ B)

/-- Globally whitened concrete physical/Fourier carrier cross operator. -/
def carrierWhitenedCoefficientCross
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    CoefficientSpace ℤ →L[ℂ] CoefficientSpace ℤ :=
  whitenedCoefficientCross
    (carrierPointMassSynthesis m hm Λ B)
    (carrierFourierPointMassSynthesis m hm Λ B)

/-- A same-side Gram matrix entry is the inner product of the corresponding
genuine normalized Hermite point masses. -/
theorem carrierCoefficientGram_entry
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) (i j : ℤ) :
    inner ℂ (coefficientAtom i)
      (carrierCoefficientGram m hm Λ B (coefficientAtom j)) =
      inner ℂ (carrierHermitePointMass m hm Λ i)
        (carrierHermitePointMass m hm Λ j) := by
  rw [carrierCoefficientGram, coefficientGram,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right,
    carrierPointMassSynthesis_coefficientAtom,
    carrierPointMassSynthesis_coefficientAtom]

/-- The concrete same-side Gram has diagonal exactly one. -/
@[simp]
theorem carrierCoefficientGram_diagonal
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) (j : ℤ) :
    inner ℂ (coefficientAtom j)
      (carrierCoefficientGram m hm Λ B (coefficientAtom j)) = 1 := by
  rw [carrierCoefficientGram_entry, inner_self_eq_norm_sq_to_K,
    norm_carrierHermitePointMass]
  norm_num

/-- A raw cross matrix entry is the physical/Fourier inner product of the
corresponding genuine normalized carrier atoms. -/
theorem carrierRawCoefficientCross_entry
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) (i j : ℤ) :
    inner ℂ (coefficientAtom i)
      (carrierRawCoefficientCross m hm Λ B (coefficientAtom j)) =
      inner ℂ (carrierHermitePointMass m hm Λ i)
        (hermiteFourier (-(m : ℤ))
          (carrierHermitePointMass m hm Λ j)) := by
  rw [carrierRawCoefficientCross, rawCoefficientCross,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right,
    carrierPointMassSynthesis_coefficientAtom,
    carrierFourierPointMassSynthesis_coefficientAtom]

/-- The raw carrier cross matrix is entrywise the exact normalized
phase-weighted Hermite resolvent kernel. -/
theorem carrierRawCoefficientCross_entry_eq_normalizedHermiteCrossKernel
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) (i j : ℤ) :
    inner ℂ (coefficientAtom i)
        (carrierRawCoefficientCross m hm Λ B (coefficientAtom j)) =
      normalizedHermiteCrossKernel m hm (Λ i) (Λ j) := by
  rw [carrierRawCoefficientCross_entry]
  exact
    inner_carrierHermitePointMass_hermiteFourier_eq_crossKernel
      m hm Λ i j

/-- The Fourier-side synthesis has the same coefficient Gram operator as the
physical synthesis because Hermite Fourier is unitary. -/
theorem carrierFourierCoefficientGram_eq
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    coefficientGram (carrierFourierPointMassSynthesis m hm Λ B) =
      carrierCoefficientGram m hm Λ B := by
  let S := carrierPointMassSynthesis m hm Λ B
  let U : HermiteScale (-(m : ℤ)) →L[ℂ] HermiteScale (-(m : ℤ)) :=
    (hermiteFourier (-(m : ℤ))).toContinuousLinearEquiv.toContinuousLinearMap
  have hU : U.adjoint.comp U = 1 := by
    apply U.norm_map_iff_adjoint_comp_self.mp
    intro x
    exact hermiteFourier_norm (-(m : ℤ)) x
  rw [carrierCoefficientGram, carrierFourierPointMassSynthesis,
    coefficientGram, coefficientGram,
    ContinuousLinearMap.adjoint_comp]
  apply ContinuousLinearMap.ext
  intro c
  change S.adjoint (U.adjoint (U (S c))) = S.adjoint (S c)
  have hc := congrArg (fun V : HermiteScale (-(m : ℤ)) →L[ℂ]
      HermiteScale (-(m : ℤ)) => V (S c)) hU
  simp only [ContinuousLinearMap.comp_apply,
    one_apply_eq_self] at hc
  rw [hc]

/-- The inverse-Fourier-side synthesis has the same coefficient Gram as the
physical synthesis. -/
theorem carrierInverseFourierCoefficientGram_eq
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    coefficientGram (carrierInverseFourierPointMassSynthesis m hm Λ B) =
      carrierCoefficientGram m hm Λ B := by
  let S := carrierPointMassSynthesis m hm Λ B
  let U : HermiteScale (-(m : ℤ)) →L[ℂ] HermiteScale (-(m : ℤ)) :=
    (hermiteFourier (-(m : ℤ))).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hU : U.adjoint.comp U = 1 := by
    apply U.norm_map_iff_adjoint_comp_self.mp
    intro x
    exact (hermiteFourier (-(m : ℤ))).symm.norm_map x
  rw [carrierCoefficientGram, carrierInverseFourierPointMassSynthesis,
    coefficientGram, coefficientGram,
    ContinuousLinearMap.adjoint_comp]
  apply ContinuousLinearMap.ext
  intro c
  change S.adjoint (U.adjoint (U (S c))) = S.adjoint (S c)
  have hc := congrArg (fun V : HermiteScale (-(m : ℤ)) →L[ℂ]
      HermiteScale (-(m : ℤ)) => V (S c)) hU
  simp only [ContinuousLinearMap.comp_apply,
    one_apply_eq_self] at hc
  rw [hc]

/-- The forward raw cross `S† 𝓕 S` is exactly the coefficient cross for the
original endpoint pair `X` to `Y = 𝓕⁻¹ X`, since `(𝓕⁻¹ S)† S = S† 𝓕 S`. -/
theorem carrierRawCoefficientCross_eq_inverseFourierCross
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    rawCoefficientCross
        (carrierInverseFourierPointMassSynthesis m hm Λ B)
        (carrierPointMassSynthesis m hm Λ B) =
      carrierRawCoefficientCross m hm Λ B := by
  let S := carrierPointMassSynthesis m hm Λ B
  let U := hermiteFourier (-(m : ℤ))
  apply ContinuousLinearMap.ext
  intro c
  apply ext_inner_right ℂ
  intro d
  change inner ℂ
      ((carrierInverseFourierPointMassSynthesis m hm Λ B).adjoint (S c)) d =
    inner ℂ (S.adjoint (U (S c))) d
  rw [(carrierInverseFourierPointMassSynthesis m hm Λ B).adjoint_inner_left,
    S.adjoint_inner_left]
  change inner ℂ (S c) (U.symm (S d)) = inner ℂ (U (S c)) (S d)
  exact (U.inner_map_eq_flip (S c) (S d)).symm

/-- Concrete whitening has exactly the abstract two-sided Gram-whitened form,
with the physical and Fourier Grams identified. -/
theorem carrierWhitenedCoefficientCross_eq
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    carrierWhitenedCoefficientCross m hm Λ B =
      gramWhitener (carrierCoefficientGram m hm Λ B) *
        carrierRawCoefficientCross m hm Λ B *
          gramWhitener (carrierCoefficientGram m hm Λ B) := by
  unfold carrierWhitenedCoefficientCross whitenedCoefficientCross
  rw [carrierFourierCoefficientGram_eq]
  rfl

/-- Strict positivity of the physical carrier Gram transfers to the
Fourier-side carrier Gram by Hermite-Fourier unitarity. -/
theorem carrierFourierCoefficientGram_strictlyPositive
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (hG : IsStrictlyPositive (carrierCoefficientGram m hm Λ B)) :
    IsStrictlyPositive
      (coefficientGram (carrierFourierPointMassSynthesis m hm Λ B)) := by
  rw [carrierFourierCoefficientGram_eq]
  exact hG

/-- Strict positivity of the physical Gram transfers to the original
inverse-Fourier endpoint synthesis. -/
theorem carrierInverseFourierCoefficientGram_strictlyPositive
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (hG : IsStrictlyPositive (carrierCoefficientGram m hm Λ B)) :
    IsStrictlyPositive
      (coefficientGram
        (carrierInverseFourierPointMassSynthesis m hm Λ B)) := by
  rw [carrierInverseFourierCoefficientGram_eq]
  exact hG

/-- The global whitened cross for the original ordered endpoint pair
`X → 𝓕⁻¹ X` is the already constructed concrete matrix `G⁻¹ᐟ² S†𝓕S G⁻¹ᐟ²`. -/
theorem carrierInverseFourierWhitenedCoefficientCross_eq
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    whitenedCoefficientCross
        (carrierInverseFourierPointMassSynthesis m hm Λ B)
        (carrierPointMassSynthesis m hm Λ B) =
      carrierWhitenedCoefficientCross m hm Λ B := by
  rw [carrierWhitenedCoefficientCross_eq]
  unfold whitenedCoefficientCross
  rw [carrierInverseFourierCoefficientGram_eq,
    carrierRawCoefficientCross_eq_inverseFourierCross]
  rfl

/-- The closed physical carrier support generated by the genuine normalized
Hermite point masses. -/
def carrierPhysicalAtomicSupport
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    ClosedSubmodule ℂ (HermiteScale (-(m : ℤ))) :=
  coefficientAtomicSupport (carrierPointMassSynthesis m hm Λ B)

/-- The closed Fourier carrier support generated by the Hermite-Fourier
transforms of the genuine normalized point masses. -/
def carrierFourierAtomicSupport
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    ClosedSubmodule ℂ (HermiteScale (-(m : ℤ))) :=
  coefficientAtomicSupport (carrierFourierPointMassSynthesis m hm Λ B)

/-- The original endpoint support `Y = 𝓕⁻¹ X`. -/
def carrierInverseFourierAtomicSupport
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    ClosedSubmodule ℂ (HermiteScale (-(m : ℤ))) :=
  coefficientAtomicSupport
    (carrierInverseFourierPointMassSynthesis m hm Λ B)

/-- The physical support really is the closed span of the concrete normalized
carrier Dirac vectors. -/
theorem carrierPhysicalAtomicSupport_toSubmodule
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    (carrierPhysicalAtomicSupport m hm Λ B).toSubmodule =
      atomicSupportSubspace (carrierHermitePointMass m hm Λ) := by
  unfold carrierPhysicalAtomicSupport coefficientAtomicSupport
  apply congrArg atomicSupportSubspace
  funext j
  exact carrierPointMassSynthesis_coefficientAtom m hm Λ B j

/-- The endpoint's closed physical atomic support is exactly the intrinsic
negative Hermite-scale carrier-supported space, defined as the annihilator of
the full carrier vanishing ideal. -/
theorem carrierPhysicalAtomicSupport_eq_supportedHermiteMeasureSubspace
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    carrierPhysicalAtomicSupport m hm Λ B =
      supportedHermiteMeasureSubspace m hm Λ := by
  apply SetLike.ext
  intro T
  change T ∈ (carrierPhysicalAtomicSupport m hm Λ B).toSubmodule ↔
    T ∈ (supportedHermiteMeasureSubspace m hm Λ).toSubmodule
  rw [carrierPhysicalAtomicSupport_toSubmodule,
    atomicSupportSubspace_eq_supportedHermiteMeasureSubspace]

/-- The Fourier support really is the closed span of the transformed concrete
normalized carrier Dirac vectors. -/
theorem carrierFourierAtomicSupport_toSubmodule
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    (carrierFourierAtomicSupport m hm Λ B).toSubmodule =
      atomicSupportSubspace
        (fun j ↦ hermiteFourier (-(m : ℤ))
          (carrierHermitePointMass m hm Λ j)) := by
  unfold carrierFourierAtomicSupport coefficientAtomicSupport
  apply congrArg atomicSupportSubspace
  funext j
  exact carrierFourierPointMassSynthesis_coefficientAtom m hm Λ B j

/-- The inverse-Fourier support is the closed span of the genuine inverse
Hermite-Fourier transforms of the normalized carrier Dirac vectors. -/
theorem carrierInverseFourierAtomicSupport_toSubmodule
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) :
    (carrierInverseFourierAtomicSupport m hm Λ B).toSubmodule =
      atomicSupportSubspace
        (fun j ↦ (hermiteFourier (-(m : ℤ))).symm
          (carrierHermitePointMass m hm Λ j)) := by
  unfold carrierInverseFourierAtomicSupport coefficientAtomicSupport
  apply congrArg atomicSupportSubspace
  funext j
  exact carrierInverseFourierPointMassSynthesis_coefficientAtom m hm Λ B j

/-- A lower Riesz bound closes the physical synthesis range and identifies it
with the genuine carrier Dirac support. -/
theorem carrierPointMassSynthesis_range_eq_atomicSupportSubspace
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (hG : IsStrictlyPositive (carrierCoefficientGram m hm Λ B)) :
    (carrierPointMassSynthesis m hm Λ B).range =
      atomicSupportSubspace (carrierHermitePointMass m hm Λ) := by
  rw [← carrierPhysicalAtomicSupport_toSubmodule m hm Λ B]
  exact synthesis_range_eq_atomicSupportSubspace
    (carrierPointMassSynthesis m hm Λ B) hG

/-- The same lower Riesz bound closes the Fourier synthesis range and
identifies it with the genuine Fourier-transformed carrier support. -/
theorem carrierFourierPointMassSynthesis_range_eq_atomicSupportSubspace
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (hG : IsStrictlyPositive (carrierCoefficientGram m hm Λ B)) :
    (carrierFourierPointMassSynthesis m hm Λ B).range =
      atomicSupportSubspace
        (fun j ↦ hermiteFourier (-(m : ℤ))
          (carrierHermitePointMass m hm Λ j)) := by
  rw [← carrierFourierAtomicSupport_toSubmodule m hm Λ B]
  exact synthesis_range_eq_atomicSupportSubspace
    (carrierFourierPointMassSynthesis m hm Λ B)
    (carrierFourierCoefficientGram_strictlyPositive m hm Λ B hG)

/-- The lower Riesz bound closes the original inverse-Fourier endpoint range
and identifies it with `Y = 𝓕⁻¹ X`. -/
theorem carrierInverseFourierPointMassSynthesis_range_eq_atomicSupportSubspace
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (hG : IsStrictlyPositive (carrierCoefficientGram m hm Λ B)) :
    (carrierInverseFourierPointMassSynthesis m hm Λ B).range =
      atomicSupportSubspace
        (fun j ↦ (hermiteFourier (-(m : ℤ))).symm
          (carrierHermitePointMass m hm Λ j)) := by
  rw [← carrierInverseFourierAtomicSupport_toSubmodule m hm Λ B]
  exact synthesis_range_eq_atomicSupportSubspace
    (carrierInverseFourierPointMassSynthesis m hm Λ B)
    (carrierInverseFourierCoefficientGram_strictlyPositive m hm Λ B hG)

/-- The exact carrier coefficient domain obtained by transporting
`X ⊖ (X ∩ 𝓕⁻¹X)` through the physical-source whitening coordinates. -/
def carrierCoefficientReducedDomain
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (hG : IsStrictlyPositive (carrierCoefficientGram m hm Λ B)) :
    Submodule ℂ (CoefficientSpace ℤ) :=
  coefficientReducedDomain
    (carrierInverseFourierPointMassSynthesis m hm Λ B)
    (carrierPointMassSynthesis m hm Λ B)
    (carrierInverseFourierCoefficientGram_strictlyPositive m hm Λ B hG)
    (carrierCoefficientGram_strictlyPositive_unfold m hm Λ B hG)

/-- The genuine carrier whitened coefficient cross, restricted to the exact
reduced domain. -/
def carrierWhitenedReducedCross
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (hG : IsStrictlyPositive (carrierCoefficientGram m hm Λ B)) :
    carrierCoefficientReducedDomain m hm Λ B hG →L[ℂ] CoefficientSpace ℤ :=
  whitenedReducedCross
    (carrierInverseFourierPointMassSynthesis m hm Λ B)
    (carrierPointMassSynthesis m hm Λ B)
    (carrierInverseFourierCoefficientGram_strictlyPositive m hm Λ B hG)
    (carrierCoefficientGram_strictlyPositive_unfold m hm Λ B hG)

/-- The exact carrier reduced-domain equivalence with
`X ⊖ (X ∩ 𝓕⁻¹X)` inside the physical atomic support. -/
def carrierCoefficientReducedDomainEquiv
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (hG : IsStrictlyPositive (carrierCoefficientGram m hm Λ B)) :
    carrierCoefficientReducedDomain m hm Λ B hG ≃ₗᵢ[ℂ]
      (intersectionIn
        (carrierPhysicalAtomicSupport m hm Λ B).toSubmodule
        (carrierInverseFourierAtomicSupport m hm Λ B).toSubmodule).orthogonal :=
  coefficientReducedDomainEquiv
    (carrierInverseFourierPointMassSynthesis m hm Λ B)
    (carrierPointMassSynthesis m hm Λ B)
    (carrierInverseFourierCoefficientGram_strictlyPositive m hm Λ B hG)
    (carrierCoefficientGram_strictlyPositive_unfold m hm Λ B hG)

/-- The restricted original-endpoint operator is the genuine concrete
whitened matrix `G⁻¹ᐟ² S†𝓕S G⁻¹ᐟ²` on its exact reduced domain. -/
@[simp]
theorem carrierWhitenedReducedCross_apply
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (hG : IsStrictlyPositive (carrierCoefficientGram m hm Λ B))
    (c : carrierCoefficientReducedDomain m hm Λ B hG) :
    carrierWhitenedReducedCross m hm Λ B hG c =
      carrierWhitenedCoefficientCross m hm Λ B
        (c : CoefficientSpace ℤ) := by
  change whitenedCoefficientCross
      (carrierInverseFourierPointMassSynthesis m hm Λ B)
      (carrierPointMassSynthesis m hm Λ B) (c : CoefficientSpace ℤ) = _
  exact congrArg (fun A : CoefficientSpace ℤ →L[ℂ] CoefficientSpace ℤ ↦
    A (c : CoefficientSpace ℤ))
      (carrierInverseFourierWhitenedCoefficientCross_eq m hm Λ B)

/-- Carrier-specific intertwining with the genuine original reduced cross
from `X` to `Y = 𝓕⁻¹X`. -/
theorem carrierWhitenedReducedCross_intertwines
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (hG : IsStrictlyPositive (carrierCoefficientGram m hm Λ B))
    (c : carrierCoefficientReducedDomain m hm Λ B hG) :
    whitenedSynthesisEquivAtomicSupport
        (carrierInverseFourierPointMassSynthesis m hm Λ B)
        (carrierInverseFourierCoefficientGram_strictlyPositive m hm Λ B hG)
        (carrierWhitenedReducedCross m hm Λ B hG c) =
      reducedCross
        (carrierPhysicalAtomicSupport m hm Λ B).toSubmodule
        (carrierInverseFourierAtomicSupport m hm Λ B).toSubmodule
        (carrierCoefficientReducedDomainEquiv m hm Λ B hG c) := by
  exact whitenedReducedCross_intertwines
    (carrierInverseFourierPointMassSynthesis m hm Λ B)
    (carrierPointMassSynthesis m hm Λ B)
    (carrierInverseFourierCoefficientGram_strictlyPositive m hm Λ B hG)
    (carrierCoefficientGram_strictlyPositive_unfold m hm Λ B hG) c

/-- The genuine original carrier endpoint radius for
`X` and `Y = 𝓕⁻¹ X`. -/
def carrierReducedEndpointRadius
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ) : ℝ :=
  TwoProjectionEndpoint.reducedEndpointRadius
    (carrierPhysicalAtomicSupport m hm Λ B).toSubmodule
    (carrierInverseFourierAtomicSupport m hm Λ B).toSubmodule

/-- Exact carrier-specific endpoint identification. Its only additional
analytic input beyond Bessel synthesis is the visible strict positivity of
the genuine carrier Gram, i.e. the lower Riesz bound. -/
theorem carrierReducedEndpointRadius_eq_whitenedReducedCross_norm_sq
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (hG : IsStrictlyPositive (carrierCoefficientGram m hm Λ B)) :
    carrierReducedEndpointRadius m hm Λ B =
      ‖carrierWhitenedReducedCross m hm Λ B hG‖ ^ 2 := by
  exact rho_eq_whitenedReducedCross_norm_sq
    (carrierInverseFourierPointMassSynthesis m hm Λ B)
    (carrierPointMassSynthesis m hm Λ B)
    (carrierInverseFourierCoefficientGram_strictlyPositive m hm Λ B hG)
    (carrierCoefficientGram_strictlyPositive_unfold m hm Λ B hG)

/-- Square fixed-`ℓ²(ℤ)` realization of the genuine carrier reduced cross.
It extends the exact restricted operator by zero on the orthogonal complement
of the transported reduced domain. -/
def carrierSquareWhitenedReducedCross
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (hG : IsStrictlyPositive (carrierCoefficientGram m hm Λ B)) :
    CoefficientSpace ℤ →L[ℂ] CoefficientSpace ℤ :=
  squareWhitenedReducedCross
    (carrierInverseFourierPointMassSynthesis m hm Λ B)
    (carrierPointMassSynthesis m hm Λ B)
    (carrierInverseFourierCoefficientGram_strictlyPositive m hm Λ B hG)
    (carrierCoefficientGram_strictlyPositive_unfold m hm Λ B hG)

/-- The square carrier operator agrees with the genuine rectangular reduced
cross on its exact reduced coefficient domain. -/
@[simp]
theorem carrierSquareWhitenedReducedCross_apply_mem
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (hG : IsStrictlyPositive (carrierCoefficientGram m hm Λ B))
    (c : carrierCoefficientReducedDomain m hm Λ B hG) :
    carrierSquareWhitenedReducedCross m hm Λ B hG
        (c : CoefficientSpace ℤ) =
      carrierWhitenedReducedCross m hm Λ B hG c := by
  exact squareWhitenedReducedCross_apply_mem
    (carrierInverseFourierPointMassSynthesis m hm Λ B)
    (carrierPointMassSynthesis m hm Λ B)
    (carrierInverseFourierCoefficientGram_strictlyPositive m hm Λ B hG)
    (carrierCoefficientGram_strictlyPositive_unfold m hm Λ B hG) c

/-- Passing from the rectangular carrier reduced cross to its square
fixed-space realization preserves the operator norm exactly. -/
theorem carrierSquareWhitenedReducedCross_norm_eq
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (hG : IsStrictlyPositive (carrierCoefficientGram m hm Λ B)) :
    ‖carrierSquareWhitenedReducedCross m hm Λ B hG‖ =
      ‖carrierWhitenedReducedCross m hm Λ B hG‖ := by
  exact squareWhitenedReducedCross_norm_eq
    (carrierInverseFourierPointMassSynthesis m hm Λ B)
    (carrierPointMassSynthesis m hm Λ B)
    (carrierInverseFourierCoefficientGram_strictlyPositive m hm Λ B hG)
    (carrierCoefficientGram_strictlyPositive_unfold m hm Λ B hG)

/-- The square genuine carrier reduced cross is a contraction. -/
theorem carrierSquareWhitenedReducedCross_norm_le_one
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (hG : IsStrictlyPositive (carrierCoefficientGram m hm Λ B)) :
    ‖carrierSquareWhitenedReducedCross m hm Λ B hG‖ ≤ 1 := by
  exact squareWhitenedReducedCross_norm_le_one
    (carrierInverseFourierPointMassSynthesis m hm Λ B)
    (carrierPointMassSynthesis m hm Λ B)
    (carrierInverseFourierCoefficientGram_strictlyPositive m hm Λ B hG)
    (carrierCoefficientGram_strictlyPositive_unfold m hm Λ B hG)

/-- The square genuine carrier reduced cross is pointwise strictly
contractive on every unit vector, with no added analytic premise. -/
theorem carrierSquareWhitenedReducedCross_apply_norm_lt_one
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (hG : IsStrictlyPositive (carrierCoefficientGram m hm Λ B))
    (x : CoefficientSpace ℤ) (hx : ‖x‖ = 1) :
    ‖carrierSquareWhitenedReducedCross m hm Λ B hG x‖ < 1 := by
  exact squareWhitenedReducedCross_apply_norm_lt_one
    (carrierInverseFourierPointMassSynthesis m hm Λ B)
    (carrierPointMassSynthesis m hm Λ B)
    (carrierInverseFourierCoefficientGram_strictlyPositive m hm Λ B hG)
    (carrierCoefficientGram_strictlyPositive_unfold m hm Λ B hG) x hx

/-- Exact endpoint identification using the square fixed-coefficient-space
carrier operator expected by the sequence-level squeeze theorem. -/
theorem carrierReducedEndpointRadius_eq_squareWhitenedReducedCross_norm_sq
    (m : ℕ) (hm : 1 ≤ m) (Λ : TwoSidedCarrier)
    (B : CarrierHermiteBesselAnalysis m hm Λ)
    (hG : IsStrictlyPositive (carrierCoefficientGram m hm Λ B)) :
    carrierReducedEndpointRadius m hm Λ B =
      ‖carrierSquareWhitenedReducedCross m hm Λ B hG‖ ^ 2 := by
  exact rho_eq_squareWhitenedReducedCross_norm_sq
    (carrierInverseFourierPointMassSynthesis m hm Λ B)
    (carrierPointMassSynthesis m hm Λ B)
    (carrierInverseFourierCoefficientGram_strictlyPositive m hm Λ B hG)
    (carrierCoefficientGram_strictlyPositive_unfold m hm Λ B hG)

namespace TwoSidedCarrier.StrictSubcritical

/-- The square reduced carrier operator with all Bessel and strict-Gram data
instantiated unconditionally from strict subcriticality. -/
def squareCarrierWhitenedReducedCross
    {Λ : TwoSidedCarrier} (hΛ : Λ.StrictSubcritical)
    (m : ℕ) (hm : 1 ≤ m) :
    CoefficientSpace ℤ →L[ℂ] CoefficientSpace ℤ :=
  MeyerGeneralProblem.carrierSquareWhitenedReducedCross
    m hm Λ hΛ.carrierHermiteBesselAnalysis
    (hΛ.carrierCoefficientGram_strictlyPositive m hm)

/-- The genuine carrier endpoint radius with its analytic synthesis data
instantiated from strict subcriticality. -/
def carrierEndpointRadius
    {Λ : TwoSidedCarrier} (hΛ : Λ.StrictSubcritical)
    (m : ℕ) (hm : 1 ≤ m) : ℝ :=
  MeyerGeneralProblem.carrierReducedEndpointRadius
    m hm Λ hΛ.carrierHermiteBesselAnalysis

theorem squareCarrierWhitenedReducedCross_norm_le_one
    {Λ : TwoSidedCarrier} (hΛ : Λ.StrictSubcritical)
    (m : ℕ) (hm : 1 ≤ m) :
    ‖hΛ.squareCarrierWhitenedReducedCross m hm‖ ≤ 1 := by
  exact MeyerGeneralProblem.carrierSquareWhitenedReducedCross_norm_le_one
    m hm Λ hΛ.carrierHermiteBesselAnalysis
    (hΛ.carrierCoefficientGram_strictlyPositive m hm)

theorem squareCarrierWhitenedReducedCross_apply_norm_lt_one
    {Λ : TwoSidedCarrier} (hΛ : Λ.StrictSubcritical)
    (m : ℕ) (hm : 1 ≤ m) (x : CoefficientSpace ℤ) (hx : ‖x‖ = 1) :
    ‖hΛ.squareCarrierWhitenedReducedCross m hm x‖ < 1 := by
  exact MeyerGeneralProblem.carrierSquareWhitenedReducedCross_apply_norm_lt_one
    m hm Λ hΛ.carrierHermiteBesselAnalysis
    (hΛ.carrierCoefficientGram_strictlyPositive m hm) x hx

/-- Unconditional exact endpoint identification for every positive Hermite
order of a strict-subcritical carrier, now through a square operator on the
fixed Hilbert space `ℓ²(ℤ)`. -/
theorem carrierEndpointRadius_eq_squareCarrierWhitenedReducedCross_norm_sq
    {Λ : TwoSidedCarrier} (hΛ : Λ.StrictSubcritical)
    (m : ℕ) (hm : 1 ≤ m) :
    hΛ.carrierEndpointRadius m hm =
      ‖hΛ.squareCarrierWhitenedReducedCross m hm‖ ^ 2 := by
  exact MeyerGeneralProblem.carrierReducedEndpointRadius_eq_squareWhitenedReducedCross_norm_sq
    m hm Λ hΛ.carrierHermiteBesselAnalysis
    (hΛ.carrierCoefficientGram_strictlyPositive m hm)

end TwoSidedCarrier.StrictSubcritical

end

end MeyerGeneralProblem
