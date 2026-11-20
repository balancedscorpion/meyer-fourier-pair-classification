module

public import MeyerGeneralProblem.Sampling.CanonicalJointSampler
public import MeyerGeneralProblem.Sampling.KNSGraphOscillator
public import MeyerGeneralProblem.Trace.SamplingCokernel
public import MeyerGeneralProblem.Carrier.HermiteMeasureSupport
public import Mathlib.Topology.Algebra.Star.LinearMap

@[expose] public section

/-!
# The order-two graph/Hermite bridge

The order-two KNS graph space is continuously linearly equivalent to the
positive order-one Hermite scale.  Its inverse is the normalized Hermite
coefficient sequence of the genuine graph oscillator.

This module also records the exact conjugate-Riesz adapter between Hilbert
analysis and the bilinear positive/negative Hermite-scale pairing.  In
particular, any already-bounded bilinear sampler constructs its own genuine
Bessel analysis; no separate order-one grouped Bessel certificate is needed.
-/

namespace MeyerGeneralProblem.KNSGraphOscillator

noncomputable section

open MeasureTheory MeyerGeneralProblem
open scoped FourierTransform ComplexConjugate

/-- The existing order-two graph oscillator, bundled as a continuous linear map. -/
def oscillatorCLM : KNSGraphSpace 2 →L[ℂ] KNSL2 :=
  (Real.pi : ℂ) •
      ((FourierTransform.fourierInvCLM ℂ KNSL2).comp
        (KNSGraphSpace.frequencyWeight 2) +
       KNSGraphSpace.physicalWeight 2) +
    (1 / 2 : ℂ) • KNSGraphSpace.physical 2

@[simp] theorem oscillatorCLM_apply (v : KNSGraphSpace 2) :
    oscillatorCLM v = oscillator v := rfl

/-- The normalized Hermite-coordinate inverse of `graphExtension`. -/
def graphExtensionInverse : KNSGraphSpace 2 →L[ℂ] HermiteScale 1 :=
  (TauCeti.twoPiHermiteHilbertBasis ℂ).repr.toLinearIsometry.toContinuousLinearMap.comp
    oscillatorCLM

@[simp] theorem graphExtensionInverse_apply (v : KNSGraphSpace 2) :
    graphExtensionInverse v =
      (TauCeti.twoPiHermiteHilbertBasis ℂ).repr (oscillator v) := rfl

theorem graphExtensionInverse_leftInverse :
    Function.LeftInverse graphExtensionInverse graphExtension := by
  intro u
  apply lp.ext
  funext n
  rw [graphExtensionInverse_apply, oscillator_coeff,
    graphExtension_physical_coeff]

theorem graphExtensionInverse_rightInverse :
    Function.RightInverse graphExtensionInverse graphExtension := by
  intro v
  exact graphExtension_oscillator v

/-- The order-one Hermite scale and the genuine order-two KNS graph space are
continuously linearly equivalent. -/
def graphExtensionEquiv : HermiteScale 1 ≃L[ℂ] KNSGraphSpace 2 :=
  ContinuousLinearEquiv.equivOfInverse graphExtension graphExtensionInverse
    graphExtensionInverse_leftInverse graphExtensionInverse_rightInverse

@[simp] theorem graphExtensionEquiv_apply (u : HermiteScale 1) :
    graphExtensionEquiv u = graphExtension u := rfl

@[simp] theorem graphExtensionEquiv_symm_apply (v : KNSGraphSpace 2) :
    graphExtensionEquiv.symm v =
      (TauCeti.twoPiHermiteHilbertBasis ℂ).repr (oscillator v) := rfl

/-- On the dense Schwartz range, the equivalence is exactly the existing
graph embedding. -/
theorem graphExtensionEquiv_schwartz (f : SchwartzMap ℝ ℂ) :
    graphExtensionEquiv (schwartzToHermiteScale 1 f) =
      KNSGraphSpace.schwartzEmbedding 2 f := by
  exact graphExtension_schwartz f

end

end MeyerGeneralProblem.KNSGraphOscillator

namespace MeyerGeneralProblem

noncomputable section

open scoped ComplexConjugate

/-- The order-one conjugate-Riesz adapter.  The two anti-linear conjugations
turn Hilbert analysis into a complex-linear sampler for the bilinear
`H⁻¹`--`H¹` pairing. -/
def orderOneRieszConjugateAnalysis
    {I : Type*} {v : I → HermiteScale (-1)}
    (B : BesselAnalysis v) : HermiteScale 1 →L[ℂ] CoefficientSpace I :=
  (star (WithConv.toConv B.toContinuousLinearMap)).ofConv

@[simp] theorem orderOneRieszConjugateAnalysis_apply
    {I : Type*} {v : I → HermiteScale (-1)}
    (B : BesselAnalysis v) (u : HermiteScale 1) :
    orderOneRieszConjugateAnalysis B u =
      star (B.toContinuousLinearMap (star u)) := rfl

theorem orderOneRieszConjugateAnalysis_coord_pairing
    {I : Type*} {v : I → HermiteScale (-1)}
    (B : BesselAnalysis v) (u : HermiteScale 1) (i : I) :
    orderOneRieszConjugateAnalysis B u i =
      hermiteScalePairing (1 : ℤ) (v i) u := by
  rw [orderOneRieszConjugateAnalysis_apply]
  change star (B.toContinuousLinearMap (star u) i) = _
  rw [B.coefficient]
  calc
    star (inner ℂ (v i) (star u)) = inner ℂ (star u) (v i) :=
      inner_conj_symm (star u) (v i)
    _ = hermiteScalePairing (1 : ℤ) (v i) u :=
      (hermiteScalePairing_eq_inner_star_left 1 (v i) u).symm

/-- A bounded sampler with the exact bilinear pairing coordinates supplies
the corresponding genuine Bessel analysis by Riesz conjugation. -/
def BesselAnalysis.ofOrderOneBilinearSampling
    {I : Type*} (v : I → HermiteScale (-1))
    (T : HermiteScale 1 →L[ℂ] CoefficientSpace I)
    (hT : ∀ u i, T u i = hermiteScalePairing (1 : ℤ) (v i) u) :
    BesselAnalysis v where
  toContinuousLinearMap := (star (WithConv.toConv T)).ofConv
  coefficient := by
    intro x i
    change star (T (star x) i) = inner ℂ (v i) x
    rw [hT]
    have hp : hermiteScalePairing (1 : ℤ) (v i) (star x) =
        inner ℂ (star (star x)) (v i) := by
      simpa using hermiteScalePairing_eq_inner_star_left 1 (v i) (star x)
    rw [hp]
    simp only [star_star]
    exact inner_conj_symm (v i) x

/-- Applying the forward conjugate-Riesz adapter to the Bessel analysis
constructed from a bounded bilinear sampler recovers that sampler exactly. -/
theorem orderOneRieszConjugateAnalysis_ofOrderOneBilinearSampling
    {I : Type*} (v : I → HermiteScale (-1))
    (T : HermiteScale 1 →L[ℂ] CoefficientSpace I)
    (hT : ∀ u i, T u i = hermiteScalePairing (1 : ℤ) (v i) u) :
    orderOneRieszConjugateAnalysis
        (BesselAnalysis.ofOrderOneBilinearSampling v T hT) = T := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext i
  rw [orderOneRieszConjugateAnalysis_coord_pairing, hT]

/-- Paired conjugate-Riesz sampling, with the second sign inherited from the
existing synthesis-difference convention. -/
def orderOnePairedRieszSampling
    {I J : Type*} {v : I → HermiteScale (-1)} {w : J → HermiteScale (-1)}
    (A : BesselAnalysis v) (B : BesselAnalysis w) :
    HermiteScale 1 →L[ℂ] WithLp 2 (CoefficientSpace I × CoefficientSpace J) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (CoefficientSpace I)
      (CoefficientSpace J)).symm.toContinuousLinearMap.comp
    ((orderOneRieszConjugateAnalysis A).prod
      (-(orderOneRieszConjugateAnalysis B)))

@[simp] theorem orderOnePairedRieszSampling_apply
    {I J : Type*} {v : I → HermiteScale (-1)} {w : J → HermiteScale (-1)}
    (A : BesselAnalysis v) (B : BesselAnalysis w) (u : HermiteScale 1) :
    orderOnePairedRieszSampling A B u =
      WithLp.toLp 2
        (orderOneRieszConjugateAnalysis A u,
          -orderOneRieszConjugateAnalysis B u) := rfl

/-- Componentwise, paired conjugate-Riesz sampling is the conjugate of the
actual paired Hilbert sampling at the conjugated input. -/
theorem orderOnePairedRieszSampling_eq_conj_pairedTraceSampling
    {I J : Type*} {v : I → HermiteScale (-1)} {w : J → HermiteScale (-1)}
    (A : BesselAnalysis v) (B : BesselAnalysis w) (u : HermiteScale 1) :
    (orderOnePairedRieszSampling A B u).fst =
        star ((pairedTraceSampling A.synthesis B.synthesis (star u)).fst) ∧
      (orderOnePairedRieszSampling A B u).snd =
        star ((pairedTraceSampling A.synthesis B.synthesis (star u)).snd) := by
  rw [orderOnePairedRieszSampling_apply, pairedTraceSampling_apply]
  constructor
  · change orderOneRieszConjugateAnalysis A u =
      star (A.synthesis.adjoint (star u))
    rw [BesselAnalysis.synthesis, ContinuousLinearMap.adjoint_adjoint]
    rfl
  · change -orderOneRieszConjugateAnalysis B u =
      star (-B.synthesis.adjoint (star u))
    rw [BesselAnalysis.synthesis, ContinuousLinearMap.adjoint_adjoint]
    rfl

end

end MeyerGeneralProblem
