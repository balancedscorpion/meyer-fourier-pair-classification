module

public import MeyerGeneralProblem.Sampling.CanonicalTraceNormalization
public import MeyerGeneralProblem.Sampling.OrderTwoGraphHermiteBridge

@[expose] public section

/-!
# Canonical order-one physical trace bridge

The bounded order-two physical graph sampler, transported across the exact
graph/Hermite equivalence, is the bilinear analysis operator of the genuinely
diagonally normalized order-one grouped atoms.  Equality is first proved on
the dense Schwartz range and then extended to every positive order-one
Hermite vector by continuity.

This produces the required order-one Bessel analysis from the bounded sampler
itself.  It does not use the high-order `actualGroupedBesselAnalysis` API and
makes no closed-range, cokernel, or paired-range assertion.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace BoundedClusterOrder

variable (S : LocallyFiniteCarrier) {d : ℝ} {q : ℕ}
  (ho : BoundedClusterOrder S.signedSquareImage d q)

/-- At graph order two, the sampler's regularity hypothesis explicitly
restricts the canonical cluster order to at most one. -/
theorem canonicalOrderOne_clusterOrder_le_one (hq : q + 1 ≤ 2) : q ≤ 1 := by
  omega

/-- The actual order-one grouped atom multiplied by the exact diagonal factor
relating Hermite trace normalization to canonical graph normalization. -/
def canonicalOrderOnePhysicalAtom
    (x : ho.signedGrouping.Index) : HermiteScale (-1) :=
  (ho.canonicalToActualTraceFactor S 1 2 (by omega)
      (ho.canonicalActualAnchor S) x.1 : ℂ) •
    ho.signedGrouping.atom 1 (by omega) x

/-- The bounded physical scalar graph sampler transported from the genuine
order-two graph space to the positive order-one Hermite scale. -/
def canonicalOrderOnePhysicalHermiteSampler
    (hd : 0 < d) (hq : q + 1 ≤ 2) :
    HermiteScale 1 →L[ℂ] CoefficientSpace ho.signedGrouping.Index :=
  (ho.canonicalPhysicalScalarSamplerBounded hd hq
      (ho.canonicalActualAnchor S)).comp
    KNSGraphOscillator.graphExtensionEquiv.toContinuousLinearMap

/-- On embedded Schwartz functions, each transported sampler coordinate is
the bilinear action of the exact diagonally normalized actual atom. -/
theorem canonicalOrderOnePhysicalHermiteSampler_schwartz_coord
    (hd : 0 < d) (hq : q + 1 ≤ 2)
    (f : SchwartzMap ℝ ℂ) (x : ho.signedGrouping.Index) :
    ho.canonicalOrderOnePhysicalHermiteSampler S hd hq
        (schwartzToHermiteScale 1 f) x =
      hermiteScalePairing (1 : ℤ)
        (ho.canonicalOrderOnePhysicalAtom S x)
        (schwartzToHermiteScale 1 f) := by
  rcases x with ⟨C, j⟩
  change ho.canonicalGraphDataCoefficientEquiv
      (ho.canonicalPhysicalSamplerBounded S hd hq
        (ho.canonicalActualAnchor S)
        (KNSGraphOscillator.graphExtensionEquiv
          (schwartzToHermiteScale 1 f))) ⟨C, j⟩ = _
  rw [KNSGraphOscillator.graphExtensionEquiv_schwartz]
  rw [ho.canonicalPhysicalSamplerBounded_schwartzEmbedding_eq_actualAtom
    S 1 2 (by omega) (by omega) hd hq (ho.canonicalActualAnchor S) C j f]
  rw [hermiteScaleDistribution_apply]
  change
    (ho.canonicalToActualTraceFactor S 1 2 (by omega)
      (ho.canonicalActualAnchor S) C : ℂ) *
        hermiteScalePairing (1 : ℤ)
          (ho.signedGrouping.atom 1 (by omega) ⟨C, j⟩)
          (schwartzToHermiteScale 1 f) =
      hermiteScalePairing (1 : ℤ)
        ((ho.canonicalToActualTraceFactor S 1 2 (by omega)
          (ho.canonicalActualAnchor S) C : ℂ) •
            ho.signedGrouping.atom 1 (by omega) ⟨C, j⟩)
        (schwartzToHermiteScale 1 f)
  have hplain : hermiteScalePairing (1 : ℤ)
      (ho.signedGrouping.atom 1 (by omega) ⟨C, j⟩)
      (schwartzToHermiteScale 1 f) =
      hermiteScalePairingRightCLM 1
        (schwartzToHermiteScale 1 f)
        (ho.signedGrouping.atom 1 (by omega) ⟨C, j⟩) := by
    simp
  have hscaled : hermiteScalePairing (1 : ℤ)
      ((ho.canonicalToActualTraceFactor S 1 2 (by omega)
        (ho.canonicalActualAnchor S) C : ℂ) •
          ho.signedGrouping.atom 1 (by omega) ⟨C, j⟩)
      (schwartzToHermiteScale 1 f) =
      hermiteScalePairingRightCLM 1
        (schwartzToHermiteScale 1 f)
        ((ho.canonicalToActualTraceFactor S 1 2 (by omega)
          (ho.canonicalActualAnchor S) C : ℂ) •
            ho.signedGrouping.atom 1 (by omega) ⟨C, j⟩) := by
    simpa using (hermiteScalePairingRightCLM_apply 1
      (schwartzToHermiteScale 1 f)
      ((ho.canonicalToActualTraceFactor S 1 2 (by omega)
        (ho.canonicalActualAnchor S) C : ℂ) •
          ho.signedGrouping.atom 1 (by omega) ⟨C, j⟩)).symm
  rw [hplain, hscaled, map_smul]
  rfl

/-- The Schwartz coordinate identity extends to every positive order-one
Hermite vector; no pointwise or almost-everywhere transfer is used. -/
theorem canonicalOrderOnePhysicalHermiteSampler_coord
    (hd : 0 < d) (hq : q + 1 ≤ 2)
    (u : HermiteScale 1) (x : ho.signedGrouping.Index) :
    ho.canonicalOrderOnePhysicalHermiteSampler S hd hq u x =
      hermiteScalePairing (1 : ℤ)
        (ho.canonicalOrderOnePhysicalAtom S x) u := by
  have huPairing : hermiteScalePairing (1 : ℤ)
      (ho.canonicalOrderOnePhysicalAtom S x) u =
      hermiteScalePairingLeftCLM 1
        (ho.canonicalOrderOnePhysicalAtom S x) u := by
    simp
  rw [huPairing]
  let P : HermiteScale 1 → Prop := fun z =>
    ho.canonicalOrderOnePhysicalHermiteSampler S hd hq z x =
      hermiteScalePairingLeftCLM 1
        (ho.canonicalOrderOnePhysicalAtom S x) z
  change P u
  apply DenseRange.induction_on
      (p := P) (schwartzToHermiteScale_denseRange 1) u
  · exact isClosed_eq
      ((lp.evalCLM ℂ (fun _ : ho.signedGrouping.Index => ℂ) 2 x).continuous.comp
        (ho.canonicalOrderOnePhysicalHermiteSampler S hd hq).continuous)
      (hermiteScalePairingLeftCLM 1
        (ho.canonicalOrderOnePhysicalAtom S x)).continuous
  · intro f
    have hs :=
      ho.canonicalOrderOnePhysicalHermiteSampler_schwartz_coord S hd hq f x
    have hfPairing : hermiteScalePairing (1 : ℤ)
        (ho.canonicalOrderOnePhysicalAtom S x)
        (schwartzToHermiteScale 1 f) =
        hermiteScalePairingLeftCLM 1
          (ho.canonicalOrderOnePhysicalAtom S x)
          (schwartzToHermiteScale 1 f) := by
      simp
    rw [hfPairing] at hs
    exact hs

/-- The sampler bound itself supplies genuine Bessel data for the exact
diagonally normalized order-one actual atoms. -/
def canonicalOrderOnePhysicalBesselAnalysis
    (hd : 0 < d) (hq : q + 1 ≤ 2) :
    BesselAnalysis (ho.canonicalOrderOnePhysicalAtom S) :=
  BesselAnalysis.ofOrderOneBilinearSampling
    (ho.canonicalOrderOnePhysicalAtom S)
    (ho.canonicalOrderOnePhysicalHermiteSampler S hd hq)
    (ho.canonicalOrderOnePhysicalHermiteSampler_coord S hd hq)

/-- Conjugate-Riesz analysis of the derived Bessel family recovers exactly
the graph-composed physical sampler. -/
theorem orderOneRieszConjugateAnalysis_canonicalOrderOnePhysicalBesselAnalysis
    (hd : 0 < d) (hq : q + 1 ≤ 2) :
    orderOneRieszConjugateAnalysis
        (ho.canonicalOrderOnePhysicalBesselAnalysis S hd hq) =
      ho.canonicalOrderOnePhysicalHermiteSampler S hd hq := by
  exact orderOneRieszConjugateAnalysis_ofOrderOneBilinearSampling
    (ho.canonicalOrderOnePhysicalAtom S)
    (ho.canonicalOrderOnePhysicalHermiteSampler S hd hq)
    (ho.canonicalOrderOnePhysicalHermiteSampler_coord S hd hq)

end BoundedClusterOrder

end

end MeyerGeneralProblem
