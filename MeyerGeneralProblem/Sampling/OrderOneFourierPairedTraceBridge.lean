module

public import MeyerGeneralProblem.Sampling.CanonicalOrderOnePhysicalTraceBridge

@[expose] public section

/-!
# Order-one Fourier paired-trace bridge

This module fixes the exact Fourier orientation between the order-two graph
sampler and the Hilbert adjoint of inverse-Fourier physical synthesis.  The
plain bilinear transpose carries inverse Fourier on both scales; the forward
test transform appears only after taking the Hilbert adjoint of the
inverse-Fourier synthesis.

The actual grouped physical atoms are proved coefficientwise real before the
double-conjugation Bessel analysis is identified with the original bilinear
sampler.  No carrier reflection, closed-range estimate, or cokernel dimension
claim is used here.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory
open scoped FourierTransform ComplexConjugate

/-- The inverse Hermite Fourier transform has the conjugate diagonal phase. -/
theorem hermiteFourier_symm_apply (m : ℤ)
    (u : HermiteScale m) (n : ℕ) :
    (hermiteFourier m).symm u n =
      starRingEnd ℂ (hermiteFourierPhase n) * u n := by
  have h := hermiteFourier_apply m ((hermiteFourier m).symm u) n
  rw [(hermiteFourier m).apply_symm_apply] at h
  calc
    (hermiteFourier m).symm u n =
        1 * (hermiteFourier m).symm u n := by rw [one_mul]
    _ = (starRingEnd ℂ (hermiteFourierPhase n) * hermiteFourierPhase n) *
        (hermiteFourier m).symm u n := by rw [conj_hermiteFourierPhase_mul]
    _ = starRingEnd ℂ (hermiteFourierPhase n) * u n := by
      rw [mul_assoc, h]

/-- Bilinear pairing transports forward Hermite Fourier on both dual scales. -/
theorem hermiteScalePairing_fourier
    (m : ℤ) (T : HermiteScale (-m)) (u : HermiteScale m) :
    hermiteScalePairing m (hermiteFourier (-m) T) u =
      hermiteScalePairing m T (hermiteFourier m u) := by
  unfold hermiteScalePairing
  apply tsum_congr
  intro n
  rw [hermiteFourier_apply, hermiteFourier_apply]
  ring

/-- Bilinear pairing transports inverse Hermite Fourier on both dual scales. -/
theorem hermiteScalePairing_fourier_symm
    (m : ℤ) (T : HermiteScale (-m)) (u : HermiteScale m) :
    hermiteScalePairing m ((hermiteFourier (-m)).symm T) u =
      hermiteScalePairing m T ((hermiteFourier m).symm u) := by
  unfold hermiteScalePairing
  apply tsum_congr
  intro n
  rw [hermiteFourier_symm_apply, hermiteFourier_symm_apply]
  ring

/-- The inverse/forward bilinear composition cancels exactly. -/
theorem hermiteScalePairing_fourier_symm_fourier
    (m : ℤ) (T : HermiteScale (-m)) (u : HermiteScale m) :
    hermiteScalePairing m ((hermiteFourier (-m)).symm T)
        (hermiteFourier m u) =
      hermiteScalePairing m T u := by
  rw [hermiteScalePairing_fourier_symm,
    (hermiteFourier m).symm_apply_apply]

/-- Positive Hermite coordinates intertwine the genuine Schwartz Fourier
transform without conjugation or reflection. -/
theorem schwartzToHermiteScale_fourier
    (m : ℕ) (f : SchwartzMap ℝ ℂ) :
    hermiteFourier (m : ℤ) (schwartzToHermiteScale m f) =
      schwartzToHermiteScale m (FourierTransform.fourier f) := by
  apply lp.ext
  funext n
  rw [hermiteFourier_apply, schwartzToHermiteScale_apply,
    schwartzToHermiteScale_apply]
  change hermiteFourierPhase n *
      ((hermiteScaleWeight (m : ℤ) n : ℂ) * schwartzHermiteCoefficients f n) =
    (hermiteScaleWeight (m : ℤ) n : ℂ) *
      schwartzHermiteCoefficients (FourierTransform.fourier f) n
  rw [schwartzHermiteCoefficients_fourier]
  ring

namespace KNSGraphOscillator

/-- The graph/Hermite equivalence intertwines forward Hermite Fourier with
the genuine order-two graph Fourier transform. -/
theorem graphExtensionEquiv_fourier (u : HermiteScale 1) :
    graphExtensionEquiv (hermiteFourier 1 u) =
      KNSGraphSpace.fourier 2 (graphExtensionEquiv u) := by
  apply KNSGraphSpace.physical_injective 2
  apply (TauCeti.twoPiHermiteHilbertBasis ℂ).repr.injective
  apply lp.ext
  funext n
  rw [graphExtensionEquiv_apply, graphExtensionEquiv_apply,
    KNSGraphSpace.physical_fourier,
    TauCeti.repr_fourier_twoPiHermiteHilbertBasis]
  have hleft := graphExtension_physical_coeff (hermiteFourier 1 u) n
  have hright := graphExtension_physical_coeff u n
  rw [hermiteFourier_apply] at hleft
  have hn : ((n : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (by positivity : (n : ℝ) + 1 ≠ 0)
  apply mul_left_cancel₀ hn
  calc
    ((n : ℂ) + 1) *
        (TauCeti.twoPiHermiteHilbertBasis ℂ).repr
          (KNSGraphSpace.physical 2
            (graphExtension (hermiteFourier 1 u))) n =
        hermiteFourierPhase n * u n := hleft
    _ = hermiteFourierPhase n * (((n : ℂ) + 1) *
        (TauCeti.twoPiHermiteHilbertBasis ℂ).repr
          (KNSGraphSpace.physical 2 (graphExtension u)) n) := by rw [hright]
    _ = ((n : ℂ) + 1) * (hermiteFourierPhase n *
        (TauCeti.twoPiHermiteHilbertBasis ℂ).repr
          (KNSGraphSpace.physical 2 (graphExtension u)) n) := by ring

end KNSGraphOscillator

/-- Genuine negative-scale Dirac vectors have real normalized coordinates. -/
theorem star_hermitePointMass
    (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    star (hermitePointMass m hm x) = hermitePointMass m hm x := by
  apply lp.ext
  funext n
  change starRingEnd ℂ (hermiteDiracCoefficients m x n) =
    hermiteDiracCoefficients m x n
  rw [hermiteDiracCoefficients_eq, map_mul]
  rw [normalizedHermiteSchwartz_eq_twoPi,
    TauCeti.twoPiHermiteSchwartzMap_apply]
  simp

/-- A finite Newton atom over real nodes is fixed by coefficientwise
conjugation whenever its constituent vectors are fixed. -/
theorem star_groupedFiniteAtom_real
    {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    [StarAddMonoid V] [StarModule ℂ V]
    (nodes : Fin n → ℝ) (v : Fin n → V)
    (hv : ∀ i, star (v i) = v i) (j : Fin n) :
    star (groupedFiniteAtom (fun i => (nodes i : ℂ)) v j) =
      groupedFiniteAtom (fun i => (nodes i : ℂ)) v j := by
  unfold groupedFiniteAtom
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [star_smul, groupedNewtonWeight_ofReal]
  simp [hv]

/-- Every normalized grouped atom over an actual real carrier is fixed by
coefficientwise conjugation. -/
theorem OrderedCarrierGrouping.star_atom
    {S : LocallyFiniteCarrier} {κ : Type*}
    (G : OrderedCarrierGrouping S κ)
    (m : ℕ) (hm : 1 ≤ m) (x : G.Index) :
    star (G.atom m hm x) = G.atom m hm x := by
  rcases x with ⟨C, j⟩
  rw [OrderedCarrierGrouping.atom, OrderedCarrierGrouping.rawAtom]
  have hnodes : G.nodes C = fun i => (G.realNodes C i : ℂ) := rfl
  rw [hnodes, star_smul]
  have hraw := star_groupedFiniteAtom_real
    (G.realNodes C) (fun i => hermitePointMass m hm (G.point C i))
    (fun i => star_hermitePointMass m hm (G.point C i)) j
  rw [hraw]
  simp

/-- On a coefficientwise-real negative-scale vector, Hilbert analysis equals
the bilinear Hermite pairing. -/
theorem inner_eq_hermiteScalePairing_of_star_eq
    (m : ℕ) (T : HermiteScale (-(m : ℤ)))
    (hT : star T = T) (u : HermiteScale (m : ℤ)) :
    inner ℂ T u = hermiteScalePairing (m : ℤ) T u := by
  rw [lp.inner_eq_tsum]
  unfold hermiteScalePairing
  apply tsum_congr
  intro n
  simp only [RCLike.inner_apply]
  have hn := congrArg (fun z : HermiteScale (-(m : ℤ)) => z n) hT
  change starRingEnd ℂ (T n) = T n at hn
  rw [hn]
  ring

/-- Inverse-Fourier synthesis is constructed by giving its exact forward
Fourier Hilbert analysis. -/
def BesselAnalysis.inverseFourier
    {I : Type*} {v : I → HermiteScale (-1)}
    (A : BesselAnalysis v) :
    BesselAnalysis (fun i => (hermiteFourier (-1)).symm (v i)) where
  toContinuousLinearMap := A.toContinuousLinearMap.comp
    (hermiteFourier (-1)).toContinuousLinearEquiv.toContinuousLinearMap
  coefficient := by
    intro u i
    rw [ContinuousLinearMap.comp_apply, A.coefficient]
    simpa using ((hermiteFourier (-1)).inner_map_map
      ((hermiteFourier (-1)).symm (v i)) u)

@[simp] theorem BesselAnalysis.inverseFourier_apply
    {I : Type*} {v : I → HermiteScale (-1)}
    (A : BesselAnalysis v) (u : HermiteScale (-1)) :
    (A.inverseFourier).toContinuousLinearMap u =
      A.toContinuousLinearMap (hermiteFourier (-1) u) := rfl

/-- The synthesis of the transported Bessel family is exactly inverse
Hermite Fourier after physical synthesis. -/
theorem BesselAnalysis.inverseFourier_synthesis
    {I : Type*} {v : I → HermiteScale (-1)}
    (A : BesselAnalysis v) :
    A.inverseFourier.synthesis =
      (hermiteFourier (-1)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        A.synthesis := by
  rw [BesselAnalysis.synthesis, BesselAnalysis.synthesis,
    BesselAnalysis.inverseFourier, ContinuousLinearMap.adjoint_comp,
    LinearIsometryEquiv.adjoint_eq_symm]

namespace BoundedClusterOrder

variable (S : LocallyFiniteCarrier) {d : ℝ} {q : ℕ}
  (ho : BoundedClusterOrder S.signedSquareImage d q)

/-- The order-one Fourier graph sampler is the physical Hermite sampler on
the forward-Fourier test vector. -/
theorem canonicalOrderOneFourierSampler_eq
    (hd : 0 < d) (hq : q + 1 ≤ 2) (u : HermiteScale 1) :
    ho.canonicalFourierScalarSamplerBounded hd hq
        (ho.canonicalActualAnchor S)
        (KNSGraphOscillator.graphExtensionEquiv u) =
      ho.canonicalOrderOnePhysicalHermiteSampler S hd hq
        (hermiteFourier 1 u) := by
  change ho.canonicalPhysicalScalarSamplerBounded hd hq
      (ho.canonicalActualAnchor S)
      (KNSGraphSpace.fourierEquiv 2
        (KNSGraphOscillator.graphExtensionEquiv u)) = _
  change ho.canonicalPhysicalScalarSamplerBounded hd hq
      (ho.canonicalActualAnchor S)
      (KNSGraphSpace.fourier 2
        (KNSGraphOscillator.graphExtensionEquiv u)) = _
  rw [← KNSGraphOscillator.graphExtensionEquiv_fourier]
  rfl

/-- The exact scaled physical atom is coefficientwise real. -/
theorem star_canonicalOrderOnePhysicalAtom
    (x : ho.signedGrouping.Index) :
    star (ho.canonicalOrderOnePhysicalAtom S x) =
      ho.canonicalOrderOnePhysicalAtom S x := by
  unfold canonicalOrderOnePhysicalAtom
  rw [star_smul, OrderedCarrierGrouping.star_atom]
  simp

/-- Hilbert analysis of the derived physical Bessel family is the original
bilinear order-one sampler, after atom reality is proved. -/
theorem canonicalOrderOnePhysicalBesselAnalysis_eq_sampler
    (hd : 0 < d) (hq : q + 1 ≤ 2) :
    (ho.canonicalOrderOnePhysicalBesselAnalysis S hd hq).toContinuousLinearMap =
      ho.canonicalOrderOnePhysicalHermiteSampler S hd hq := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext x
  rw [(ho.canonicalOrderOnePhysicalBesselAnalysis S hd hq).coefficient,
    ho.canonicalOrderOnePhysicalHermiteSampler_coord S hd hq]
  exact inner_eq_hermiteScalePairing_of_star_eq 1
    (ho.canonicalOrderOnePhysicalAtom S x)
    (ho.star_canonicalOrderOnePhysicalAtom S x) u

/-- The adjoint of physical synthesis is exactly the physical graph sampler. -/
theorem canonicalOrderOnePhysicalSynthesis_adjoint
    (hd : 0 < d) (hq : q + 1 ≤ 2) :
    (ho.canonicalOrderOnePhysicalBesselAnalysis S hd hq).synthesis.adjoint =
      ho.canonicalOrderOnePhysicalHermiteSampler S hd hq := by
  rw [BesselAnalysis.synthesis, ContinuousLinearMap.adjoint_adjoint,
    ho.canonicalOrderOnePhysicalBesselAnalysis_eq_sampler S hd hq]

/-- The genuine Bessel family obtained by inverse Fourier transport of the
actual physical atoms. -/
def canonicalOrderOneInverseFourierBesselAnalysis
    (hd : 0 < d) (hq : q + 1 ≤ 2) :
    BesselAnalysis (fun x => (hermiteFourier (-1)).symm
      (ho.canonicalOrderOnePhysicalAtom S x)) :=
  (ho.canonicalOrderOnePhysicalBesselAnalysis S hd hq).inverseFourier

/-- Its synthesis is exactly inverse Fourier after physical synthesis. -/
theorem canonicalOrderOneInverseFourierBesselAnalysis_synthesis
    (hd : 0 < d) (hq : q + 1 ≤ 2) :
    (ho.canonicalOrderOneInverseFourierBesselAnalysis S hd hq).synthesis =
      (hermiteFourier (-1)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (ho.canonicalOrderOnePhysicalBesselAnalysis S hd hq).synthesis := by
  exact BesselAnalysis.inverseFourier_synthesis _

/-- Hilbert analysis of inverse-Fourier physical synthesis is exactly the
existing forward-Fourier graph sampler. -/
theorem canonicalOrderOneInverseFourierBesselAnalysis_eq_graphSampler
    (hd : 0 < d) (hq : q + 1 ≤ 2) :
    (ho.canonicalOrderOneInverseFourierBesselAnalysis S hd hq).toContinuousLinearMap =
      (ho.canonicalFourierScalarSamplerBounded hd hq
          (ho.canonicalActualAnchor S)).comp
        KNSGraphOscillator.graphExtensionEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro u
  change
    ((ho.canonicalOrderOnePhysicalBesselAnalysis S hd hq).inverseFourier).toContinuousLinearMap
      u = _
  rw [BesselAnalysis.inverseFourier_apply,
    ho.canonicalOrderOnePhysicalBesselAnalysis_eq_sampler S hd hq]
  exact (ho.canonicalOrderOneFourierSampler_eq S hd hq u).symm

/-- The paired Hilbert sampler has exactly the physical row and the negative
forward-Fourier graph row, with no residual conjugation. -/
theorem pairedTraceSampling_exact_graphSamplers
    (hd : 0 < d) (hq : q + 1 ≤ 2) (u : HermiteScale 1) :
    pairedTraceSampling
        (ho.canonicalOrderOnePhysicalBesselAnalysis S hd hq).synthesis
        (ho.canonicalOrderOneInverseFourierBesselAnalysis S hd hq).synthesis u =
      WithLp.toLp 2
        (ho.canonicalOrderOnePhysicalHermiteSampler S hd hq u,
          -((ho.canonicalFourierScalarSamplerBounded hd hq
              (ho.canonicalActualAnchor S)).comp
            KNSGraphOscillator.graphExtensionEquiv.toContinuousLinearMap) u) := by
  rw [pairedTraceSampling_apply, BesselAnalysis.synthesis,
    BesselAnalysis.synthesis, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.adjoint_adjoint,
    ho.canonicalOrderOnePhysicalBesselAnalysis_eq_sampler S hd hq,
    ho.canonicalOrderOneInverseFourierBesselAnalysis_eq_graphSampler S hd hq]

end BoundedClusterOrder

/-! The first Hermite mode is an executable normalization regression. -/

@[simp] theorem hermiteFourierPhase_one :
    hermiteFourierPhase 1 = -Complex.I := by
  simp [hermiteFourierPhase]

theorem hermiteFourier_one_apply_one (u : HermiteScale 1) :
    hermiteFourier 1 u 1 = -Complex.I * u 1 := by
  rw [hermiteFourier_apply, hermiteFourierPhase_one]

theorem hermiteFourier_neg_one_symm_apply_one (T : HermiteScale (-1)) :
    (hermiteFourier (-1)).symm T 1 = Complex.I * T 1 := by
  rw [hermiteFourier_symm_apply, hermiteFourierPhase_one]
  simp

end


end MeyerGeneralProblem
