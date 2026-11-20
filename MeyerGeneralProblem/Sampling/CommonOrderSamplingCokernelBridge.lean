module

public import MeyerGeneralProblem.Sampling.CanonicalJointSampler
public import MeyerGeneralProblem.Sampling.SignedSumCoefficientEquiv
public import MeyerGeneralProblem.Sampling.CanonicalTraceNormalization
public import MeyerGeneralProblem.Sampling.OrderOneFourierPairedTraceBridge
public import MeyerGeneralProblem.Carrier.GroupedSynthesisInjectivity
public import MeyerGeneralProblem.Trace.SamplingCokernel

@[expose] public section

/-!
# Common-order sampling cokernel bridge

At every positive Hermite order with available grouped synthesis, this module
maps the genuine orthogonal cokernel of the same-order canonical KNS graph
sampler injectively into the intrinsic fixed-order Meyer layer. The proof
uses conjugate Schwartz tests and the canonical trace normalization, avoiding
any unproved all-orders graph/Hermite equivalence.

This is a terminal cokernel-to-endpoint bridge only. It does not construct
the bounded-cluster deformation, prove upper semi-Fredholmness along that
path, or establish infinite deficiency at its seed; those remain the analytic
U6 obligations.
-/

open MeasureTheory
open scoped FourierTransform

noncomputable section

attribute [local instance] Classical.propDecidable

namespace MeyerGeneralProblem

/-- Complex conjugation of a Schwartz function, retained as a Schwartz map. -/
def complexConjugateSchwartz (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap f

@[simp] theorem complexConjugateSchwartz_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    complexConjugateSchwartz f x = starRingEnd ℂ (f x) := by
  simp [complexConjugateSchwartz]

theorem fourier_complexConjugateSchwartz (f : SchwartzMap ℝ ℂ) :
    FourierTransform.fourier (complexConjugateSchwartz f) =
      complexConjugateSchwartz (FourierTransform.fourierInv f) := by
  ext x
  rw [SchwartzMap.fourier_coe]
  simp only [complexConjugateSchwartz_apply, SchwartzMap.fourierInv_coe]
  rw [Real.fourier_eq, Real.fourierInv_eq, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [complexConjugateSchwartz_apply]
  change ((Real.fourierChar (-inner ℝ t x) : Circle) : ℂ) * starRingEnd ℂ (f t) =
    starRingEnd ℂ (((Real.fourierChar (inner ℝ t x) : Circle) : ℂ) * f t)
  rw [map_mul, Circle.starRingEnd_addChar]

theorem groupedRealDividedDifference_complexConjugate
    {n : ℕ} (nodes : Fin n → ℝ) (j : Fin n) (f : SchwartzMap ℝ ℂ) :
    groupedRealDividedDifference nodes j (complexConjugateSchwartz f) =
      starRingEnd ℂ (groupedRealDividedDifference nodes j f) := by
  simp only [groupedRealDividedDifference, complexConjugateSchwartz_apply, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.conj_ofReal]

namespace BoundedClusterOrder

variable {S : LocallyFiniteCarrier} {d : ℝ} {q : ℕ}
  (ho : BoundedClusterOrder S.signedSquareImage d q)

theorem physicalSignedSquarePullbackMap_complexConjugate
    (f : SchwartzMap ℝ ℂ) (s : ℝ) :
    S.physicalSignedSquarePullbackMap (complexConjugateSchwartz f) s =
      starRingEnd ℂ (S.physicalSignedSquarePullbackMap f s) := by
  change (if hs : s ∈ S.signedSquareImage.subtype then
      complexConjugateSchwartz f (S.signedSquareSubtypeEquiv.symm ⟨s, hs⟩) else 0) =
    starRingEnd ℂ (if hs : s ∈ S.signedSquareImage.subtype then
      f (S.signedSquareSubtypeEquiv.symm ⟨s, hs⟩) else 0)
  by_cases hs : s ∈ S.signedSquareImage.subtype <;> simp [hs]

theorem canonicalPrefixData_complexConjugate
    (f : SchwartzMap ℝ ℂ)
    (C : CanonicalClusterIndex S.signedSquareImage d)
    (j : Fin (ho.clusterSize C)) :
    ho.canonicalPrefixData
        (S.physicalSignedSquarePullbackMap (complexConjugateSchwartz f)) C j =
      starRingEnd ℂ (ho.canonicalPrefixData
        (S.physicalSignedSquarePullbackMap f) C j) := by
  rw [canonicalPrefixData, analyticDividedDifference_eq_dividedDifferences
    (ho.realClusterNode C) (ho.realClusterNode_strictMono C).injective,
    canonicalPrefixData, analyticDividedDifference_eq_dividedDifferences
    (ho.realClusterNode C) (ho.realClusterNode_strictMono C).injective,
    dividedDifferences_eq_groupedNewtonWeights,
    dividedDifferences_eq_groupedNewtonWeights]
  simp only [map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [physicalSignedSquarePullbackMap_complexConjugate]
  rw [groupedNewtonWeight_ofReal]
  simp

theorem canonicalPhysicalScalarSamplerBounded_complexConjugate
    {k : ℕ} (hk : 2 ≤ k) (hd : 0 < d) (hq : q + 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C)) (f : SchwartzMap ℝ ℂ) :
    ho.canonicalPhysicalScalarSamplerBounded hd hq anchor
        (KNSGraphSpace.schwartzEmbedding k (complexConjugateSchwartz f)) =
      star (ho.canonicalPhysicalScalarSamplerBounded hd hq anchor
        (KNSGraphSpace.schwartzEmbedding k f)) := by
  apply lp.ext
  funext x
  change ho.canonicalPhysicalScalarSamplerBounded hd hq anchor
      (KNSGraphSpace.schwartzEmbedding k (complexConjugateSchwartz f)) x =
    starRingEnd ℂ (ho.canonicalPhysicalScalarSamplerBounded hd hq anchor
      (KNSGraphSpace.schwartzEmbedding k f) x)
  rw [ho.canonicalPhysicalScalarSamplerBounded_apply,
    ho.canonicalPhysicalScalarSamplerBounded_apply]
  rcases x with ⟨C, j⟩
  let j' : Fin (ho.clusterSize C) :=
    Fin.cast (show ho.signedGrouping.size C = ho.clusterSize C from rfl) j
  change (ho.canonicalGraphWeight k anchor C : ℂ) *
      ho.canonicalPrefixData
        (S.physicalSignedSquarePullbackMap
          (KNSGraphSpace.representative k
            (KNSGraphSpace.schwartzEmbedding k (complexConjugateSchwartz f)))) C j' =
    starRingEnd ℂ ((ho.canonicalGraphWeight k anchor C : ℂ) *
      ho.canonicalPrefixData
        (S.physicalSignedSquarePullbackMap
          (KNSGraphSpace.representative k
            (KNSGraphSpace.schwartzEmbedding k f))) C j')
  rw [KNSGraphSpace.representative_schwartzEmbedding hk,
    KNSGraphSpace.representative_schwartzEmbedding hk,
    ho.canonicalPrefixData_complexConjugate]
  change (ho.canonicalGraphWeight k anchor C : ℂ) *
      starRingEnd ℂ
        (ho.canonicalPrefixData (S.physicalSignedSquarePullbackMap ⇑f) C j) =
    starRingEnd ℂ ((ho.canonicalGraphWeight k anchor C : ℂ) *
      ho.canonicalPrefixData (S.physicalSignedSquarePullbackMap ⇑f) C j)
  rw [map_mul, Complex.conj_ofReal]

theorem fourier_schwartzEmbedding
    {k : ℕ} (f : SchwartzMap ℝ ℂ) :
    KNSGraphSpace.fourier k (KNSGraphSpace.schwartzEmbedding k f) =
      KNSGraphSpace.schwartzEmbedding k (FourierTransform.fourier f) := by
  apply KNSGraphSpace.physical_injective k
  rw [KNSGraphSpace.physical_fourier,
    KNSGraphSpace.physical_schwartzEmbedding,
    KNSGraphSpace.physical_schwartzEmbedding,
    SchwartzMap.toLp_fourier_eq]

theorem canonicalFourierScalarSamplerBounded_complexConjugate
    {k : ℕ} (hk : 2 ≤ k) (hd : 0 < d) (hq : q + 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C)) (f : SchwartzMap ℝ ℂ) :
    ho.canonicalFourierScalarSamplerBounded hd hq anchor
        (KNSGraphSpace.schwartzEmbedding k (complexConjugateSchwartz f)) =
      star (ho.canonicalPhysicalScalarSamplerBounded hd hq anchor
        (KNSGraphSpace.schwartzEmbedding k (FourierTransform.fourierInv f))) := by
  apply lp.ext
  funext x
  change ho.canonicalFourierScalarSamplerBounded hd hq anchor
      (KNSGraphSpace.schwartzEmbedding k (complexConjugateSchwartz f)) x =
    starRingEnd ℂ (ho.canonicalPhysicalScalarSamplerBounded hd hq anchor
      (KNSGraphSpace.schwartzEmbedding k (FourierTransform.fourierInv f)) x)
  rw [ho.canonicalFourierScalarSamplerBounded_apply,
    ho.canonicalPhysicalScalarSamplerBounded_apply]
  rcases x with ⟨C, j⟩
  let j' : Fin (ho.clusterSize C) :=
    Fin.cast (show ho.signedGrouping.size C = ho.clusterSize C from rfl) j
  change (ho.canonicalGraphWeight k anchor C : ℂ) *
      ho.canonicalPrefixData
        (S.physicalSignedSquarePullbackMap
          (KNSGraphSpace.representative k
            (KNSGraphSpace.fourier k
              (KNSGraphSpace.schwartzEmbedding k (complexConjugateSchwartz f))))) C j' =
    starRingEnd ℂ ((ho.canonicalGraphWeight k anchor C : ℂ) *
      ho.canonicalPrefixData
        (S.physicalSignedSquarePullbackMap
          (KNSGraphSpace.representative k
            (KNSGraphSpace.schwartzEmbedding k
              (FourierTransform.fourierInv f)))) C j')
  rw [fourier_schwartzEmbedding,
    KNSGraphSpace.representative_schwartzEmbedding hk,
    KNSGraphSpace.representative_schwartzEmbedding hk,
    fourier_complexConjugateSchwartz,
    ho.canonicalPrefixData_complexConjugate]
  change (ho.canonicalGraphWeight k anchor C : ℂ) *
      starRingEnd ℂ
        (ho.canonicalPrefixData
          (S.physicalSignedSquarePullbackMap ⇑(FourierTransform.fourierInv f)) C j) =
    starRingEnd ℂ ((ho.canonicalGraphWeight k anchor C : ℂ) *
      ho.canonicalPrefixData
        (S.physicalSignedSquarePullbackMap ⇑(FourierTransform.fourierInv f)) C j)
  rw [map_mul, Complex.conj_ofReal]

/-- Inverse Fourier has the expected positive-order action on Schwartz data. -/
theorem schwartzToHermiteScale_fourierInv
    (m : ℕ) (f : SchwartzMap ℝ ℂ) :
    (hermiteFourier (m : ℤ)).symm (schwartzToHermiteScale m f) =
      schwartzToHermiteScale m (FourierTransform.fourierInv f) := by
  apply (hermiteFourier (m : ℤ)).injective
  rw [(hermiteFourier (m : ℤ)).apply_symm_apply,
    schwartzToHermiteScale_fourier]
  exact congrArg (schwartzToHermiteScale m)
    (FourierTransform.fourier_fourierInv_eq f).symm

/-- Arbitrary-order grouped synthesis with canonical graph normalization. -/
def commonOrderPhysicalSynthesis
    (m : ℕ) (hm : 1 ≤ m) (hd : 0 < d)
    (hmB : groupedHermiteDifferentiationOrder (q + 1) ≤ m) :
    CoefficientSpace ho.signedGrouping.Index →L[ℂ]
      HermiteScale (-(m : ℤ)) :=
  (ho.actualGroupedBesselAnalysis hd m hmB).synthesis.comp
    (ho.canonicalToActualTraceEquiv S m hm).toContinuousLinearMap

/-- Its inverse-Fourier companion. -/
def commonOrderInverseFourierSynthesis
    (m : ℕ) (hm : 1 ≤ m) (hd : 0 < d)
    (hmB : groupedHermiteDifferentiationOrder (q + 1) ≤ m) :
    CoefficientSpace ho.signedGrouping.Index →L[ℂ]
      HermiteScale (-(m : ℤ)) :=
  (hermiteFourier (-(m : ℤ))).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ho.commonOrderPhysicalSynthesis m hm hd hmB)

/-- The arbitrary-order synthesis lands in the intrinsic physical support. -/
theorem commonOrderPhysicalSynthesis_range_le
    (m : ℕ) (hm : 1 ≤ m) (hd : 0 < d)
    (hmB : groupedHermiteDifferentiationOrder (q + 1) ≤ m) :
    (ho.commonOrderPhysicalSynthesis m hm hd hmB).range ≤
      (fixedOrderPhysicalSupport S m hm).toSubmodule := by
  rintro _ ⟨c, rfl⟩
  change (ho.actualGroupedBesselAnalysis hd m hmB).synthesis
      (ho.canonicalToActualTraceEquiv S m hm c) ∈ _
  refine (fixedOrderPhysicalSupport S m hm).isClosed'.mem_of_tendsto
    ((ho.actualGroupedBesselAnalysis hd m hmB).hasSum_synthesis
      (ho.canonicalToActualTraceEquiv S m hm c))
    (Filter.Eventually.of_forall fun t => ?_)
  apply Submodule.sum_mem
  intro x hx
  apply Submodule.smul_mem
  rw [← ho.signedGrouping.atom_closedSpan m hm]
  exact atom_mem_atomicSupportSubspace _ x

/-- The arbitrary-order physical synthesis is injective. -/
theorem commonOrderPhysicalSynthesis_injective
    (m : ℕ) (hm : 1 ≤ m) (hd : 0 < d)
    (hmB : groupedHermiteDifferentiationOrder (q + 1) ≤ m) :
    Function.Injective (ho.commonOrderPhysicalSynthesis m hm hd hmB) := by
  exact (ho.signedGrouping.groupedSynthesis_injective m hm
      (ho.actualGroupedBesselAnalysis hd m hmB)).comp
    (ho.canonicalToActualTraceEquiv S m hm).injective

/-- The inverse-Fourier synthesis lands in the inverse-Fourier support. -/
theorem commonOrderInverseFourierSynthesis_range_le
    (m : ℕ) (hm : 1 ≤ m) (hd : 0 < d)
    (hmB : groupedHermiteDifferentiationOrder (q + 1) ≤ m) :
    (ho.commonOrderInverseFourierSynthesis m hm hd hmB).range ≤
      (fixedOrderInverseFourierSupport S m hm).toSubmodule := by
  rintro _ ⟨c, rfl⟩
  change (hermiteFourier (-(m : ℤ))).symm
      (ho.commonOrderPhysicalSynthesis m hm hd hmB c) ∈ _
  rw [fixedOrderInverseFourierSupport, ClosedSubmodule.mapEquiv_apply]
  exact ⟨_, ho.commonOrderPhysicalSynthesis_range_le m hm hd hmB ⟨c, rfl⟩, rfl⟩

/-- The inverse-Fourier synthesis is injective. -/
theorem commonOrderInverseFourierSynthesis_injective
    (m : ℕ) (hm : 1 ≤ m) (hd : 0 < d)
    (hmB : groupedHermiteDifferentiationOrder (q + 1) ≤ m) :
    Function.Injective
      (ho.commonOrderInverseFourierSynthesis m hm hd hmB) :=
  (hermiteFourier (-(m : ℤ))).symm.injective.comp
    (ho.commonOrderPhysicalSynthesis_injective m hm hd hmB)

/-- The physical synthesis pairs with the canonical graph sampler. -/
theorem commonOrderPhysicalSynthesis_pairing
    [DecidableEq ho.signedGrouping.Index]
    (m : ℕ) (hm : 1 ≤ m) (hd : 0 < d)
    (hmB : groupedHermiteDifferentiationOrder (q + 1) ≤ m)
    (hq : q + 1 ≤ 2 * m)
    (c : CoefficientSpace ho.signedGrouping.Index) (f : SchwartzMap ℝ ℂ) :
    hermiteScaleDistribution m
        (ho.commonOrderPhysicalSynthesis m hm hd hmB c) f =
      inner ℂ
        (star (ho.canonicalPhysicalScalarSamplerBounded hd hq
          (ho.canonicalActualAnchor S)
          (KNSGraphSpace.schwartzEmbedding (2 * m) f))) c := by
  exact ho.actualGroupedSynthesis_canonicalToActualTraceEquiv_pairing
    S m hm hd hmB hq c f

/-- The inverse-Fourier synthesis pairs with the physical synthesis against
inverse-Fourier-transformed Schwartz tests. -/
theorem commonOrderInverseFourierSynthesis_pairing
    [DecidableEq ho.signedGrouping.Index]
    (m : ℕ) (hm : 1 ≤ m) (hd : 0 < d)
    (hmB : groupedHermiteDifferentiationOrder (q + 1) ≤ m)
    (hq : q + 1 ≤ 2 * m)
    (c : CoefficientSpace ho.signedGrouping.Index) (f : SchwartzMap ℝ ℂ) :
    hermiteScaleDistribution m
        (ho.commonOrderInverseFourierSynthesis m hm hd hmB c) f =
      inner ℂ
        (star (ho.canonicalPhysicalScalarSamplerBounded hd hq
          (ho.canonicalActualAnchor S)
          (KNSGraphSpace.schwartzEmbedding (2 * m)
            (FourierTransform.fourierInv f)))) c := by
  change hermiteScaleDistribution m
      ((hermiteFourier (-(m : ℤ))).symm
        (ho.commonOrderPhysicalSynthesis m hm hd hmB c)) f = _
  rw [hermiteScaleDistribution_apply, hermiteScalePairing_fourier_symm,
    schwartzToHermiteScale_fourierInv, ← hermiteScaleDistribution_apply]
  exact ho.commonOrderPhysicalSynthesis_pairing m hm hd hmB hq c
    (FourierTransform.fourierInv f)

end BoundedClusterOrder

namespace CanonicalJointSampler

variable {d : ℝ} {q : ℕ}
  (Λ : TwoSidedCarrier)
  (ho : BoundedClusterOrder Λ.toLocallyFinite.signedSquareImage d q)

/-- The two-sided canonical scalar sampler at the common graph order `2m`. -/
def commonOrderScalarSampler
    (m : ℕ) (hd : 0 < d) (hq : q + 1 ≤ 2 * m) :
    KNSGraphSpace (2 * m) →L[ℂ]
      CoefficientSpace (ScalarIndex Λ Λ ho ho) :=
  scalarSamplerBounded Λ Λ ho ho hd hq hd hq
    (ho.canonicalActualAnchor Λ.toLocallyFinite)
    (ho.canonicalActualAnchor Λ.toLocallyFinite)

/-- The signed splitting of the scalar sampler recovers its physical block. -/
theorem signed_commonOrderScalarSampler_fst
    (m : ℕ) (hd : 0 < d) (hq : q + 1 ≤ 2 * m)
    (v : KNSGraphSpace (2 * m)) :
    (signedSumCoefficientEquiv
      (commonOrderScalarSampler Λ ho m hd hq v)).fst =
        ho.canonicalPhysicalScalarSamplerBounded hd hq
          (ho.canonicalActualAnchor Λ.toLocallyFinite) v := by
  apply lp.ext
  funext x
  simp only [commonOrderScalarSampler]
  rw [signedSumCoefficientEquiv_apply_fst_apply,
    scalarSamplerBounded_apply_inl]
  rfl

/-- The signed splitting recovers the negative Fourier block. -/
theorem signed_commonOrderScalarSampler_snd
    (m : ℕ) (hd : 0 < d) (hq : q + 1 ≤ 2 * m)
    (v : KNSGraphSpace (2 * m)) :
    (signedSumCoefficientEquiv
      (commonOrderScalarSampler Λ ho m hd hq v)).snd =
        -ho.canonicalFourierScalarSamplerBounded hd hq
          (ho.canonicalActualAnchor Λ.toLocallyFinite) v := by
  apply lp.ext
  funext x
  simp only [commonOrderScalarSampler]
  rw [signedSumCoefficientEquiv_apply_snd_apply,
    scalarSamplerBounded_apply_inr]
  rfl

/-- Orthogonality to the arbitrary-order canonical graph sampler already
forces the exact equality of the arbitrary-order physical and inverse-Fourier
grouped syntheses.  This bypasses a general graph/Hermite equivalence. -/
theorem commonOrderScalarCokernel_synthesis_eq
    [DecidableEq ho.signedGrouping.Index]
    (m : ℕ) (hm : 1 ≤ m) (hd : 0 < d)
    (hmB : groupedHermiteDifferentiationOrder (q + 1) ≤ m)
    (hq : q + 1 ≤ 2 * m)
    (c : (commonOrderScalarSampler Λ ho m hd hq).rangeᗮ) :
    ho.commonOrderPhysicalSynthesis m hm hd hmB
        (signedSumCoefficientEquiv c.val).fst =
      ho.commonOrderInverseFourierSynthesis m hm hd hmB
        (signedSumCoefficientEquiv c.val).snd := by
  apply hermiteScaleDistribution_injective m
  ext f
  let v : KNSGraphSpace (2 * m) :=
    KNSGraphSpace.schwartzEmbedding (2 * m) (complexConjugateSchwartz f)
  have hc : inner ℂ
      (commonOrderScalarSampler Λ ho m hd hq v) c.val = 0 :=
    (Submodule.mem_orthogonal _ _).mp c.property _ ⟨v, rfl⟩
  have hinner : inner ℂ
      (signedSumCoefficientEquiv
        (commonOrderScalarSampler Λ ho m hd hq v))
      (signedSumCoefficientEquiv c.val) = 0 := by
    rw [LinearIsometryEquiv.inner_map_map, hc]
  have hfst :
      (signedSumCoefficientEquiv
        (commonOrderScalarSampler Λ ho m hd hq v)).fst =
      star (ho.canonicalPhysicalScalarSamplerBounded hd hq
        (ho.canonicalActualAnchor Λ.toLocallyFinite)
        (KNSGraphSpace.schwartzEmbedding (2 * m) f)) := by
    rw [signed_commonOrderScalarSampler_fst]
    exact ho.canonicalPhysicalScalarSamplerBounded_complexConjugate
      (by omega) hd hq (ho.canonicalActualAnchor Λ.toLocallyFinite) f
  have hsnd :
      (signedSumCoefficientEquiv
        (commonOrderScalarSampler Λ ho m hd hq v)).snd =
      -star (ho.canonicalPhysicalScalarSamplerBounded hd hq
        (ho.canonicalActualAnchor Λ.toLocallyFinite)
        (KNSGraphSpace.schwartzEmbedding (2 * m)
          (FourierTransform.fourierInv f))) := by
    rw [signed_commonOrderScalarSampler_snd]
    exact congrArg Neg.neg (ho.canonicalFourierScalarSamplerBounded_complexConjugate
      (by omega) hd hq (ho.canonicalActualAnchor Λ.toLocallyFinite) f)
  rw [WithLp.prod_inner_apply] at hinner
  change inner ℂ
      (signedSumCoefficientEquiv
        (commonOrderScalarSampler Λ ho m hd hq v)).fst
      (signedSumCoefficientEquiv c.val).fst +
    inner ℂ
      (signedSumCoefficientEquiv
        (commonOrderScalarSampler Λ ho m hd hq v)).snd
      (signedSumCoefficientEquiv c.val).snd = 0 at hinner
  rw [hfst, hsnd, inner_neg_left] at hinner
  rw [ho.commonOrderPhysicalSynthesis_pairing m hm hd hmB hq,
    ho.commonOrderInverseFourierSynthesis_pairing m hm hd hmB hq]
  exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hinner)

/-- Continuous signed splitting of an arbitrary-order scalar-sampler
orthogonal cokernel. -/
def commonOrderScalarCokernelSplit
    (m : ℕ) (hd : 0 < d) (hq : q + 1 ≤ 2 * m) :
    (commonOrderScalarSampler Λ ho m hd hq).rangeᗮ →L[ℂ]
      WithLp 2 (CoefficientSpace ho.signedGrouping.Index ×
        CoefficientSpace ho.signedGrouping.Index) :=
  (signedSumCoefficientEquiv
    (I := ho.signedGrouping.Index) (J := ho.signedGrouping.Index)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (commonOrderScalarSampler Λ ho m hd hq).rangeᗮ.subtypeL

/-- Left coefficient projection of the signed cokernel split. -/
def commonOrderScalarCokernelLeft
    (m : ℕ) (hd : 0 < d) (hq : q + 1 ≤ 2 * m) :
    (commonOrderScalarSampler Λ ho m hd hq).rangeᗮ →L[ℂ]
      CoefficientSpace ho.signedGrouping.Index :=
  (WithLp.fstL 2 ℂ (CoefficientSpace ho.signedGrouping.Index)
    (CoefficientSpace ho.signedGrouping.Index)).comp
      (commonOrderScalarCokernelSplit Λ ho m hd hq)

/-- Right coefficient projection of the signed cokernel split. -/
def commonOrderScalarCokernelRight
    (m : ℕ) (hd : 0 < d) (hq : q + 1 ≤ 2 * m) :
    (commonOrderScalarSampler Λ ho m hd hq).rangeᗮ →L[ℂ]
      CoefficientSpace ho.signedGrouping.Index :=
  (WithLp.sndL 2 ℂ (CoefficientSpace ho.signedGrouping.Index)
    (CoefficientSpace ho.signedGrouping.Index)).comp
      (commonOrderScalarCokernelSplit Λ ho m hd hq)

@[simp] theorem commonOrderScalarCokernelLeft_apply
    (m : ℕ) (hd : 0 < d) (hq : q + 1 ≤ 2 * m)
    (c : (commonOrderScalarSampler Λ ho m hd hq).rangeᗮ) :
    commonOrderScalarCokernelLeft Λ ho m hd hq c =
      (signedSumCoefficientEquiv c.val).fst := rfl

@[simp] theorem commonOrderScalarCokernelRight_apply
    (m : ℕ) (hd : 0 < d) (hq : q + 1 ≤ 2 * m)
    (c : (commonOrderScalarSampler Λ ho m hd hq).rangeᗮ) :
    commonOrderScalarCokernelRight Λ ho m hd hq c =
      (signedSumCoefficientEquiv c.val).snd := rfl

/-- Direct injection from the arbitrary common-order graph-sampler cokernel
to the intrinsic Meyer layer, with no graph/Hermite equivalence. -/
def commonOrderScalarCokernelMap
    [DecidableEq ho.signedGrouping.Index]
    (m : ℕ) (hm : 1 ≤ m) (hd : 0 < d)
    (hmB : groupedHermiteDifferentiationOrder (q + 1) ≤ m)
    (hq : q + 1 ≤ 2 * m) :
    (commonOrderScalarSampler Λ ho m hd hq).rangeᗮ →L[ℂ]
      FixedOrderMeyerLayer Λ.toLocallyFinite m hm :=
  ((ho.commonOrderPhysicalSynthesis m hm hd hmB).comp
    (commonOrderScalarCokernelLeft Λ ho m hd hq)).codRestrict
      (FixedOrderMeyerLayer Λ.toLocallyFinite m hm) fun c => by
    constructor
    · exact ho.commonOrderPhysicalSynthesis_range_le m hm hd hmB
        ⟨commonOrderScalarCokernelLeft Λ ho m hd hq c, rfl⟩
    · change ho.commonOrderPhysicalSynthesis m hm hd hmB
          (signedSumCoefficientEquiv c.val).fst ∈
        (fixedOrderInverseFourierSupport Λ.toLocallyFinite m hm).toSubmodule
      rw [commonOrderScalarCokernel_synthesis_eq Λ ho m hm hd hmB hq c]
      exact ho.commonOrderInverseFourierSynthesis_range_le m hm hd hmB
        ⟨(signedSumCoefficientEquiv c.val).snd, rfl⟩

@[simp] theorem commonOrderScalarCokernelMap_apply
    [DecidableEq ho.signedGrouping.Index]
    (m : ℕ) (hm : 1 ≤ m) (hd : 0 < d)
    (hmB : groupedHermiteDifferentiationOrder (q + 1) ≤ m)
    (hq : q + 1 ≤ 2 * m)
    (c : (commonOrderScalarSampler Λ ho m hd hq).rangeᗮ) :
    (commonOrderScalarCokernelMap Λ ho m hm hd hmB hq c :
      HermiteScale (-(m : ℤ))) =
      ho.commonOrderPhysicalSynthesis m hm hd hmB
        (signedSumCoefficientEquiv c.val).fst := rfl

/-- The direct graph-cokernel map is injective. -/
theorem commonOrderScalarCokernelMap_injective
    [DecidableEq ho.signedGrouping.Index]
    (m : ℕ) (hm : 1 ≤ m) (hd : 0 < d)
    (hmB : groupedHermiteDifferentiationOrder (q + 1) ≤ m)
    (hq : q + 1 ≤ 2 * m) :
    Function.Injective
      (commonOrderScalarCokernelMap Λ ho m hm hd hmB hq) := by
  intro c e hce
  have hfirstSynth :
      ho.commonOrderPhysicalSynthesis m hm hd hmB
          (signedSumCoefficientEquiv c.val).fst =
        ho.commonOrderPhysicalSynthesis m hm hd hmB
          (signedSumCoefficientEquiv e.val).fst :=
    congrArg Subtype.val hce
  have hfirst : (signedSumCoefficientEquiv c.val).fst =
      (signedSumCoefficientEquiv e.val).fst :=
    ho.commonOrderPhysicalSynthesis_injective m hm hd hmB hfirstSynth
  have hc := commonOrderScalarCokernel_synthesis_eq
    Λ ho m hm hd hmB hq c
  have he := commonOrderScalarCokernel_synthesis_eq
    Λ ho m hm hd hmB hq e
  have hsecondSynth :
      ho.commonOrderInverseFourierSynthesis m hm hd hmB
          (signedSumCoefficientEquiv c.val).snd =
        ho.commonOrderInverseFourierSynthesis m hm hd hmB
          (signedSumCoefficientEquiv e.val).snd :=
    hc.symm.trans (hfirstSynth.trans he)
  have hsecond : (signedSumCoefficientEquiv c.val).snd =
      (signedSumCoefficientEquiv e.val).snd :=
    ho.commonOrderInverseFourierSynthesis_injective m hm hd hmB hsecondSynth
  apply Subtype.ext
  apply (signedSumCoefficientEquiv
    (I := ho.signedGrouping.Index) (J := ho.signedGrouping.Index)).injective
  apply WithLp.ofLp_injective
  exact Prod.ext hfirst hsecond

/-- Infinite cokernel of the arbitrary common-order graph sampler forces an
infinite intrinsic Meyer layer at the corresponding Hermite order. -/
theorem infinite_fixedOrderMeyerLayer_of_infinite_commonOrderScalarCokernel
    [DecidableEq ho.signedGrouping.Index]
    (m : ℕ) (hm : 1 ≤ m) (hd : 0 < d)
    (hmB : groupedHermiteDifferentiationOrder (q + 1) ≤ m)
    (hq : q + 1 ≤ 2 * m)
    (hinf : ¬ FiniteDimensional ℂ
      (commonOrderScalarSampler Λ ho m hd hq).rangeᗮ) :
    ¬ FiniteDimensional ℂ
      (FixedOrderMeyerLayer Λ.toLocallyFinite m hm) := by
  intro hfin
  let := hfin
  exact hinf (FiniteDimensional.of_injective
    (commonOrderScalarCokernelMap Λ ho m hm hd hmB hq).toLinearMap
    (commonOrderScalarCokernelMap_injective Λ ho m hm hd hmB hq))

end CanonicalJointSampler
end MeyerGeneralProblem
