module

public import MeyerGeneralProblem.Sampling.CanonicalGraphSamplerBound
public import MeyerGeneralProblem.Sampling.CanonicalBlockScalarIsometry
public import MeyerGeneralProblem.Sampling.KNSGraphUniqueness
public import MeyerGeneralProblem.Hilbert.FiniteDeletionDeficiency
public import MeyerGeneralProblem.Cross.CoefficientKernelExtension

@[expose] public section

/-!
# Joint canonical sampling and finite-deletion injectivity

This module combines the bounded physical and Fourier
canonical samplers for two actual ordered carriers.  Their exact dependent
scalar coordinates are embedded into the two sides of one disjoint-sum
coefficient space.  A finite scalar deletion is enlarged to all coordinates
of every touched finite canonical cluster before applying genuine cofinite
point-zero uniqueness.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set MeasureTheory
open scoped ENNReal FourierTransform

attribute [local instance] Classical.propDecidable

namespace KNSGraphSpace

/-- The representative of the genuine graph Fourier transform is pointwise
the ordinary Fourier integral of the original representative.  Both sides
are continuous; the proof uses their common frequency coordinate only to
identify the already-continuous functions. -/
theorem representative_fourier_eq_fourier_representative_for_joint
    {k : ℕ} (hk : 2 ≤ k) (v : KNSGraphSpace k) :
    representative k (fourier k v) = 𝓕 (representative k v) := by
  apply ((representative_contDiff_pair hk (fourier k v)).1.continuous.ae_eq_iff_eq
    volume (representative_contDiff_pair hk v).2.continuous).mp
  have hleft := representative_ae (by omega : 1 ≤ k) (fourier k v)
  have hright := fourier_representative_ae (by omega : 1 ≤ k) v
  rw [physical_fourier, ← frequency_eq_fourier] at hleft
  exact hleft.trans hright.symm

end KNSGraphSpace

private theorem coefficient_apply_eq_inner_atom
    {ι : Type*} [DecidableEq ι] (x : CoefficientSpace ι) (i : ι) :
    x i = inner ℂ (coefficientAtom i) x := by
  change x i = inner ℂ ((coefficientHilbertBasis ι) i) x
  exact (coefficientHilbertBasis ι).repr_apply_apply x i

private theorem coefficientInjection_apply_image
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : ι ↪ κ) (x : CoefficientSpace ι) (i : ι) :
    coefficientInjection e x (e i) = x i := by
  rw [coefficient_apply_eq_inner_atom, coefficient_apply_eq_inner_atom]
  change inner ℂ (coefficientAtom (e i)) (coefficientInjection e x) =
    inner ℂ (coefficientAtom i) x
  rw [← ContinuousLinearMap.adjoint_inner_left,
    coefficientInjection_adjoint_coefficientAtom]

private theorem coefficientInjection_apply_zero_of_not_mem_range
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : ι ↪ κ) (x : CoefficientSpace ι) (j : κ)
    (hj : j ∉ Set.range e) :
    coefficientInjection e x j = 0 := by
  have hadj : (coefficientInjection e).adjoint (coefficientAtom j) = 0 := by
    apply (coefficientHilbertBasis ι).repr.injective
    apply lp.ext
    funext i
    rw [(coefficientHilbertBasis ι).repr_apply_apply,
      (coefficientHilbertBasis ι).repr_apply_apply]
    change inner ℂ (coefficientAtom i)
        ((coefficientInjection e).adjoint (coefficientAtom j)) =
      inner ℂ (coefficientAtom i) 0
    rw [ContinuousLinearMap.adjoint_inner_right,
      coefficientInjection_coefficientAtom]
    have hne : e i ≠ j := fun h => hj ⟨i, h⟩
    have horth :=
      orthonormal_iff_ite.mp (coefficientHilbertBasis κ).orthonormal (e i) j
    change inner ℂ (coefficientAtom (e i)) (coefficientAtom j) =
      (if e i = j then 1 else 0) at horth
    simp [horth, hne]
  rw [coefficient_apply_eq_inner_atom]
  change inner ℂ (coefficientAtom j) (coefficientInjection e x) = 0
  rw [← ContinuousLinearMap.adjoint_inner_left, hadj]
  simp

theorem finiteCoordinateDeletion_apply_of_not_mem
    {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (x : CoefficientSpace ι) (i : ι) (hi : i ∉ F) :
    finiteCoordinateDeletion F x i = x i := by
  rw [coefficient_apply_eq_inner_atom, coefficient_apply_eq_inner_atom]
  change inner ℂ (coefficientAtom i) (finiteCoordinateDeletion F x) =
    inner ℂ (coefficientAtom i) x
  rw [finiteCoordinateDeletion, _root_.sub_apply,
    ContinuousLinearMap.id_apply, inner_sub_right,
    inner_finiteCoordinateProjection]
  simp [hi]

namespace BoundedClusterOrder

variable {S : LocallyFiniteCarrier} {d : ℝ} {q : ℕ}
  (ho : BoundedClusterOrder S.signedSquareImage d q)

/-- Enlarge finitely many dependent scalar coordinates to every coordinate
of each canonical cluster which they touch. -/
def wholeClusterCoordinateEnlargement
    (F : Finset ho.signedGrouping.Index) : Finset ho.signedGrouping.Index :=
  (F.image Sigma.fst).sigma fun _C => Finset.univ

theorem subset_wholeClusterCoordinateEnlargement
    (F : Finset ho.signedGrouping.Index) :
    F ⊆ ho.wholeClusterCoordinateEnlargement F := by
  intro x hx
  rcases x with ⟨C, i⟩
  simp only [wholeClusterCoordinateEnlargement, Finset.mem_sigma,
    Finset.mem_image, Finset.mem_univ, and_true]
  exact ⟨⟨C, i⟩, hx, rfl⟩

theorem mem_wholeClusterCoordinateEnlargement_iff
    (F : Finset ho.signedGrouping.Index) (x : ho.signedGrouping.Index) :
    x ∈ ho.wholeClusterCoordinateEnlargement F ↔ x.1 ∈ F.image Sigma.fst := by
  rcases x with ⟨C, i⟩
  simp [wholeClusterCoordinateEnlargement]

theorem wholeClusterCoordinateEnlargement_finite
    (F : Finset ho.signedGrouping.Index) :
    ((ho.wholeClusterCoordinateEnlargement F : Finset ho.signedGrouping.Index) :
      Set ho.signedGrouping.Index).Finite :=
  Finset.finite_toSet _

/-- The physical sampler with its canonical finite blocks flattened to the
exact dependent scalar index. -/
def canonicalPhysicalScalarSamplerBounded
    {k : ℕ} (hd : 0 < d) (hq : q + 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C)) :
    KNSGraphSpace k →L[ℂ] CoefficientSpace ho.signedGrouping.Index :=
  ho.canonicalGraphDataCoefficientEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ho.canonicalPhysicalSamplerBounded S hd hq anchor)

@[simp] theorem canonicalPhysicalScalarSamplerBounded_apply
    {k : ℕ} (hd : 0 < d) (hq : q + 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (v : KNSGraphSpace k) (x : ho.signedGrouping.Index) :
    ho.canonicalPhysicalScalarSamplerBounded hd hq anchor v x =
      (ho.canonicalGraphWeight k anchor x.1 : ℂ) *
        ho.canonicalPrefixData
          (S.physicalSignedSquarePullbackMap
            (KNSGraphSpace.representative k v)) x.1 x.2 := by
  rcases x with ⟨C, i⟩
  rfl

/-- The Fourier sampler with its canonical finite blocks flattened to the
exact dependent scalar index. -/
def canonicalFourierScalarSamplerBounded
    {k : ℕ} (hd : 0 < d) (hq : q + 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C)) :
    KNSGraphSpace k →L[ℂ] CoefficientSpace ho.signedGrouping.Index :=
  ho.canonicalGraphDataCoefficientEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ho.canonicalFourierSamplerBounded S hd hq anchor)

@[simp] theorem canonicalFourierScalarSamplerBounded_apply
    {k : ℕ} (hd : 0 < d) (hq : q + 1 ≤ k)
    (anchor : (C : CanonicalClusterIndex S.signedSquareImage d) →
      Fin (ho.clusterSize C))
    (v : KNSGraphSpace k) (x : ho.signedGrouping.Index) :
    ho.canonicalFourierScalarSamplerBounded hd hq anchor v x =
      (ho.canonicalGraphWeight k anchor x.1 : ℂ) *
        ho.canonicalPrefixData
          (S.physicalSignedSquarePullbackMap
            (KNSGraphSpace.representative k
              (KNSGraphSpace.fourier k v))) x.1 x.2 := by
  rcases x with ⟨C, i⟩
  rfl

end BoundedClusterOrder

namespace CanonicalJointSampler

variable {dΛ dM : ℝ} {qΛ qM : ℕ}
  (Λ M : TwoSidedCarrier)
  (hoΛ : BoundedClusterOrder Λ.toLocallyFinite.signedSquareImage dΛ qΛ)
  (hoM : BoundedClusterOrder M.toLocallyFinite.signedSquareImage dM qM)

/-- The disjoint scalar coordinate set for the physical and Fourier rows of
the joint sampler. -/
abbrev ScalarIndex := hoΛ.signedGrouping.Index ⊕ hoM.signedGrouping.Index

/-- The integer carrier index represented by one canonical scalar
coordinate.  This is the exact inverse of the two actual subtype
equivalences, with no new enumeration. -/
def carrierIndexOfScalar
    (T : TwoSidedCarrier) {d : ℝ} {q : ℕ}
    (ho : BoundedClusterOrder T.toLocallyFinite.signedSquareImage d q)
    (x : ho.signedGrouping.Index) : ℤ :=
  T.indexSubtypeEquiv.symm
    (T.toLocallyFinite.signedSquareSubtypeEquiv.symm
      (ho.orderedClusterNode x.1 x.2))

@[simp] theorem indexSubtypeEquiv_carrierIndexOfScalar
    (T : TwoSidedCarrier) {d : ℝ} {q : ℕ}
    (ho : BoundedClusterOrder T.toLocallyFinite.signedSquareImage d q)
    (x : ho.signedGrouping.Index) :
    T.indexSubtypeEquiv (carrierIndexOfScalar T ho x) =
      T.toLocallyFinite.signedSquareSubtypeEquiv.symm
        (ho.orderedClusterNode x.1 x.2) := by
  simp [carrierIndexOfScalar]

/-- A finite coordinate deletion produces a finite exceptional set of
actual integer carrier points after enlarging every touched canonical
cluster to all of its scalar coordinates. -/
def deletedCarrierIndices
    (T : TwoSidedCarrier) {d : ℝ} {q : ℕ}
    (ho : BoundedClusterOrder T.toLocallyFinite.signedSquareImage d q)
    (F : Finset ho.signedGrouping.Index) : Finset ℤ :=
  (ho.wholeClusterCoordinateEnlargement F).image
    (carrierIndexOfScalar T ho)

theorem deletedCarrierIndices_finite
    (T : TwoSidedCarrier) {d : ℝ} {q : ℕ}
    (ho : BoundedClusterOrder T.toLocallyFinite.signedSquareImage d q)
    (F : Finset ho.signedGrouping.Index) :
    ((deletedCarrierIndices T ho F : Finset ℤ) : Set ℤ).Finite :=
  Finset.finite_toSet _

/-- The genuine bounded joint sampler before scalar flattening.  The first
component samples the actual physical representative on `Λ`; the second
samples the transformed graph representative on `M`. -/
def graphSamplerBounded
    {k : ℕ}
    (hdΛ : 0 < dΛ) (hqΛ : qΛ + 1 ≤ k)
    (hdM : 0 < dM) (hqM : qM + 1 ≤ k)
    (anchorΛ : (C : CanonicalClusterIndex Λ.toLocallyFinite.signedSquareImage dΛ) →
      Fin (hoΛ.clusterSize C))
    (anchorM : (C : CanonicalClusterIndex M.toLocallyFinite.signedSquareImage dM) →
      Fin (hoM.clusterSize C)) :
    KNSGraphSpace k →L[ℂ] hoΛ.CanonicalGraphData × hoM.CanonicalGraphData :=
  (hoΛ.canonicalPhysicalSamplerBounded Λ.toLocallyFinite hdΛ hqΛ anchorΛ).prod
    (hoM.canonicalFourierSamplerBounded M.toLocallyFinite hdM hqM anchorM)

@[simp] theorem graphSamplerBounded_apply
    {k : ℕ}
    (hdΛ : 0 < dΛ) (hqΛ : qΛ + 1 ≤ k)
    (hdM : 0 < dM) (hqM : qM + 1 ≤ k)
    (anchorΛ : (C : CanonicalClusterIndex Λ.toLocallyFinite.signedSquareImage dΛ) →
      Fin (hoΛ.clusterSize C))
    (anchorM : (C : CanonicalClusterIndex M.toLocallyFinite.signedSquareImage dM) →
      Fin (hoM.clusterSize C))
    (v : KNSGraphSpace k) :
    graphSamplerBounded Λ M hoΛ hoM hdΛ hqΛ hdM hqM anchorΛ anchorM v =
      (hoΛ.canonicalPhysicalSamplerBounded Λ.toLocallyFinite hdΛ hqΛ anchorΛ v,
       hoM.canonicalFourierSamplerBounded M.toLocallyFinite hdM hqM anchorM v) := rfl

/-- Flatten the two genuine graph-data components and embed them into the
left and right sides of one disjoint-sum scalar coefficient space. -/
def scalarSamplerBounded
    {k : ℕ}
    (hdΛ : 0 < dΛ) (hqΛ : qΛ + 1 ≤ k)
    (hdM : 0 < dM) (hqM : qM + 1 ≤ k)
    (anchorΛ : (C : CanonicalClusterIndex Λ.toLocallyFinite.signedSquareImage dΛ) →
      Fin (hoΛ.clusterSize C))
    (anchorM : (C : CanonicalClusterIndex M.toLocallyFinite.signedSquareImage dM) →
      Fin (hoM.clusterSize C)) :
    KNSGraphSpace k →L[ℂ] CoefficientSpace (ScalarIndex Λ M hoΛ hoM) :=
  (coefficientInjection
      (Function.Embedding.inl : hoΛ.signedGrouping.Index ↪
        ScalarIndex Λ M hoΛ hoM)).comp
      (hoΛ.canonicalPhysicalScalarSamplerBounded hdΛ hqΛ anchorΛ) +
    (coefficientInjection
      (Function.Embedding.inr : hoM.signedGrouping.Index ↪
        ScalarIndex Λ M hoΛ hoM)).comp
      (hoM.canonicalFourierScalarSamplerBounded hdM hqM anchorM)

@[simp] theorem scalarSamplerBounded_apply_inl
    {k : ℕ}
    (hdΛ : 0 < dΛ) (hqΛ : qΛ + 1 ≤ k)
    (hdM : 0 < dM) (hqM : qM + 1 ≤ k)
    (anchorΛ : (C : CanonicalClusterIndex Λ.toLocallyFinite.signedSquareImage dΛ) →
      Fin (hoΛ.clusterSize C))
    (anchorM : (C : CanonicalClusterIndex M.toLocallyFinite.signedSquareImage dM) →
      Fin (hoM.clusterSize C))
    (v : KNSGraphSpace k) (x : hoΛ.signedGrouping.Index) :
    scalarSamplerBounded Λ M hoΛ hoM hdΛ hqΛ hdM hqM anchorΛ anchorM v (.inl x) =
      (hoΛ.canonicalGraphWeight k anchorΛ x.1 : ℂ) *
        hoΛ.canonicalPrefixData
          (Λ.toLocallyFinite.physicalSignedSquarePullbackMap
            (KNSGraphSpace.representative k v)) x.1 x.2 := by
  unfold scalarSamplerBounded
  change
    coefficientInjection Function.Embedding.inl
        (hoΛ.canonicalPhysicalScalarSamplerBounded hdΛ hqΛ anchorΛ v) (.inl x) +
      coefficientInjection Function.Embedding.inr
        (hoM.canonicalFourierScalarSamplerBounded hdM hqM anchorM v) (.inl x) = _
  have hleft := coefficientInjection_apply_image
    (e := (Function.Embedding.inl : hoΛ.signedGrouping.Index ↪
      ScalarIndex Λ M hoΛ hoM))
    (hoΛ.canonicalPhysicalScalarSamplerBounded hdΛ hqΛ anchorΛ v) x
  change coefficientInjection Function.Embedding.inl
      (hoΛ.canonicalPhysicalScalarSamplerBounded hdΛ hqΛ anchorΛ v) (.inl x) =
    hoΛ.canonicalPhysicalScalarSamplerBounded hdΛ hqΛ anchorΛ v x at hleft
  have hright := coefficientInjection_apply_zero_of_not_mem_range
    (e := (Function.Embedding.inr : hoM.signedGrouping.Index ↪
      ScalarIndex Λ M hoΛ hoM))
    (hoM.canonicalFourierScalarSamplerBounded hdM hqM anchorM v) (.inl x) (by simp)
  rw [hleft, hright, add_zero]
  exact hoΛ.canonicalPhysicalScalarSamplerBounded_apply hdΛ hqΛ anchorΛ v x

@[simp] theorem scalarSamplerBounded_apply_inr
    {k : ℕ}
    (hdΛ : 0 < dΛ) (hqΛ : qΛ + 1 ≤ k)
    (hdM : 0 < dM) (hqM : qM + 1 ≤ k)
    (anchorΛ : (C : CanonicalClusterIndex Λ.toLocallyFinite.signedSquareImage dΛ) →
      Fin (hoΛ.clusterSize C))
    (anchorM : (C : CanonicalClusterIndex M.toLocallyFinite.signedSquareImage dM) →
      Fin (hoM.clusterSize C))
    (v : KNSGraphSpace k) (x : hoM.signedGrouping.Index) :
    scalarSamplerBounded Λ M hoΛ hoM hdΛ hqΛ hdM hqM anchorΛ anchorM v (.inr x) =
      (hoM.canonicalGraphWeight k anchorM x.1 : ℂ) *
        hoM.canonicalPrefixData
          (M.toLocallyFinite.physicalSignedSquarePullbackMap
            (KNSGraphSpace.representative k (KNSGraphSpace.fourier k v))) x.1 x.2 := by
  unfold scalarSamplerBounded
  change
    coefficientInjection Function.Embedding.inl
        (hoΛ.canonicalPhysicalScalarSamplerBounded hdΛ hqΛ anchorΛ v) (.inr x) +
      coefficientInjection Function.Embedding.inr
        (hoM.canonicalFourierScalarSamplerBounded hdM hqM anchorM v) (.inr x) = _
  have hleft := coefficientInjection_apply_zero_of_not_mem_range
    (e := (Function.Embedding.inl : hoΛ.signedGrouping.Index ↪
      ScalarIndex Λ M hoΛ hoM))
    (hoΛ.canonicalPhysicalScalarSamplerBounded hdΛ hqΛ anchorΛ v) (.inr x) (by simp)
  have hright := coefficientInjection_apply_image
    (e := (Function.Embedding.inr : hoM.signedGrouping.Index ↪
      ScalarIndex Λ M hoΛ hoM))
    (hoM.canonicalFourierScalarSamplerBounded hdM hqM anchorM v) x
  change coefficientInjection Function.Embedding.inr
      (hoM.canonicalFourierScalarSamplerBounded hdM hqM anchorM v) (.inr x) =
    hoM.canonicalFourierScalarSamplerBounded hdM hqM anchorM v x at hright
  rw [hleft, hright, zero_add]
  exact hoM.canonicalFourierScalarSamplerBounded_apply hdM hqM anchorM v x

private theorem physicalPrefix_eq_zero_of_cluster_not_touched
    {k : ℕ}
    (hdΛ : 0 < dΛ) (hqΛ : qΛ + 1 ≤ k)
    (hdM : 0 < dM) (hqM : qM + 1 ≤ k)
    (anchorΛ : (C : CanonicalClusterIndex Λ.toLocallyFinite.signedSquareImage dΛ) →
      Fin (hoΛ.clusterSize C))
    (anchorM : (C : CanonicalClusterIndex M.toLocallyFinite.signedSquareImage dM) →
      Fin (hoM.clusterSize C))
    (F : Finset (ScalarIndex Λ M hoΛ hoM)) (v : KNSGraphSpace k)
    (hzero : finiteCoordinateDeletion F
      (scalarSamplerBounded Λ M hoΛ hoM hdΛ hqΛ hdM hqM anchorΛ anchorM v) = 0)
    (C : CanonicalClusterIndex Λ.toLocallyFinite.signedSquareImage dΛ)
    (hC : C ∉ F.toLeft.image Sigma.fst) :
    hoΛ.canonicalPrefixData
        (Λ.toLocallyFinite.physicalSignedSquarePullbackMap
          (KNSGraphSpace.representative k v)) C = 0 := by
  funext r
  have hnotF : Sum.inl (⟨C, r⟩ : hoΛ.signedGrouping.Index) ∉ F := by
    intro hmem
    apply hC
    have hx : (⟨C, r⟩ : hoΛ.signedGrouping.Index) ∈ F.toLeft :=
      Finset.mem_toLeft.mpr hmem
    exact Finset.mem_image_of_mem Sigma.fst hx
  have hzcoord :
      scalarSamplerBounded Λ M hoΛ hoM hdΛ hqΛ hdM hqM anchorΛ anchorM v
          (.inl (⟨C, r⟩ : hoΛ.signedGrouping.Index)) = 0 := by
    rw [← finiteCoordinateDeletion_apply_of_not_mem F _ _ hnotF, hzero]
    rfl
  rw [scalarSamplerBounded_apply_inl] at hzcoord
  have hw : (hoΛ.canonicalGraphWeight k anchorΛ C : ℂ) ≠ 0 := by
    exact_mod_cast (hoΛ.canonicalGraphWeight_pos k anchorΛ C).ne'
  exact (mul_eq_zero.mp hzcoord).resolve_left hw

private theorem fourierPrefix_eq_zero_of_cluster_not_touched
    {k : ℕ}
    (hdΛ : 0 < dΛ) (hqΛ : qΛ + 1 ≤ k)
    (hdM : 0 < dM) (hqM : qM + 1 ≤ k)
    (anchorΛ : (C : CanonicalClusterIndex Λ.toLocallyFinite.signedSquareImage dΛ) →
      Fin (hoΛ.clusterSize C))
    (anchorM : (C : CanonicalClusterIndex M.toLocallyFinite.signedSquareImage dM) →
      Fin (hoM.clusterSize C))
    (F : Finset (ScalarIndex Λ M hoΛ hoM)) (v : KNSGraphSpace k)
    (hzero : finiteCoordinateDeletion F
      (scalarSamplerBounded Λ M hoΛ hoM hdΛ hqΛ hdM hqM anchorΛ anchorM v) = 0)
    (C : CanonicalClusterIndex M.toLocallyFinite.signedSquareImage dM)
    (hC : C ∉ F.toRight.image Sigma.fst) :
    hoM.canonicalPrefixData
        (M.toLocallyFinite.physicalSignedSquarePullbackMap
          (KNSGraphSpace.representative k (KNSGraphSpace.fourier k v))) C = 0 := by
  funext r
  have hnotF : Sum.inr (⟨C, r⟩ : hoM.signedGrouping.Index) ∉ F := by
    intro hmem
    apply hC
    have hx : (⟨C, r⟩ : hoM.signedGrouping.Index) ∈ F.toRight :=
      Finset.mem_toRight.mpr hmem
    exact Finset.mem_image_of_mem Sigma.fst hx
  have hzcoord :
      scalarSamplerBounded Λ M hoΛ hoM hdΛ hqΛ hdM hqM anchorΛ anchorM v
          (.inr (⟨C, r⟩ : hoM.signedGrouping.Index)) = 0 := by
    rw [← finiteCoordinateDeletion_apply_of_not_mem F _ _ hnotF, hzero]
    rfl
  rw [scalarSamplerBounded_apply_inr] at hzcoord
  have hw : (hoM.canonicalGraphWeight k anchorM C : ℂ) ≠ 0 := by
    exact_mod_cast (hoM.canonicalGraphWeight_pos k anchorM C).ne'
  exact (mul_eq_zero.mp hzcoord).resolve_left hw

/-- Deleting any finite collection of exact scalar canonical coordinates
leaves the genuine joint sampler injective.  The only extra assumptions are
the two cofinite reciprocal-gap bounds required by graph uniqueness. -/
theorem finiteDeletion_scalarSamplerBounded_injective
    {k : ℕ} (hk : 2 ≤ k)
    (hdΛ : 0 < dΛ) (hqΛ : qΛ + 1 ≤ k)
    (hdM : 0 < dM) (hqM : qM + 1 ≤ k)
    (anchorΛ : (C : CanonicalClusterIndex Λ.toLocallyFinite.signedSquareImage dΛ) →
      Fin (hoΛ.clusterSize C))
    (anchorM : (C : CanonicalClusterIndex M.toLocallyFinite.signedSquareImage dM) →
      Fin (hoM.clusterSize C))
    {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (J L : Finset ℤ)
    (hgapΛ : ∀ j : ℤ, j ∉ J →
      max |Λ j| |Λ (j + 1)| * (Λ (j + 1) - Λ j) ≤ ρ)
    (hgapM : ∀ j : ℤ, j ∉ L →
      max |M j| |M (j + 1)| * (M (j + 1) - M j) ≤ ρ) :
    ∀ F : Finset (ScalarIndex Λ M hoΛ hoM),
      Function.Injective
        ((finiteCoordinateDeletion F).comp
          (scalarSamplerBounded Λ M hoΛ hoM
            hdΛ hqΛ hdM hqM anchorΛ anchorM)) := by
  intro F
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change finiteCoordinateDeletion F
    (scalarSamplerBounded Λ M hoΛ hoM
      hdΛ hqΛ hdM hqM anchorΛ anchorM v) = 0 at hv
  apply KNSGraphSpace.eq_zero_of_representative_zeros hk hρ hρhalf
    Λ M
    (deletedCarrierIndices Λ hoΛ F.toLeft) J
    (deletedCarrierIndices M hoM F.toRight) L
    hgapΛ hgapM v
  · intro j hj
    obtain ⟨⟨C, i⟩, hnode⟩ :=
      hoΛ.orderedClusterNode_bijective.2
        (Λ.toLocallyFinite.signedSquareSubtypeEquiv (Λ.indexSubtypeEquiv j))
    change hoΛ.orderedClusterNode C i =
      Λ.toLocallyFinite.signedSquareSubtypeEquiv (Λ.indexSubtypeEquiv j) at hnode
    have hC : C ∉ F.toLeft.image Sigma.fst := by
      intro hCtouched
      apply hj
      simp only [deletedCarrierIndices, Finset.mem_image]
      refine ⟨(⟨C, i⟩ : hoΛ.signedGrouping.Index), ?_, ?_⟩
      · exact (hoΛ.mem_wholeClusterCoordinateEnlargement_iff F.toLeft ⟨C, i⟩).2 hCtouched
      · apply Λ.indexSubtypeEquiv.injective
        rw [indexSubtypeEquiv_carrierIndexOfScalar, hnode,
          Equiv.symm_apply_apply]
    have hprefix := physicalPrefix_eq_zero_of_cluster_not_touched
      Λ M hoΛ hoM hdΛ hqΛ hdM hqM anchorΛ anchorM F v hv C hC
    have hforward :=
      hoΛ.canonicalPrefixData_representative_eq_forward_values
        Λ.toLocallyFinite v C
    rw [hprefix] at hforward
    have hvalues :
        (fun r : Fin (hoΛ.clusterSize C) =>
          KNSGraphSpace.representative k v
            (Λ.toLocallyFinite.signedSquareSubtypeEquiv.symm
              (hoΛ.orderedClusterNode C r))) = 0 := by
      apply (hoΛ.canonicalValuesEquiv C).injective
      simpa only [map_zero] using hforward.symm
    have hi := congrFun hvalues i
    change KNSGraphSpace.representative k v (Λ j) = 0
    simpa only [Pi.zero_apply, hnode, Equiv.symm_apply_apply,
      TwoSidedCarrier.coe_indexSubtypeEquiv] using hi
  · intro j hj
    obtain ⟨⟨C, i⟩, hnode⟩ :=
      hoM.orderedClusterNode_bijective.2
        (M.toLocallyFinite.signedSquareSubtypeEquiv (M.indexSubtypeEquiv j))
    change hoM.orderedClusterNode C i =
      M.toLocallyFinite.signedSquareSubtypeEquiv (M.indexSubtypeEquiv j) at hnode
    have hC : C ∉ F.toRight.image Sigma.fst := by
      intro hCtouched
      apply hj
      simp only [deletedCarrierIndices, Finset.mem_image]
      refine ⟨(⟨C, i⟩ : hoM.signedGrouping.Index), ?_, ?_⟩
      · exact (hoM.mem_wholeClusterCoordinateEnlargement_iff F.toRight ⟨C, i⟩).2 hCtouched
      · apply M.indexSubtypeEquiv.injective
        rw [indexSubtypeEquiv_carrierIndexOfScalar, hnode,
          Equiv.symm_apply_apply]
    have hprefix := fourierPrefix_eq_zero_of_cluster_not_touched
      Λ M hoΛ hoM hdΛ hqΛ hdM hqM anchorΛ anchorM F v hv C hC
    have hforward :=
      hoM.canonicalPrefixData_representative_eq_forward_values
        M.toLocallyFinite (KNSGraphSpace.fourier k v) C
    rw [hprefix] at hforward
    have hvalues :
        (fun r : Fin (hoM.clusterSize C) =>
          KNSGraphSpace.representative k (KNSGraphSpace.fourier k v)
            (M.toLocallyFinite.signedSquareSubtypeEquiv.symm
              (hoM.orderedClusterNode C r))) = 0 := by
      apply (hoM.canonicalValuesEquiv C).injective
      simpa only [map_zero] using hforward.symm
    have hi := congrFun hvalues i
    rw [← KNSGraphSpace.representative_fourier_eq_fourier_representative_for_joint
      hk v]
    simpa only [Pi.zero_apply, hnode, Equiv.symm_apply_apply,
      TwoSidedCarrier.coe_indexSubtypeEquiv] using hi


end CanonicalJointSampler

end


end MeyerGeneralProblem
