module

public import MeyerGeneralProblem.Trace.Presentation
public import MeyerGeneralProblem.Hermite.DistributionCoherence
public import MeyerGeneralProblem.Endpoint.Certificates
public import MeyerGeneralProblem.Fredholm.PathTransport
public import Mathlib.Analysis.InnerProductSpace.ProdL2

@[expose] public section

/-!
# The actual paired-sampling cokernel maps into the support intersection

This module uses the orthogonal complement of the range of an actual bounded
Hilbert-space sampling operator, not a separately postulated kernel. Its adjoint
is the difference of the two synthesis maps. Injectivity of both syntheses and
their actual range inclusions give an injective map to the intrinsic support
intersection, hence to the distributional Meyer space in the Hermite instance.
No frame lower bound, individual-mass growth estimate, or finite-cokernel
hypothesis is used. Analytic grouped synthesis bounds remain separate inputs.
-/

namespace MeyerGeneralProblem

noncomputable section

variable {E F H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Difference of two genuine synthesis maps on the Hilbert direct sum. -/
def pairedTraceSynthesis (A : E →L[ℂ] H) (B : F →L[ℂ] H) :
    WithLp 2 (E × F) →L[ℂ] H :=
  A.comp (WithLp.fstL 2 ℂ E F) - B.comp (WithLp.sndL 2 ℂ E F)

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace H] in
@[simp]
theorem pairedTraceSynthesis_apply (A : E →L[ℂ] H) (B : F →L[ℂ] H)
    (c : WithLp 2 (E × F)) :
    pairedTraceSynthesis A B c = A c.fst - B c.snd := rfl

/-- Paired sampling is the actual Hilbert adjoint of synthesis difference. -/
def pairedTraceSampling (A : E →L[ℂ] H) (B : F →L[ℂ] H) :
    H →L[ℂ] WithLp 2 (E × F) :=
  (pairedTraceSynthesis A B).adjoint

/-- Paired sampling really consists of the two adjoint sample vectors,
with the minus sign fixing the synthesis-equality convention. -/
theorem pairedTraceSampling_apply (A : E →L[ℂ] H) (B : F →L[ℂ] H)
    (x : H) :
    pairedTraceSampling A B x = WithLp.toLp 2 (A.adjoint x, -B.adjoint x) := by
  apply ext_inner_left ℂ
  intro c
  rw [pairedTraceSampling, ContinuousLinearMap.adjoint_inner_right]
  simp only [pairedTraceSynthesis_apply, WithLp.prod_inner_apply, inner_neg_right,
    ContinuousLinearMap.adjoint_inner_right, sub_eq_add_neg, inner_add_left, inner_neg_left]
  rfl

/-- The adjoint relation is exact, with no closed-range assumption. -/
theorem pairedTraceSampling_adjoint (A : E →L[ℂ] H) (B : F →L[ℂ] H) :
    (pairedTraceSampling A B).adjoint = pairedTraceSynthesis A B := by
  exact ContinuousLinearMap.adjoint_adjoint _

/-- An actual orthogonal-cokernel vector identifies the two synthesized
vectors. This is the Fourier relation when the second synthesis is inverse
Fourier synthesis. -/
theorem mem_pairedTraceSampling_orthogonal_iff
    (A : E →L[ℂ] H) (B : F →L[ℂ] H) (c : WithLp 2 (E × F)) :
    c ∈ (pairedTraceSampling A B).rangeᗮ ↔ A c.fst = B c.snd := by
  rw [ContinuousLinearMap.orthogonal_range, pairedTraceSampling_adjoint]
  change pairedTraceSynthesis A B c = 0 ↔ _
  simp only [pairedTraceSynthesis_apply, sub_eq_zero]

/-- The actual paired-sampling orthogonal cokernel maps continuously into
the intersection whenever both synthesis ranges have the declared support. -/
def pairedSamplingCokernelToIntersection
    (A : E →L[ℂ] H) (B : F →L[ℂ] H)
    (X Y : Submodule ℂ H) (hA : A.range ≤ X) (hB : B.range ≤ Y) :
    (pairedTraceSampling A B).rangeᗮ →L[ℂ] ↥(X ⊓ Y : Submodule ℂ H) :=
  ((A.comp (WithLp.fstL 2 ℂ E F)).domRestrict
    (pairedTraceSampling A B).rangeᗮ).codRestrict (X ⊓ Y) fun c => by
      constructor
      · exact hA ⟨c.val.fst, rfl⟩
      · have h := (mem_pairedTraceSampling_orthogonal_iff A B c.val).mp c.property
        change A c.val.fst ∈ Y
        rw [h]
        exact hB ⟨c.val.snd, rfl⟩

@[simp]
theorem pairedSamplingCokernelToIntersection_apply
    (A : E →L[ℂ] H) (B : F →L[ℂ] H)
    (X Y : Submodule ℂ H) (hA : A.range ≤ X) (hB : B.range ≤ Y)
    (c : (pairedTraceSampling A B).rangeᗮ) :
    (pairedSamplingCokernelToIntersection A B X Y hA hB c : H) =
      A c.val.fst := rfl

/-- The map loses no cokernel vector if both actual syntheses are injective. -/
theorem pairedSamplingCokernelToIntersection_injective
    (A : E →L[ℂ] H) (B : F →L[ℂ] H)
    (X Y : Submodule ℂ H) (hA : A.range ≤ X) (hB : B.range ≤ Y)
    (hAi : Function.Injective A) (hBi : Function.Injective B) :
    Function.Injective (pairedSamplingCokernelToIntersection A B X Y hA hB) := by
  intro c d hcd
  have hfirst : A c.val.fst = A d.val.fst := congrArg Subtype.val hcd
  have hc := (mem_pairedTraceSampling_orthogonal_iff A B c.val).mp c.property
  have hd := (mem_pairedTraceSampling_orthogonal_iff A B d.val).mp d.property
  have hsecond : B c.val.snd = B d.val.snd := hc.symm.trans (hfirst.trans hd)
  apply Subtype.ext
  apply (WithLp.equiv 2 (E × F)).injective
  exact Prod.ext (hAi hfirst) (hBi hsecond)

/-- Infinite orthogonal cokernel forces an infinite support intersection;
the sampling operator itself need not have closed range. -/
theorem infinite_intersection_of_infinite_pairedSamplingCokernel
    (A : E →L[ℂ] H) (B : F →L[ℂ] H)
    (X Y : Submodule ℂ H) (hA : A.range ≤ X) (hB : B.range ≤ Y)
    (hAi : Function.Injective A) (hBi : Function.Injective B)
    (hinf : ¬ FiniteDimensional ℂ (pairedTraceSampling A B).rangeᗮ) :
    ¬ FiniteDimensional ℂ ↥(X ⊓ Y : Submodule ℂ H) := by
  intro hfin
  let := hfin
  exact hinf (FiniteDimensional.of_injective
    (pairedSamplingCokernelToIntersection A B X Y hA hB).toLinearMap
    (pairedSamplingCokernelToIntersection_injective A B X Y hA hB hAi hBi))

/-- Actual Hermite synthesis ranges give a map from sampling's orthogonal
cokernel to the exact intrinsic Meyer layer, at the same order. -/
def fixedOrderPairedSamplingCokernelMap
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m)
    (A : E →L[ℂ] HermiteScale (-(m : ℤ)))
    (B : F →L[ℂ] HermiteScale (-(m : ℤ)))
    (hA : A.range ≤ (fixedOrderPhysicalSupport S m hm).toSubmodule)
    (hB : B.range ≤ (fixedOrderInverseFourierSupport S m hm).toSubmodule) :
    (pairedTraceSampling A B).rangeᗮ →L[ℂ] FixedOrderMeyerLayer S m hm :=
  pairedSamplingCokernelToIntersection A B _ _ hA hB

/-- The cokernel-to-intrinsic-layer map is injective as soon as the two
actual syntheses are injective. -/
theorem fixedOrderPairedSamplingCokernelMap_injective
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m)
    (A : E →L[ℂ] HermiteScale (-(m : ℤ)))
    (B : F →L[ℂ] HermiteScale (-(m : ℤ)))
    (hA : A.range ≤ (fixedOrderPhysicalSupport S m hm).toSubmodule)
    (hB : B.range ≤ (fixedOrderInverseFourierSupport S m hm).toSubmodule)
    (hAi : Function.Injective A) (hBi : Function.Injective B) :
    Function.Injective (fixedOrderPairedSamplingCokernelMap S m hm A B hA hB) :=
  pairedSamplingCokernelToIntersection_injective A B _ _ hA hB hAi hBi

/-- The orthogonal cokernel realizes in the genuine distributional Meyer
space through the already-proved intrinsic realization. -/
def pairedSamplingCokernelToDistributionalMeyerSpace
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m)
    (A : E →L[ℂ] HermiteScale (-(m : ℤ)))
    (B : F →L[ℂ] HermiteScale (-(m : ℤ)))
    (hA : A.range ≤ (fixedOrderPhysicalSupport S m hm).toSubmodule)
    (hB : B.range ≤ (fixedOrderInverseFourierSupport S m hm).toSubmodule) :
    (pairedTraceSampling A B).rangeᗮ →L[ℂ] DistributionalMeyerSpace S :=
  (fixedOrderMeyerLayerToDistributionalMeyerSpace S m hm).comp
    (fixedOrderPairedSamplingCokernelMap S m hm A B hA hB)

/-- Distributional realization also loses no cokernel vector. No separate
polynomial estimate on the individual carrier masses is assumed. -/
theorem pairedSamplingCokernelToDistributionalMeyerSpace_injective
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m)
    (A : E →L[ℂ] HermiteScale (-(m : ℤ)))
    (B : F →L[ℂ] HermiteScale (-(m : ℤ)))
    (hA : A.range ≤ (fixedOrderPhysicalSupport S m hm).toSubmodule)
    (hB : B.range ≤ (fixedOrderInverseFourierSupport S m hm).toSubmodule)
    (hAi : Function.Injective A) (hBi : Function.Injective B) :
    Function.Injective
      (pairedSamplingCokernelToDistributionalMeyerSpace S m hm A B hA hB) :=
  (fixedOrderMeyerLayerToDistributionalMeyerSpace_injective S m hm).comp
    (fixedOrderPairedSamplingCokernelMap_injective S m hm A B hA hB hAi hBi)

/-- Infinite actual sampling cokernel forces an infinite intrinsic layer. -/
theorem infinite_fixedOrderMeyerLayer_of_infinite_pairedSamplingCokernel
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m)
    (A : E →L[ℂ] HermiteScale (-(m : ℤ)))
    (B : F →L[ℂ] HermiteScale (-(m : ℤ)))
    (hA : A.range ≤ (fixedOrderPhysicalSupport S m hm).toSubmodule)
    (hB : B.range ≤ (fixedOrderInverseFourierSupport S m hm).toSubmodule)
    (hAi : Function.Injective A) (hBi : Function.Injective B)
    (hinf : ¬ FiniteDimensional ℂ (pairedTraceSampling A B).rangeᗮ) :
    ¬ FiniteDimensional ℂ (FixedOrderMeyerLayer S m hm) :=
  infinite_intersection_of_infinite_pairedSamplingCokernel A B _ _ hA hB hAi hBi hinf

/-- A genuine upper semi-Fredholm sampling deformation with an infinite
orthogonal cokernel at its seed gives an intrinsic supercritical certificate.
The analytic path, its common Hilbert order, and its semi-Fredholm estimates
remain explicit obligations; no finite-cokernel or frame hypothesis is added. -/
def supercriticalCertificate_of_samplingDeformation
    (S : LocallyFiniteCarrier) (m : ℕ) (hm : 1 ≤ m)
    (A : E →L[ℂ] HermiteScale (-(m : ℤ)))
    (B : F →L[ℂ] HermiteScale (-(m : ℤ)))
    (hA : A.range ≤ (fixedOrderPhysicalSupport S m hm).toSubmodule)
    (hB : B.range ≤ (fixedOrderInverseFourierSupport S m hm).toSubmodule)
    (hAi : Function.Injective A) (hBi : Function.Injective B)
    (T : HermiteScale (-(m : ℤ)) →L[ℂ] WithLp 2 (E × F))
    (p : Path T (pairedTraceSampling A B))
    (hp : ∀ t, IsUpperSemiFredholm (p t))
    (hinf : ¬ FiniteDimensional ℂ T.rangeᗮ) :
    SupercriticalEndpointCertificate S where
  order := m
  order_pos := hm
  infiniteLayer := infinite_fixedOrderMeyerLayer_of_infinite_pairedSamplingCokernel
    S m hm A B hA hB hAi hBi
      (infinite_orthogonal_coker_of_upperSemiFredholm_path p hp hinf)

end

end MeyerGeneralProblem
