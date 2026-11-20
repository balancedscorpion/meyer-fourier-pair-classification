module

public import MeyerGeneralProblem.Distribution.FiniteCombConvolutionSupport
public import MeyerGeneralProblem.Distribution.OriginalAtomicTorusPhaseFamily
public import MeyerGeneralProblem.Distribution.WeakLimitIntrinsicSupport

@[expose] public section

/-!
# Intrinsic support carriers of the original atomic phase leaves

The original physical unit-window count controls all translates.
Combining this bound with the weak phase limits constructs the actual
locally finite support carriers for the Poisson counting detector.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Distribution Filter MeasureTheory ProbabilityTheory Set UnitAddTorus
open scoped FourierTransform NNReal Topology

/-- Counts in half-open windows of any fixed length are invariant under
translating the carrier and the window together. -/
theorem LocallyFiniteCarrier.ncard_translate_inter_Ico_window
    (A : LocallyFiniteCarrier) (a r L : ℝ) :
    ((A.translate a).carrier ∩ Ico r (r + L)).ncard =
      (A.carrier ∩ Ico (r - a) (r - a + L)).ncard := by
  have hEq : (A.translate a).carrier ∩ Ico r (r + L) =
      (fun x : ℝ => a + x) '' (A.carrier ∩ Ico (r - a) (r - a + L)) := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hLeft, hRight⟩
      exact ⟨y, ⟨hy, by linarith only [hLeft], by linarith only [hRight]⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hLeft, hRight⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, by linarith only [hLeft], by linarith only [hRight]⟩
  rw [hEq, Set.ncard_image_of_injective _ (add_right_injective a)]

/-- A half-open unit count on a translated carrier is the original count
in the translated-back window. -/
theorem LocallyFiniteCarrier.ncard_translate_inter_Ico_unit
    (A : LocallyFiniteCarrier) (a r : ℝ) :
    ((A.translate a).carrier ∩ Ico r (r + 1)).ncard =
      (A.carrier ∩ Ico (r - a) (r - a + 1)).ncard :=
  A.ncard_translate_inter_Ico_window a r 1

private theorem exists_originalPhaseTranslationWithSupport
    {d : Type*} [Fintype d] (A B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ)
    (β : d → ℝ) (hLabel : ∀ x : B.subtype, torusDirectionalFrequency β (label x) = (x : ℝ))
    (hIndep : ∀ k : d → ℤ, torusDirectionalFrequency β k = 0 → k = 0)
    (N : ℕ) (μ : TemperedDistribution ℝ ℂ) (hν : 𝓕 μ ∈ stronglyTemperedAtomicAtExponent B N)
    (hμ : DistributionSupportedOn A.carrier μ) (θ : UnitAddTorus d) :
    ∃ t : ℕ → ℝ,
      (∀ f : SchwartzMap ℝ ℂ, Tendsto (fun j => combDistributionTranslation (-t j) μ f) atTop
        (𝓝 (originalPhasePhysicalRecord B label N μ hν θ f))) ∧
      ∀ j, DistributionSupportedOn (A.translate (-t j)).carrier
        (combDistributionTranslation (-t j) μ) := by
  obtain ⟨t, ht⟩ := exists_originalTranslation_seq_tendsto_originalPhasePhysicalRecord
    B label β hLabel hIndep N μ hν θ
  refine ⟨t, ht, ?_⟩
  intro j f hf hAway
  apply distributionSupportedOn_intrinsic_dsupport _ f hf
  intro x hx
  apply hAway
  rw [dsupport_combDistributionTranslation] at hx
  exact Set.image_mono (dsupport_subset_of_discrete_support A μ hμ) hx

/-- At every phase and every location, each fixed-length site-count bound
of the original physical carrier passes to the intrinsic phase support. -/
theorem finite_and_ncard_originalPhasePhysical_support_window
    {d : Type*} [Fintype d] (A B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ)
    (β : d → ℝ) (hLabel : ∀ x : B.subtype, torusDirectionalFrequency β (label x) = (x : ℝ))
    (hIndep : ∀ k : d → ℤ, torusDirectionalFrequency β k = 0 → k = 0)
    (N : ℕ) (μ : TemperedDistribution ℝ ℂ) (hν : 𝓕 μ ∈ stronglyTemperedAtomicAtExponent B N)
    (hμ : DistributionSupportedOn A.carrier μ)
    (L : ℝ) (C : ℕ) (hCount : ∀ r, (A.carrier ∩ Ico r (r + L)).ncard ≤ C)
    (θ : UnitAddTorus d) (r : ℝ) :
    let V := dsupport (originalPhasePhysicalRecord B label N μ hν θ) ∩ Ico r (r + L)
    V.Finite ∧ V.ncard ≤ C := by
  obtain ⟨t, ht, hTranslate⟩ :=
    exists_originalPhaseTranslationWithSupport A B label β hLabel hIndep N μ hν hμ θ
  exact finite_and_ncard_weakLimit_support_window
    (fun j => A.translate (-t j)) (fun j => combDistributionTranslation (-t j) μ)
    (originalPhasePhysicalRecord B label N μ hν θ) hTranslate (fun f _ => ht f) L
    (fun j a => by
      rw [LocallyFiniteCarrier.ncard_translate_inter_Ico_window]
      exact hCount _) r

/-- Every phase leaf has a locally finite intrinsic support and inherits
the original physical distinct-site count. This supplies the carriers and
compact-test support hypotheses for the original Poisson support detector. -/
theorem exists_originalPhasePhysicalRecord_supportFamily
    {d : Type*} [Fintype d] (A B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ)
    (β : d → ℝ) (hLabel : ∀ x : B.subtype, torusDirectionalFrequency β (label x) = (x : ℝ))
    (hIndep : ∀ k : d → ℤ, torusDirectionalFrequency β k = 0 → k = 0)
    (N : ℕ) (μ : TemperedDistribution ℝ ℂ) (hν : 𝓕 μ ∈ stronglyTemperedAtomicAtExponent B N)
    (hμ : DistributionSupportedOn A.carrier μ)
    {K : ℕ} (hCount : ∀ r, (A.carrier ∩ Ico r (r + 1)).ncard ≤ K) :
    let T := originalPhasePhysicalRecord B label N μ hν
    ∃ S : UnitAddTorus d → LocallyFiniteCarrier,
      (∀ θ, (S θ).carrier = dsupport (T θ)) ∧
      (∀ θ, DistributionSupportedOn (S θ).carrier (T θ)) ∧
      ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K := by
  let T := originalPhasePhysicalRecord B label N μ hν
  have hEach (θ : UnitAddTorus d) : ∃ S : LocallyFiniteCarrier,
      S.carrier = dsupport (T θ) ∧ ∀ r, (S.carrier ∩ Ico r (r + 1)).ncard ≤ K := by
    obtain ⟨t, ht, hTranslate⟩ :=
      exists_originalPhaseTranslationWithSupport A B label β hLabel hIndep N μ hν hμ θ
    exact exists_locallyFiniteCarrier_weakLimit_support
      (fun j => A.translate (-t j)) (fun j => combDistributionTranslation (-t j) μ) (T θ)
      hTranslate (fun f _ => ht f) (fun j r => by
        rw [LocallyFiniteCarrier.ncard_translate_inter_Ico_unit]
        exact hCount _)
  choose S hS hSC using hEach
  refine ⟨S, hS, fun θ => ?_, hSC⟩
  rw [hS θ]
  exact distributionSupportedOn_intrinsic_dsupport _

/-- Use normalized Haar measure on each circle factor of the original phase torus. -/
local instance originalPhaseSupportCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

/-- The true Poisson detector of the original phase leaves has a shared
strictly positive Haar mean at all positive heights. -/
theorem exists_pos_mean_originalPhasePoisson
    {d : Type*} [Fintype d] (A B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ)
    (β : d → ℝ) (hLabel : ∀ x : B.subtype, torusDirectionalFrequency β (label x) = (x : ℝ))
    (hIndep : ∀ k : d → ℤ, torusDirectionalFrequency β k = 0 → k = 0)
    (N : ℕ) (μ : TemperedDistribution ℝ ℂ) (hν : 𝓕 μ ∈ stronglyTemperedAtomicAtExponent B N)
    (hμ : DistributionSupportedOn A.carrier μ) (hNonzero : μ ≠ 0)
    {K : ℕ} (hCount : ∀ r, (A.carrier ∩ Ico r (r + 1)).ncard ≤ K) :
    ∃ m : ℝ, 0 < m ∧ ∀ y : ℝ≥0, 0 < y →
      (∫ θ : UnitAddTorus d, ∫ x, cauchyPDFReal 0 y x
        ∂discreteSupportCount (originalPhasePhysicalRecord B label N μ hν θ)) = m := by
  obtain ⟨S, _, hSupport, hSC⟩ :=
    exists_originalPhasePhysicalRecord_supportFamily A B label β hLabel hIndep N μ hν hμ hCount
  exact exists_pos_mean_poisson_discreteSupportCount β S
    (originalPhasePhysicalRecord B label N μ hν) hSupport
    (fun t θ => originalPhasePhysicalRecord_advance B label β hLabel N μ hν θ t)
    (fun f _ => continuous_originalPhasePhysicalRecord_apply B label N μ hν f)
    hSC (originalPhasePhysicalRecord_ne_zero B label N μ hν hNonzero)

end
end MeyerGeneralProblem
