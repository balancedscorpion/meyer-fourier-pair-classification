module

public import MeyerGeneralProblem.Distribution.OriginalGapOscillation
public import MeyerGeneralProblem.Distribution.LatticeSlabModulation

@[expose] public section

/-!
# Classification from finite lower linear density on one ray

The original value-only pair supplies its own Fourier-gap detector.
The finite modulation matrix and the quadratic-gap comb extraction can
therefore be used without a supplied gap or structural certificate.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter Set
open scoped FourierTransform

/-- One finite lower ray count gives a nonzero exponential polynomial
annihilating the entire physical record of an original broad pair. -/
theorem exists_finiteExponentialAnnihilator_of_finite_lower_ray_count
    (A B : LocallyFiniteCarrier) (positive : Bool)
    (hCount : HasFiniteLowerRayCount A positive) (U : TemperedDistribution ℝ ℂ)
    (hA : AtomicOnCarrier A U) (hB : AtomicOnCarrier B (𝓕 U)) :
    ∃ (ι : Type) (inst : Fintype ι), letI := inst
      ∃ (a : ι → ℝ) (c : ι → ℂ), Function.Injective a ∧
        (∃ x : ℝ, ∑ i, c i * combModulationCharacter (a i) x ≠ 0) ∧
        finiteExponentialMultiplication a c U = 0 := by
  obtain ⟨J, hJ, hGap⟩ :=
    exists_spectralGapUniqueness_of_finite_lower_ray_count atomicFourierGapRayLowerBound A positive hCount
  exact exists_finiteExponentialAnnihilator_of_spectralGapUniqueness_via_latticeSlabs
    A B U hA hB hJ (lt_add_of_pos_right J zero_lt_one) hGap

/-- One finite lower ray count and opposite quadratic lower density
zero imply finite modulated Dirac comb sums on both records. -/
theorem finiteModulatedDiracCombSum_pair_of_finite_lower_ray_count
    (A B : LocallyFiniteCarrier) (positive : Bool)
    (hCount : HasFiniteLowerRayCount A positive) (T : TemperedDistribution ℝ ℂ)
    (hA : AtomicOnCarrier A T) (hB : AtomicOnCarrier B (𝓕 T))
    (hActual : ∀ x : A.subtype, T (A.isolationSchwartz x) ≠ 0)
    (hQuadratic : ∀ c : ℝ, 0 < c → ∃ᶠ r : ℝ in atTop,
      ((B.carrier ∩ Icc (-r) r).ncard : ℝ) < c * r ^ 2) :
    IsFiniteModulatedDiracCombSum T ∧ IsFiniteModulatedDiracCombSum (𝓕 T) := by
  obtain ⟨ι, inst, a, c, ha, hNonzero, hz⟩ :=
    exists_finiteExponentialAnnihilator_of_finite_lower_ray_count A B positive hCount T hA hB
  let _ := inst
  exact finiteModulatedDiracCombSum_pair_of_annihilator A B T hA hB hActual a c ha hNonzero hz hQuadratic

/-- The finite lower ray hypothesis may instead be on the original
Fourier record, with quadratic lower density zero on the physical record. -/
theorem finiteModulatedDiracCombSum_pair_of_fourier_finite_lower_ray_count
    (A B : LocallyFiniteCarrier) (positive : Bool)
    (hCount : HasFiniteLowerRayCount B positive) (T : TemperedDistribution ℝ ℂ)
    (hA : AtomicOnCarrier A T) (hB : AtomicOnCarrier B (𝓕 T))
    (hActual : ∀ x : B.subtype, (𝓕 T) (B.isolationSchwartz x) ≠ 0)
    (hQuadratic : ∀ c : ℝ, 0 < c → ∃ᶠ r : ℝ in atTop,
      ((A.carrier ∩ Icc (-r) r).ncard : ℝ) < c * r ^ 2) :
    IsFiniteModulatedDiracCombSum T ∧ IsFiniteModulatedDiracCombSum (𝓕 T) := by
  have hFFT : AtomicOnCarrier A.reflect (𝓕 (𝓕 T)) := by
    rw [fourier_fourier_eq_originalDistributionReflection]
    exact atomicOnCarrier_originalDistributionReflection A T hA
  have hComb := finiteModulatedDiracCombSum_pair_of_finite_lower_ray_count
    B A.reflect positive hCount (𝓕 T) hB hFFT hActual
    (by simpa only [centeredCount_reflect] using hQuadratic)
  exact ⟨hComb.1.of_fourier, hComb.1⟩

/-- A noncomb pair with joint subquadratic centered counts has
divergent linear counts on all four original rays. -/
theorem tendsto_four_original_ray_counts_of_joint_subquadratic_noncomb_pair
    (A B : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hA : AtomicOnCarrier A T) (hB : AtomicOnCarrier B (𝓕 T))
    (hActualA : ∀ x : A.subtype, T (A.isolationSchwartz x) ≠ 0)
    (hActualB : ∀ x : B.subtype, (𝓕 T) (B.isolationSchwartz x) ≠ 0)
    (hNotComb : ¬ IsFiniteModulatedDiracCombSum T)
    (hJoint : Asymptotics.IsLittleO atTop
      (fun r : ℝ => ((A.carrier ∩ Icc (-r) r).ncard : ℝ) + ((B.carrier ∩ Icc (-r) r).ncard : ℝ))
      (fun r : ℝ => r ^ 2)) :
    (∀ positive : Bool, Tendsto (fun r : ℝ => (originalRayCount A positive r : ℝ) / r) atTop atTop) ∧
    (∀ positive : Bool, Tendsto (fun r : ℝ => (originalRayCount B positive r : ℝ) / r) atTop atTop) :=
  tendsto_four_ray_counts_of_joint_subquadratic_noncomb_pair
    atomicFourierGapRayLowerBound A B T hA hB hActualA hActualB hNotComb hJoint

end
end MeyerGeneralProblem
