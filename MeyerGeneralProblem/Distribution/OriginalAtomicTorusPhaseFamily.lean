module

public import MeyerGeneralProblem.Cardinal.Adaptive.TorusFlowDensity
public import MeyerGeneralProblem.Distribution.OriginalStrongEvaluation
public import MeyerGeneralProblem.Distribution.TorusPoissonFourierMultiplier
public import Mathlib.Analysis.Normed.Group.Tannery

@[expose] public section

/-!
# The original atomic Fourier phase family

An absolutely weighted original Fourier record can be twisted on the
finite phase torus. This constructs the weakly continuous physical
family with the original Fourier weights, the zero-phase identity,
actual translation covariance and nonzero phase leaves.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Distribution Filter Set UnitAddTorus
open scoped FourierTransform SchwartzMap Topology

variable {d : Type*} [Fintype d]

private theorem norm_phaseCharacter (n : d → ℤ) (θ : UnitAddTorus d) :
    ‖mFourier n θ‖ = 1 := by
  simp only [mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply,
    Circle.norm_coe, Finset.prod_const_one]

private theorem phaseCharacter_at_zero (n : d → ℤ) :
    mFourier n (0 : UnitAddTorus d) = 1 := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.zero_apply, fourier_eval_zero, Finset.prod_const_one]

/-- The original weighted Fourier atom at a phase has the same mass modulus. -/
def phaseAtomicCoefficient (B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ)
    (ν : TemperedDistribution ℝ ℂ) (θ : UnitAddTorus d) (x : B.subtype) : ℂ :=
  mFourier (label x) θ * ν (B.isolationSchwartz x)

/-- The original absolute spectral weight remains summable in every phase. -/
theorem phaseAtomicCoefficient_weight_summable (B : LocallyFiniteCarrier)
    (label : B.subtype → d → ℤ) (N : ℕ) (ν : TemperedDistribution ℝ ℂ)
    (hν : ν ∈ stronglyTemperedAtomicAtExponent B N) (θ : UnitAddTorus d) :
    Summable (weightedAtomicMassTerm B (phaseAtomicCoefficient B label ν θ) N) := by
  have hEq : weightedAtomicMassTerm B (phaseAtomicCoefficient B label ν θ) N =
      weightedAtomicMassTerm B (fun x => ν (B.isolationSchwartz x)) N := by
    funext x
    simp only [weightedAtomicMassTerm, phaseAtomicCoefficient, norm_mul, norm_phaseCharacter, one_mul]
  rw [hEq]
  exact hν.2

/-- The actual weighted atomic Fourier record with original coefficients twisted
by their torus characters. The weight bound comes from the original record. -/
def originalPhaseSpectralRecord (B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ)
    (N : ℕ) (ν : TemperedDistribution ℝ ℂ) (hν : ν ∈ stronglyTemperedAtomicAtExponent B N)
    (θ : UnitAddTorus d) : TemperedDistribution ℝ ℂ :=
  weightedAtomicDistribution B (phaseAtomicCoefficient B label ν θ) N
    (phaseAtomicCoefficient_weight_summable B label N ν hν θ)

/-- The physical phase family is the inverse Fourier transform of the original twisted record. -/
def originalPhasePhysicalRecord (B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ)
    (N : ℕ) (μ : TemperedDistribution ℝ ℂ) (hν : 𝓕 μ ∈ stronglyTemperedAtomicAtExponent B N)
    (θ : UnitAddTorus d) : TemperedDistribution ℝ ℂ :=
  𝓕⁻ (originalPhaseSpectralRecord B label N (𝓕 μ) hν θ)

/-- Pointwise continuity on each Schwartz test of the original twisted Fourier records. -/
theorem continuous_originalPhaseSpectralRecord_apply
    (B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ)
    (N : ℕ) (ν : TemperedDistribution ℝ ℂ) (hν : ν ∈ stronglyTemperedAtomicAtExponent B N)
    (f : SchwartzMap ℝ ℂ) :
    Continuous (fun θ : UnitAddTorus d => originalPhaseSpectralRecord B label N ν hν θ f) := by
  simp only [originalPhaseSpectralRecord, weightedAtomicDistribution_apply]
  refine continuous_iff_continuousAt.mpr fun θ => ?_
  exact tendsto_tsum_of_dominated_convergence
    (weightedAtomic_samples_summable B (fun x => ν (B.isolationSchwartz x)) N hν.2 f).norm
    (fun x => (((mFourier (label x)).continuous.mul continuous_const).mul continuous_const).tendsto θ)
    (Eventually.of_forall fun φ x => by
      rw [phaseAtomicCoefficient, mul_assoc, norm_mul, norm_phaseCharacter, one_mul])

/-- Weak continuity of the actual physical family on every Schwartz test. -/
theorem continuous_originalPhasePhysicalRecord_apply
    (B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ)
    (N : ℕ) (μ : TemperedDistribution ℝ ℂ) (hν : 𝓕 μ ∈ stronglyTemperedAtomicAtExponent B N)
    (f : SchwartzMap ℝ ℂ) :
    Continuous (fun θ : UnitAddTorus d => originalPhasePhysicalRecord B label N μ hν θ f) := by
  simp only [originalPhasePhysicalRecord, TemperedDistribution.fourierInv_apply]
  exact continuous_originalPhaseSpectralRecord_apply B label N (𝓕 μ) hν (𝓕⁻ f)

/-- The zero phase of the twisted Fourier family is the original Fourier record. -/
theorem originalPhaseSpectralRecord_zero
    (B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ)
    (N : ℕ) (ν : TemperedDistribution ℝ ℂ) (hν : ν ∈ stronglyTemperedAtomicAtExponent B N) :
    originalPhaseSpectralRecord B label N ν hν 0 = ν := by
  ext f
  simp only [originalPhaseSpectralRecord, weightedAtomicDistribution_apply, phaseAtomicCoefficient,
    phaseCharacter_at_zero, one_mul]
  exact (stronglyTemperedAtomicAtExponent_apply_tsum B N ν hν f).symm

/-- The zero phase is the original physical record. -/
theorem originalPhasePhysicalRecord_zero
    (B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ)
    (N : ℕ) (μ : TemperedDistribution ℝ ℂ) (hν : 𝓕 μ ∈ stronglyTemperedAtomicAtExponent B N) :
    originalPhasePhysicalRecord B label N μ hν 0 = μ := by
  rw [originalPhasePhysicalRecord, originalPhaseSpectralRecord_zero,
    FourierTransform.fourierInv_fourier_eq]

/-- Phase advance multiplies the original Fourier record by the physical modulation
character, with the exact original atom coordinates. -/
theorem originalPhaseSpectralRecord_advance
    (B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ) (β : d → ℝ)
    (hLabel : ∀ x : B.subtype, torusDirectionalFrequency β (label x) = (x : ℝ))
    (N : ℕ) (ν : TemperedDistribution ℝ ℂ) (hν : ν ∈ stronglyTemperedAtomicAtExponent B N)
    (θ : UnitAddTorus d) (t : ℝ) :
    originalPhaseSpectralRecord B label N ν hν (unitAddTorusFlow β t θ) =
      combDistributionModulation t (originalPhaseSpectralRecord B label N ν hν θ) := by
  ext f
  simp only [originalPhaseSpectralRecord, combDistributionModulation_apply,
    weightedAtomicDistribution_apply, phaseAtomicCoefficient, mFourier_unitAddTorusFlow,
    hLabel, combSchwartzModulation_apply]
  apply tsum_congr
  intro x
  have hChar : combModulationCharacter (x : ℝ) t = combModulationCharacter t x := by
    simp only [combModulationCharacter, mul_comm (x : ℝ) t]
  rw [hChar]
  ring

/-- Phase advance is exactly the original physical translation on every leaf. -/
theorem originalPhasePhysicalRecord_advance
    (B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ) (β : d → ℝ)
    (hLabel : ∀ x : B.subtype, torusDirectionalFrequency β (label x) = (x : ℝ))
    (N : ℕ) (μ : TemperedDistribution ℝ ℂ) (hν : 𝓕 μ ∈ stronglyTemperedAtomicAtExponent B N)
    (θ : UnitAddTorus d) (t : ℝ) :
    originalPhasePhysicalRecord B label N μ hν (unitAddTorusFlow β t θ) =
      combDistributionTranslation (-t) (originalPhasePhysicalRecord B label N μ hν θ) := by
  have h := originalPhaseSpectralRecord_advance B label β hLabel N (𝓕 μ) hν θ t
  have hF : 𝓕 (originalPhasePhysicalRecord B label N μ hν (unitAddTorusFlow β t θ)) =
      𝓕 (combDistributionTranslation (-t) (originalPhasePhysicalRecord B label N μ hν θ)) := by
    simpa only [originalPhasePhysicalRecord, fourier_combDistributionTranslation, neg_neg,
      FourierTransform.fourier_fourierInv_eq] using h
  simpa only [FourierTransform.fourierInv_fourier_eq] using
    congrArg (fun D : TemperedDistribution ℝ ℂ => 𝓕⁻ D) hF

/-- A nonzero original Fourier record gives a nonzero twisted record at every phase. -/
theorem originalPhaseSpectralRecord_ne_zero
    (B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ)
    (N : ℕ) (ν : TemperedDistribution ℝ ℂ) (hν : ν ∈ stronglyTemperedAtomicAtExponent B N)
    (hNonzero : ν ≠ 0) (θ : UnitAddTorus d) :
    originalPhaseSpectralRecord B label N ν hν θ ≠ 0 := by
  obtain ⟨x, hx⟩ := locallyAtomic_exists_isolationAction_ne_zero B ν hν.1 hNonzero
  intro h
  have hx' := congrArg (fun D : TemperedDistribution ℝ ℂ => D (B.isolationSchwartz x)) h
  change originalPhaseSpectralRecord B label N ν hν θ (B.isolationSchwartz x) = 0 at hx'
  simp only [originalPhaseSpectralRecord, weightedAtomicDistribution_isolation,
    phaseAtomicCoefficient] at hx'
  exact (mul_ne_zero (norm_ne_zero_iff.mp (by rw [norm_phaseCharacter]; exact one_ne_zero)) hx) hx'

/-- A nonzero original physical record gives a nonzero distribution on every phase leaf. -/
theorem originalPhasePhysicalRecord_ne_zero
    (B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ)
    (N : ℕ) (μ : TemperedDistribution ℝ ℂ) (hν : 𝓕 μ ∈ stronglyTemperedAtomicAtExponent B N)
    (hNonzero : μ ≠ 0) (θ : UnitAddTorus d) :
    originalPhasePhysicalRecord B label N μ hν θ ≠ 0 := by
  have hF : 𝓕 μ ≠ 0 := by
    intro h
    apply hNonzero
    simpa only [FourierTransform.fourierInv_fourier_eq, FourierTransform.fourierInv_zero] using
      congrArg (fun D : TemperedDistribution ℝ ℂ => 𝓕⁻ D) h
  intro h
  apply originalPhaseSpectralRecord_ne_zero B label N (𝓕 μ) hν hF θ
  simpa only [originalPhasePhysicalRecord, FourierTransform.fourier_fourierInv_eq,
    FourierTransform.fourier_zero] using congrArg (fun D : TemperedDistribution ℝ ℂ => 𝓕 D) h

/-- A common Schwartz bound for the whole physical phase family, with the
original spectral variation and the same weight exponent at every phase. -/
theorem norm_originalPhasePhysicalRecord_apply_le
    (B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ)
    (N : ℕ) (μ : TemperedDistribution ℝ ℂ) (hν : 𝓕 μ ∈ stronglyTemperedAtomicAtExponent B N)
    (θ : UnitAddTorus d) (f : SchwartzMap ℝ ℂ) :
    ‖originalPhasePhysicalRecord B label N μ hν θ f‖ ≤
      (2 ^ N * ∑' x : B.subtype, stronglyTemperedCoefficientTerm B N (𝓕 μ) x) *
        (Finset.Iic (N, 0)).sup (schwartzSeminormFamily ℂ ℝ ℂ) (𝓕⁻ f) := by
  rw [originalPhasePhysicalRecord, TemperedDistribution.fourierInv_apply,
    originalPhaseSpectralRecord, weightedAtomicDistribution_apply]
  have h := weightedAtomic_sum_norm_le B (phaseAtomicCoefficient B label (𝓕 μ) θ) N
    (phaseAtomicCoefficient_weight_summable B label N (𝓕 μ) hν θ) (𝓕⁻ f)
  simpa only [weightedAtomicMassTerm, phaseAtomicCoefficient, stronglyTemperedCoefficientTerm,
    norm_mul, norm_phaseCharacter, one_mul] using h

/-- With rationally independent flow frequencies, each original phase leaf
is a weak limit of translations of the original physical record. A single
sequence converges on all Schwartz tests. -/
theorem exists_originalTranslation_seq_tendsto_originalPhasePhysicalRecord
    (B : LocallyFiniteCarrier) (label : B.subtype → d → ℤ) (β : d → ℝ)
    (hLabel : ∀ x : B.subtype, torusDirectionalFrequency β (label x) = (x : ℝ))
    (hIndep : ∀ k : d → ℤ, torusDirectionalFrequency β k = 0 → k = 0)
    (N : ℕ) (μ : TemperedDistribution ℝ ℂ) (hν : 𝓕 μ ∈ stronglyTemperedAtomicAtExponent B N)
    (θ : UnitAddTorus d) :
    ∃ t : ℕ → ℝ, ∀ f : SchwartzMap ℝ ℂ,
      Tendsto (fun j => combDistributionTranslation (-t j) μ f) atTop
        (𝓝 (originalPhasePhysicalRecord B label N μ hν θ f)) := by
  have hDense := torusLinearFlow_denseRange β hIndep
  obtain ⟨u, hu, hLimit⟩ := mem_closure_iff_seq_limit.mp (hDense θ)
  choose t ht using hu
  have hFlow (s : ℝ) : unitAddTorusFlow β s 0 = torusLinearFlow β s := by
    funext i
    simp only [unitAddTorusFlow, Pi.zero_apply, zero_add, torusLinearFlow,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk, mul_comm (β i) s]
  have hTranslate (j : ℕ) : originalPhasePhysicalRecord B label N μ hν (u j) =
      combDistributionTranslation (-t j) μ := by
    rw [← ht j, ← hFlow, originalPhasePhysicalRecord_advance B label β hLabel,
      originalPhasePhysicalRecord_zero]
  refine ⟨t, fun f => ?_⟩
  have hWeak := (continuous_originalPhasePhysicalRecord_apply B label N μ hν f).continuousAt.tendsto.comp hLimit
  simpa only [Function.comp_def, hTranslate] using hWeak

end
end MeyerGeneralProblem
