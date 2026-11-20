module

public import MeyerGeneralProblem.UniformDiscrete.RelativeSeparationGap

@[expose] public section

/-!
# Broad Fourier pairs on two separate carriers

Membership uses the original value-only atomic records. A fixed Fourier
window detects the entire pair space when the physical carrier has
bounded local counts, with only local finiteness on the spectral side.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped FourierTransform
open UniformDiscrete

/-- The complete broad space with physical carrier `A` and spectral carrier `B`. -/
def DistributionalMeyerPairSpace (A B : LocallyFiniteCarrier) :
    Submodule ℂ (TemperedDistribution ℝ ℂ) :=
  schwartzAnnihilator (schwartzVanishingSubmodule A) ⊓
    (schwartzAnnihilator (schwartzVanishingSubmodule B)).comap temperedFourierLinearMap

@[simp]
theorem mem_distributionalMeyerPairSpace_iff (A B : LocallyFiniteCarrier)
    (U : TemperedDistribution ℝ ℂ) :
    U ∈ DistributionalMeyerPairSpace A B ↔ AtomicOnCarrier A U ∧ AtomicOnCarrier B (𝓕 U) :=
  Iff.rfl

theorem distributionalMeyerPairSpace_diagonal (A : LocallyFiniteCarrier) :
    DistributionalMeyerPairSpace A A = DistributionalMeyerSpace A := by
  ext U
  rw [mem_distributionalMeyerPairSpace_iff, mem_distributionalMeyerSpace_iff,
    atomicOnCarrier_iff_hasLocallyAtomicAction, atomicOnCarrier_iff_hasLocallyAtomicAction]

/-- The actual coefficient measured by the carrier isolation test. -/
def atomicCoefficientLinearMap (A : LocallyFiniteCarrier) (x : A.subtype) :
    TemperedDistribution ℝ ℂ →ₗ[ℂ] ℂ where
  toFun U := U (A.isolationSchwartz x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Opposite-record coefficients of the original broad pair in a fixed window. -/
def pairSpectralWindowMap (A B : LocallyFiniteCarrier) (R : ℝ) :
    DistributionalMeyerPairSpace A B →ₗ[ℂ] (spectralWindow B R → ℂ) :=
  LinearMap.pi fun x =>
    (atomicCoefficientLinearMap B ⟨x, x.property.1⟩).comp
      (temperedFourierLinearMap.comp (DistributionalMeyerPairSpace A B).subtype)

theorem pairSpectralWindowMap_injective_of_gap (A B : LocallyFiniteCarrier)
    (R : ℝ) (hgap : SpectralGapUniqueness A R) :
    Function.Injective (pairSpectralWindowMap A B R) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro U hU
  change pairSpectralWindowMap A B R U = 0 at hU
  change U = 0
  apply Subtype.ext
  change (U : TemperedDistribution ℝ ℂ) = 0
  have hpair := (mem_distributionalMeyerPairSpace_iff A B _).mp U.property
  apply hgap _ (atomicOnCarrier_hasLocallyAtomicAction A _ hpair.1)
  apply vanishesOnInterval_of_coefficients_zero B R _
    (atomicOnCarrier_hasLocallyAtomicAction B _ hpair.2)
  intro x hx
  exact congrFun hU ⟨x, x.property, hx⟩

/-- One relatively separated side suffices for finite dimension of the
whole broad pair space. No uniform separation or variation bound is used. -/
theorem finiteDimensional_distributionalMeyerPairSpace_of_unitCellBound
    (A B : LocallyFiniteCarrier) (K : ℕ) (hK : UnitCellBound A K) :
    FiniteDimensional ℂ (DistributionalMeyerPairSpace A B) := by
  obtain ⟨R, _, hgap⟩ := exists_spectralGapUniqueness_of_unitCellBound A K hK
  exact FiniteDimensional.of_injective (pairSpectralWindowMap A B R)
    (pairSpectralWindowMap_injective_of_gap A B R hgap)

end

end MeyerGeneralProblem
