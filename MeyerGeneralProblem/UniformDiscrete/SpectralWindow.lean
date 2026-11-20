module

public import MeyerGeneralProblem.Distribution.MeyerSpace
public import MeyerGeneralProblem.UniformDiscrete.FiniteRows

@[expose] public section

/-!
# A spectral gap gives a finite coordinate injection

The analytic spectral-gap uniqueness statement is an explicit hypothesis.
The passage from local atomic coefficients to vanishing on an open interval,
and then to a finite-dimensional bound for the actual distributional Meyer
space, is proved here. This file does not derive spectral-gap uniqueness
from uniform discreteness.
-/

open scoped FourierTransform SchwartzMap

namespace MeyerGeneralProblem.UniformDiscrete

noncomputable section

/-- Vanishing as a distribution on an open interval, tested only on
compactly supported Schwartz functions inside that interval. -/
def VanishesOnInterval (T : TemperedDistribution ℝ ℂ) (R : ℝ) : Prop :=
  ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport f →
    tsupport f ⊆ Set.Ioo (-R) R → T f = 0

/-- The exact analytic input used in the finite-window argument.

For a uniformly discrete carrier, an implementation of the cited
Lev--Olevskii gap theorem must supply this proposition for some positive
`R`. It is not supplied or assumed as a global instance in this module. -/
def SpectralGapUniqueness (S : LocallyFiniteCarrier) (R : ℝ) : Prop :=
  ∀ T : TemperedDistribution ℝ ℂ, HasLocallyAtomicAction S T →
    VanishesOnInterval (FourierTransform.fourier T) R → T = 0

/-- The finite set of carrier points in the closed spectral window. -/
def spectralWindow (S : LocallyFiniteCarrier) (R : ℝ) : Set ℝ :=
  S.carrier ∩ Set.Icc (-R) R

instance spectralWindow_fintype (S : LocallyFiniteCarrier) (R : ℝ) :
    Fintype (spectralWindow S R) :=
  (S.finite_inter_Icc (-R) R).fintype

/-- Extract the actual Fourier atom coefficients using the repository's
canonical isolation tests. -/
def spectralWindowMap (S : LocallyFiniteCarrier) (R : ℝ) :
    DistributionalMeyerSpace S →ₗ[ℂ] (spectralWindow S R → ℂ) where
  toFun T x := temperedFourierLinearMap (T : TemperedDistribution ℝ ℂ)
    (S.isolationSchwartz ⟨x, x.property.1⟩)
  map_add' := by
    intro T U
    funext x
    exact congrArg
      (fun V : TemperedDistribution ℝ ℂ =>
        V (S.isolationSchwartz ⟨x, x.property.1⟩))
      (map_add temperedFourierLinearMap
        (T : TemperedDistribution ℝ ℂ) (U : TemperedDistribution ℝ ℂ))
  map_smul' := by
    intro c T
    funext x
    exact congrArg
      (fun V : TemperedDistribution ℝ ℂ =>
        V (S.isolationSchwartz ⟨x, x.property.1⟩))
      (map_smul temperedFourierLinearMap c (T : TemperedDistribution ℝ ℂ))

@[simp]
theorem spectralWindowMap_apply (S : LocallyFiniteCarrier) (R : ℝ)
    (T : DistributionalMeyerSpace S) (x : spectralWindow S R) :
    spectralWindowMap S R T x =
      FourierTransform.fourier (T : TemperedDistribution ℝ ℂ)
        (S.isolationSchwartz ⟨x, x.property.1⟩) := rfl

/-- Zero atom coefficients in the closed window imply distributional
vanishing on its interior. The local finite-sum formula justifies the
implication; no interchange of an infinite sum is involved. -/
theorem vanishesOnInterval_of_coefficients_zero
    (S : LocallyFiniteCarrier) (R : ℝ)
    (T : TemperedDistribution ℝ ℂ) (hT : HasLocallyAtomicAction S T)
    (hz : ∀ x : S.subtype, (x : ℝ) ∈ Set.Icc (-R) R →
      T (S.isolationSchwartz x) = 0) :
    VanishesOnInterval T R := by
  intro f hfc hfs
  obtain ⟨a, ha⟩ := hT
  obtain ⟨E, _, hsum⟩ := ha f hfc
  rw [hsum]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : f (x : ℝ) = 0
  · rw [hx, mul_zero]
  · have hxt : (x : ℝ) ∈ tsupport f := subset_tsupport f hx
    have hxw : (x : ℝ) ∈ Set.Icc (-R) R :=
      Set.Ioo_subset_Icc_self (hfs hxt)
    have hax : a x = 0 :=
      (locallyAtomicCoefficient_eq_isolationAction S T a ha x).trans (hz x hxw)
    rw [hax, zero_mul]

/-- The finite spectral coordinate map is injective, conditional exactly
on the displayed gap-uniqueness input. -/
theorem spectralWindowMap_injective_of_gap
    (S : LocallyFiniteCarrier) (R : ℝ) (hgap : SpectralGapUniqueness S R) :
    Function.Injective (spectralWindowMap S R) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro T hT
  change spectralWindowMap S R T = 0 at hT
  change T = 0
  apply Subtype.ext
  apply hgap (T : TemperedDistribution ℝ ℂ) T.property.1
  apply vanishesOnInterval_of_coefficients_zero S R
    (FourierTransform.fourier (T : TemperedDistribution ℝ ℂ)) T.property.2
  intro x hx
  exact congrFun hT (⟨x, x.property, hx⟩ : spectralWindow S R)

/-- A gap gives finite dimension of the whole Meyer space, not merely
finite dimension of each fixed Hermite-order layer. -/
theorem finiteDimensional_of_gap
    (S : LocallyFiniteCarrier) (R : ℝ) (hgap : SpectralGapUniqueness S R) :
    FiniteDimensional ℂ (DistributionalMeyerSpace S) :=
  FiniteDimensional.of_injective (spectralWindowMap S R)
    (spectralWindowMap_injective_of_gap S R hgap)

/-- The explicit bound by the number of carrier points in the window. -/
theorem finrank_le_spectralWindow_card_of_gap
    (S : LocallyFiniteCarrier) (R : ℝ) (hgap : SpectralGapUniqueness S R) :
    Module.finrank ℂ (DistributionalMeyerSpace S) ≤
      Fintype.card (spectralWindow S R) := by
  simpa only [Module.finrank_fintype_fun_eq_card] using
    LinearMap.finrank_le_finrank_of_injective
      (spectralWindowMap_injective_of_gap S R hgap)

end

end MeyerGeneralProblem.UniformDiscrete
