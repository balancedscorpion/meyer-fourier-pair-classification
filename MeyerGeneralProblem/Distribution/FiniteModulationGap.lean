module

public import MeyerGeneralProblem.Distribution.FiniteConvolutionCoefficients
public import MeyerGeneralProblem.UniformDiscrete.SpectralWindow

@[expose] public section

/-!
# Finite modulation matrices on the original Fourier record

The rows are all sites of the finite union of shifted spectral carriers
in the closed window. Each entry is the original coefficient at the
corresponding preimage, extended by zero. Thus the local matrix retains
all collisions and its kernel gives a genuine distributional Fourier gap.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped FourierTransform
open UniformDiscrete

private def modulationHom (a : ℝ) : Multiplicative ℝ →* ℂ where
  toFun x := combModulationCharacter a x.toAdd
  map_one' := by simp [combModulationCharacter]
  map_mul' x y := by
    change combModulationCharacter a (x.toAdd + y.toAdd) =
      combModulationCharacter a x.toAdd * combModulationCharacter a y.toAdd
    simp only [combModulationCharacter, mul_add, Real.fourierChar.map_add_eq_mul]
    rfl

private theorem modulationHom_injective : Function.Injective modulationHom := by
  intro a b hab
  by_contra h
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr h
  apply Real.fourierChar_ne_one
  apply AddChar.eq_one_iff.mpr
  intro y
  let x := y / (a - b)
  have hx : (a - b) * x = y := by
    dsimp [x]
    field_simp
  rw [sub_mul] at hx
  have hxy : a * x = b * x + y := by linarith
  have he := DFunLike.congr_fun hab (Multiplicative.ofAdd x)
  change ((Real.fourierChar (a * x)) : ℂ) = (Real.fourierChar (b * x) : ℂ) at he
  rw [hxy, Real.fourierChar.map_add_eq_mul] at he
  have he' : Real.fourierChar (b * x) * Real.fourierChar y =
      Real.fourierChar (b * x) := Subtype.ext he
  exact mul_left_cancel (he'.trans (mul_one _).symm)

/-- A nonzero coefficient vector on distinct real frequencies defines a nonzero
function. This uses Dedekind independence for actual additive characters. -/
theorem exists_eval_ne_zero_of_finiteModulation_coefficients_ne_zero
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : Function.Injective a)
    (c : ι → ℂ) (hc : c ≠ 0) :
    ∃ x : ℝ, ∑ i, c i * combModulationCharacter (a i) x ≠ 0 := by
  classical
  by_contra h
  have hli := (linearIndependent_monoidHom (Multiplicative ℝ) ℂ).comp
    (modulationHom ∘ a) (modulationHom_injective.comp ha)
  have hzero : ∑ i, c i • (modulationHom (a i) : Multiplicative ℝ → ℂ) = 0 := by
    funext x
    change (∑ i, c i • (modulationHom (a i) : Multiplicative ℝ → ℂ)) x = 0
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change (∑ i, c i * combModulationCharacter (a i) x.toAdd) = 0
    by_contra hn
    exact h ⟨x.toAdd, hn⟩
  exact hc (funext (Fintype.linearIndependent_iff.mp hli c hzero))

/-- The complete coefficient map of a finite modulation menu in a window. -/
def finiteModulationWindowMap {ι : Type*} [Fintype ι]
    (B : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ) (a : ι → ℝ) (R : ℝ) :
    (ι → ℂ) →ₗ[ℂ] (spectralWindow (finiteCombConvolutionCarrier B a) R → ℂ) where
  toFun c x := ∑ i, c i * extendedAtomicCoefficient B T ((x : ℝ) - a i)
  map_add' c d := by
    funext x
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' z c := by
    funext x
    simp [mul_assoc, Finset.mul_sum]

/-- A kernel vector kills the original spectral convolution on the open
window. The finite local atomic formula covers every Schwartz test there. -/
theorem vanishesOnInterval_finiteCombConvolution_of_windowMap_eq_zero
    {ι : Type*} [Fintype ι] (B : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : AtomicOnCarrier B T) (a : ι → ℝ) (c : ι → ℂ) (R : ℝ)
    (hc : finiteModulationWindowMap B T a R c = 0) :
    VanishesOnInterval (finiteCombConvolution a c T) R := by
  apply vanishesOnInterval_of_coefficients_zero
  · exact hasLocallyAtomicAction_finiteCombConvolution B T
      (atomicOnCarrier_hasLocallyAtomicAction B T hT) a c
  · intro x hx
    rw [finiteCombConvolution_isolation_apply B T hT a c x]
    exact congrFun hc ⟨x, x.property, hx⟩

/-- A strict deficit of actual rows relative to modulation columns gives a
nonzero coefficient vector whose modulated source has a genuine Fourier gap. -/
theorem exists_finiteModulation_fourierGap_of_card_lt
    {ι : Type*} [Fintype ι] (B : LocallyFiniteCarrier) (U : TemperedDistribution ℝ ℂ)
    (hB : AtomicOnCarrier B (𝓕 U)) (a : ι → ℝ) (R : ℝ)
    (hcard : Fintype.card (spectralWindow (finiteCombConvolutionCarrier B a) R) <
      Fintype.card ι) :
    ∃ c : ι → ℂ, c ≠ 0 ∧
      VanishesOnInterval (𝓕 (finiteExponentialMultiplication a c U)) R := by
  classical
  let F := finiteModulationWindowMap B (𝓕 U) a R
  have hker : ∃ c, c ≠ 0 ∧ F c = 0 := by
    by_contra h
    have hinj : Function.Injective F := by
      apply LinearMap.ker_eq_bot.mp
      apply le_antisymm ?_ bot_le
      intro c hc
      by_contra hne
      exact h ⟨c, hne, hc⟩
    have hdim := LinearMap.finrank_le_finrank_of_injective hinj
    simp only [Module.finrank_fintype_fun_eq_card] at hdim
    exact (not_lt_of_ge hdim) hcard
  obtain ⟨c, hc, hz⟩ := hker
  refine ⟨c, hc, ?_⟩
  rw [fourier_finiteExponentialMultiplication]
  exact vanishesOnInterval_finiteCombConvolution_of_windowMap_eq_zero B _ hB a c R hz

/-- A detector for the physical carrier promotes the exact matrix kernel
from local Fourier vanishing to annihilation of the whole original source. -/
theorem exists_finiteModulation_eq_zero_of_card_lt_of_gap
    {ι : Type*} [Fintype ι] (A B : LocallyFiniteCarrier) (U : TemperedDistribution ℝ ℂ)
    (hA : AtomicOnCarrier A U) (hB : AtomicOnCarrier B (𝓕 U)) (a : ι → ℝ) (R : ℝ)
    (hgap : SpectralGapUniqueness A R)
    (hcard : Fintype.card (spectralWindow (finiteCombConvolutionCarrier B a) R) <
      Fintype.card ι) :
    ∃ c : ι → ℂ, c ≠ 0 ∧ finiteExponentialMultiplication a c U = 0 := by
  obtain ⟨c, hc, hvan⟩ := exists_finiteModulation_fourierGap_of_card_lt B U hB a R hcard
  refine ⟨c, hc, hgap _ (atomicOnCarrier_hasLocallyAtomicAction A _ ?_) hvan⟩
  intro f hf
  rw [finiteExponentialMultiplication_apply]
  apply hA
  intro x hx
  rw [finiteCombSchwartzSymbol_apply, hf x hx, mul_zero]

end

end MeyerGeneralProblem
