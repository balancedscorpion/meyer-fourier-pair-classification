module

public import MeyerGeneralProblem.Distribution.PeriodicAtomicComb
public import MeyerGeneralProblem.Distribution.RealRootedCosetPhysicalJets

@[expose] public section

/-!
# Quasiperiodic atomic records and a single spectral coset

A single translation eigenvalue determines the phase of every affine comb.
This kernel argument uses only the physical atomic action. It can also be
applied to differences whose Fourier transforms are tempered distributions.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped SchwartzMap FourierTransform

/-- The original affine comb multiplied by the character of frequency `s`. -/
def modulatedAffineDiracComb (w : ℝ) (hw : 0 < w) (y s : ℝ) :
    TemperedDistribution ℝ ℂ :=
  combDistributionModulation s (affineDiracComb w hw y)

theorem modulatedAffineDiracComb_apply (w : ℝ) (hw : 0 < w) (y s : ℝ)
    (f : SchwartzMap ℝ ℂ) :
    modulatedAffineDiracComb w hw y s f =
      ∑' k : ℤ, combModulationCharacter s (y + (k : ℝ) * w) * f (y + (k : ℝ) * w) := by
  simp only [modulatedAffineDiracComb, combDistributionModulation_apply, affineDiracComb_apply,
    combSchwartzModulation_apply]

/-- The individual summand is spectrally supported on the full coset
`s + w⁻¹ ℤ`, with ordinary value-only atomic action. -/
theorem fourier_modulatedAffineDiracComb_atomicOnCarrier (w : ℝ) (hw : 0 < w) (y s : ℝ) :
    AtomicOnCarrier (affineDiracCombCarrier w⁻¹ (inv_pos.mpr hw) s)
      (𝓕 (modulatedAffineDiracComb w hw y s)) := by
  intro f hf
  simp only [modulatedAffineDiracComb, affineDiracComb, fourier_combDistributionModulation,
    fourier_combDistributionDilation, fourier_shiftedIntegerComb, map_smul, smul_apply,
    combDistributionTranslation_apply, combDistributionDilation_apply, modulatedIntegerComb_apply,
    combSchwartzDilation_apply, combSchwartzTranslation_apply]
  have hzero (k : ℤ) : f (s + w⁻¹ * (k : ℝ)) = 0 :=
    hf _ ((mem_affineDiracCombCarrier w⁻¹ (inv_pos.mpr hw) s _).mpr
      ⟨k, by rw [mul_comm w⁻¹]⟩)
  simp only [hzero, mul_zero, tsum_zero, smul_zero]

/-- Actual translation and modulation commute with their precise scalar. -/
theorem combDistributionTranslation_modulation (a s : ℝ) (T : TemperedDistribution ℝ ℂ) :
    combDistributionTranslation a (combDistributionModulation s T) =
      combModulationCharacter (-a) s • combDistributionModulation s
        (combDistributionTranslation a T) := by
  ext f
  simp only [combDistributionTranslation_apply, combDistributionModulation_apply, smul_apply,
    ← map_smul]
  congr 1
  ext x
  simp only [combSchwartzModulation_apply, combSchwartzTranslation_apply, _root_.smul_apply,
    smul_eq_mul, ← mul_assoc]
  congr 1
  rw [combModulationCharacter_eq_exp, combModulationCharacter_eq_exp,
    combModulationCharacter_eq_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The exact kernel for a single prescribed translation eigenvalue.
Only the original physical atomic record is used. -/
theorem exists_modulatedAffineDiracComb_sum_of_translation_eigen (A : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T) (w : ℝ) (hw : 0 < w) (s : ℝ)
    (heigen : combDistributionTranslation w T = combModulationCharacter (-w) s • T) :
    ∃ E : Finset ℝ, (∀ y, y ∈ E ↔ y ∈ A.carrier ∩ Ico 0 w) ∧
      T = ∑ y ∈ E, extendedAtomicCoefficient A (combDistributionModulation (-s) T) y •
        modulatedAffineDiracComb w hw y s := by
  let V := combDistributionModulation (-s) T
  have hV : AtomicOnCarrier A V := atomicOnCarrier_combDistributionModulation A T hT (-s)
  have hscalar : combModulationCharacter (-w) (-s) * combModulationCharacter (-w) s = 1 := by
    rw [combModulationCharacter_eq_exp, combModulationCharacter_eq_exp, ← Complex.exp_add]
    rw [show 2 * (Real.pi : ℂ) * Complex.I * ((-w : ℝ) : ℂ) * ((-s : ℝ) : ℂ) +
      2 * (Real.pi : ℂ) * Complex.I * ((-w : ℝ) : ℂ) * (s : ℂ) = 0 by push_cast; ring,
      Complex.exp_zero]
  have hperiod : combDistributionTranslation w V = V := by
    dsimp only [V]
    rw [combDistributionTranslation_modulation, heigen, map_smul, smul_smul, hscalar, one_smul]
  obtain ⟨E, hE, hsum⟩ := exists_affineDiracComb_sum_of_translation A V hV w hw hperiod
  refine ⟨E, hE, ?_⟩
  have h := congrArg (combDistributionModulation s) hsum
  simpa only [V, combDistributionModulation_neg_apply, map_sum, map_smul, modulatedAffineDiracComb]
    using h

theorem combModulationCharacter_eq_on_reciprocal_coset (w s : ℝ) (hw : 0 < w) (k : ℤ) :
    combModulationCharacter (-w) (s + (k : ℝ) * w⁻¹) = combModulationCharacter (-w) s := by
  rw [combModulationCharacter_eq_exp, combModulationCharacter_eq_exp]
  have he : 2 * (Real.pi : ℂ) * Complex.I * ((-w : ℝ) : ℂ) *
      ((s + (k : ℝ) * w⁻¹ : ℝ) : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I * ((-w : ℝ) : ℂ) * (s : ℂ) +
        ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    have hw' : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
    push_cast
    field_simp
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Fourier support in a single coset of reciprocal spacing forces the
exact translation eigenvalue on the original tempered distribution. -/
theorem combDistributionTranslation_eigen_of_spectral_coset (B : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hFT : AtomicOnCarrier B (𝓕 T)) (w : ℝ) (hw : 0 < w) (s : ℝ)
    (hB : B.carrier ⊆ (affineDiracCombCarrier w⁻¹ (inv_pos.mpr hw) s).carrier) :
    combDistributionTranslation w T = combModulationCharacter (-w) s • T := by
  apply (FourierTransform.fourierEquiv ℂ (TemperedDistribution ℝ ℂ)).injective
  change 𝓕 (combDistributionTranslation w T) = 𝓕 (combModulationCharacter (-w) s • T)
  rw [fourier_combDistributionTranslation, FourierTransform.fourier_smul]
  ext f
  rw [combDistributionModulation_apply, smul_apply, ← map_smul, ← sub_eq_zero, ← map_sub]
  apply hFT
  intro x hx
  obtain ⟨k, rfl⟩ := (mem_affineDiracCombCarrier w⁻¹ (inv_pos.mpr hw) s x).mp (hB hx)
  simp only [_root_.sub_apply, combSchwartzModulation_apply, _root_.smul_apply,
    smul_eq_mul, combModulationCharacter_eq_on_reciprocal_coset w s hw, sub_self]

/-- Complete single-coset reconstruction for the original broad pair. -/
theorem exists_modulatedAffineDiracComb_sum_of_spectral_coset (A B : LocallyFiniteCarrier)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T) (hFT : AtomicOnCarrier B (𝓕 T))
    (w : ℝ) (hw : 0 < w) (s : ℝ)
    (hB : B.carrier ⊆ (affineDiracCombCarrier w⁻¹ (inv_pos.mpr hw) s).carrier) :
    ∃ E : Finset ℝ, (∀ y, y ∈ E ↔ y ∈ A.carrier ∩ Ico 0 w) ∧
      T = ∑ y ∈ E, extendedAtomicCoefficient A (combDistributionModulation (-s) T) y •
        modulatedAffineDiracComb w hw y s :=
  exists_modulatedAffineDiracComb_sum_of_translation_eigen A T hT w hw s
    (combDistributionTranslation_eigen_of_spectral_coset B T hFT w hw s hB)

end
end MeyerGeneralProblem
