module

public import MeyerGeneralProblem.Distribution.ModuleAtomicAnnihilation
public import MeyerGeneralProblem.Distribution.FiniteModulationMenu

@[expose] public section

/-!
# Descend a finite annihilator to the original spectral module

Each coset of the module in the modulation menu gives a separate
coefficient equation, because its convolution lives in that coset.
Retain a coset with a nonzero coefficient and translate it to the module.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped FourierTransform

set_option maxHeartbeats 800000 in
/-- An annihilator of an actual atomic Fourier pair can be chosen with
frequencies in any additive subgroup containing the spectral carrier.
No discreteness or generation condition on the subgroup is needed. -/
theorem exists_finiteExponentialAnnihilator_in_module_of_annihilated
    {ι : Type} [Fintype ι] (B : LocallyFiniteCarrier) (H : AddSubgroup ℝ)
    (hH : B.carrier ⊆ H) (U : TemperedDistribution ℝ ℂ)
    (hB : AtomicOnCarrier B (𝓕 U)) (a : ι → ℝ) (c : ι → ℂ)
    (ha : Function.Injective a) (hc : c ≠ 0)
    (hz : finiteExponentialMultiplication a c U = 0) :
    ∃ (κ : Type) (f : Fintype κ), letI := f
      ∃ (b : κ → ℝ) (d : κ → ℂ), Function.Injective b ∧
        (∀ i, b i ∈ H) ∧ d ≠ 0 ∧ finiteExponentialMultiplication b d U = 0 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  let κ := {i : ι // a i - a j ∈ H}
  let b (i : κ) : H := ⟨a i - a j, i.property⟩
  let d (i : κ) := c i
  let f : Fintype κ := inferInstance
  have hne : d ≠ 0 := fun h => hj (congrFun h ⟨j, by simp⟩)
  have hbi : Function.Injective (fun i : κ => (b i : ℝ)) := by
    intro i k hik
    apply Subtype.ext
    apply ha
    change a i - a j = a k - a j at hik
    linarith
  have hold : finiteCombConvolution a c (𝓕 U) = 0 := by
    rw [← fourier_finiteExponentialMultiplication, hz, FourierTransform.fourier_zero]
  have hrow (x : ℝ) :
      ∑ i, c i * extendedAtomicCoefficient B (𝓕 U) (x - a i) = 0 := by
    rw [← extendedAtomicCoefficient_finiteCombConvolution B (𝓕 U) hB a c x, hold]
    unfold extendedAtomicCoefficient
    split_ifs <;> simp
  have hoff (x : ℝ) (hx : x ∉ H) : extendedAtomicCoefficient B (𝓕 U) x = 0 := by
    unfold extendedAtomicCoefficient
    exact dite_eq_right (fun hb => hx (hH hb))
  have hrec (x : H) :
      ∑ i : κ, d i * extendedAtomicCoefficient B (𝓕 U) (↑(x - b i) : ℝ) = 0 := by
    have harg (i : κ) : (↑(x - b i) : ℝ) = (x : ℝ) + a j - a i := by
      change (x : ℝ) - (a i - a j) = _
      ring
    simp only [harg, d]
    rw [← Finset.sum_subtype (Finset.univ.filter fun i => a i - a j ∈ H)
      (fun i => by simp) (fun i => c i * extendedAtomicCoefficient B (𝓕 U) (↑x + a j - a i))]
    calc
      _ = ∑ i, c i * extendedAtomicCoefficient B (𝓕 U) (↑x + a j - a i) := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i _ hi
        have hnot : a i - a j ∉ H := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        have hx : (x : ℝ) + a j - a i ∉ H := by
          intro hx
          apply hnot
          convert H.sub_mem x.property hx using 1
          ring
        rw [hoff _ hx, mul_zero]
      _ = 0 := hrow ((x : ℝ) + a j)
  have hzero := finiteCombConvolution_eq_zero_of_module_recurrence B H.subtype b d (𝓕 U) hB
    (fun x hx => hoff x (fun h => hx ⟨⟨x, h⟩, rfl⟩)) hrec
  have hfourier : 𝓕 (finiteExponentialMultiplication (fun i : κ => (b i : ℝ)) d U) = 0 := by
    rw [fourier_finiteExponentialMultiplication]
    exact hzero
  exact ⟨κ, f, (fun i => (b i : ℝ)), d, hbi, (fun i => (b i).property), hne,
    by simpa only [FourierTransform.fourierInv_fourier_eq, FourierTransform.fourierInv_zero]
      using congrArg FourierTransform.fourierInv hfourier⟩

end

end MeyerGeneralProblem
