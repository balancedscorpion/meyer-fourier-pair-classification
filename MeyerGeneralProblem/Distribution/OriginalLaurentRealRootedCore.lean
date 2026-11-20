module

public import MeyerGeneralProblem.Distribution.AtomicConvolutionNumerator
public import MeyerGeneralProblem.Distribution.CommonPairAnnihilator
public import MeyerGeneralProblem.Distribution.LaurentRecurrenceFactorCancellation
public import MeyerGeneralProblem.Distribution.OriginalLaurentRealRootedFactor

@[expose] public section

/-!
# Restriction to the common real-rooted zero carrier

The reduced recurrence holds on the original complete Fourier array.
The corresponding finite convolution is zero on every Schwartz test,
forcing the original physical coefficients outside the reduced zero
carrier to vanish.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set
open scoped FourierTransform

variable {G ι : Type*} [AddCommGroup G] [Fintype ι]

/-- The original physical carrier restricted to the zeros of the
literal Laurent symbol. -/
def annihilatorZeroSubcarrier (L : G →+ ℝ) (p : G →₀ ℂ) (A : LocallyFiniteCarrier) :
    LocallyFiniteCarrier :=
  A.restrict {x | x ∈ A.carrier ∧ annihilatorExponentialSymbol L p x = 0}
    (fun _ hx => hx.1)

/-- The spectral recurrence implies physical vanishing at each
original site where the literal annihilator symbol is nonzero. -/
theorem originalPair_atomicOn_zeroSubcarrier_of_arrayRecurrence
    (L : G →+ ℝ) (hL : Function.Injective L) (p : AddMonoidAlgebra ℂ G)
    (A B : LocallyFiniteCarrier) (hB : B.carrier ⊆ range L)
    (T : TemperedDistribution ℝ ℂ) (hT : AtomicOnCarrier A T)
    (hFT : AtomicOnCarrier B (𝓕 T))
    (hrec : ∀ n, annihilatorArrayConvolution p.coeff (originalFourierArray L B T) n = 0) :
    AtomicOnCarrier (annihilatorZeroSubcarrier L p.coeff A) T := by
  classical
  let a : p.coeff.support → ℝ := fun m => L m
  let c : p.coeff.support → ℂ := fun m => p.coeff m
  have hrec' (n : G) : annihilatorArrayConvolution p.coeff
      (fun m => extendedAtomicCoefficient B (𝓕 T) (L m)) n = (0 : AddMonoidAlgebra ℂ G).coeff n := by
    change annihilatorArrayConvolution p.coeff (originalFourierArray L B T) n = 0
    exact hrec n
  have hmul : finiteExponentialMultiplication a c T = 0 := by
    apply (FourierTransform.fourierEquiv ℂ (TemperedDistribution ℝ ℂ)).injective
    change 𝓕 (finiteExponentialMultiplication a c T) = 𝓕 (0 : TemperedDistribution ℝ ℂ)
    have hzero : 𝓕 (0 : TemperedDistribution ℝ ℂ) = 0 := map_zero temperedFourierLinearMap
    rw [fourier_finiteExponentialMultiplication, hzero]
    ext f
    change finiteCombConvolution (fun m : p.coeff.support => L m)
      (fun m : p.coeff.support => p.coeff m) (𝓕 T) f = 0
    rw [finiteCombConvolution_apply_of_module_finite_numerator B (𝓕 T) hFT L hL
      hB p.coeff (0 : G →₀ ℂ) hrec' f]
    simp
  apply (atomicOnCarrier_restrict_iff A _ _ T).2
  refine ⟨hT, fun x hnot => ?_⟩
  by_contra hx
  apply hnot
  refine ⟨x.property, ?_⟩
  have h := finiteExponentialSymbol_eq_zero_of_annihilated_of_nonzero_atom A T hT a c hmul x hx
  change (∑ m : p.coeff.support, (fun m : G =>
    p.coeff m * combModulationCharacter (L m) x) m) = 0 at h
  rw [p.coeff.support.sum_coe_sort (fun m : G => p.coeff m * combModulationCharacter (L m) x)] at h
  exact h

/-- The real-rooted factor preserves the complete original pair space.
The equality concerns the actual value-only distributions on the
two prescribed carriers, with any unused points still allowed. -/
theorem exists_realRooted_common_core_of_Laurent_annihilator
    (b : Module.Basis ι ℤ G) (L : G →+ ℝ) (hL : Function.Injective L)
    (p : AddMonoidAlgebra ℂ G) (hp : p ≠ 0)
    (A B : LocallyFiniteCarrier) (hB : B.carrier ⊆ range L)
    (hA : ∀ x ∈ A.carrier, annihilatorExponentialSymbol L p.coeff x = 0) :
    ∃ d g : AddMonoidAlgebra ℂ G, p = d * g ∧ g ≠ 0 ∧
      (∀ z : ℂ, z.im ≠ 0 → complexExponentialSum L g.coeff z ≠ 0) ∧
      DistributionalMeyerPairSpace A B =
        DistributionalMeyerPairSpace (annihilatorZeroSubcarrier L g.coeff A) B := by
  obtain ⟨d, g, hpg, hg, hroot, hdiv⟩ :=
    exists_realRooted_factor_dvd_all_originalPair_numerators b L hL p hp
  have hd : d.coeff ≠ 0 := by
    intro hd
    have hd' : d = 0 := AddMonoidAlgebra.coeff_injective (hd.trans AddMonoidAlgebra.coeff_zero.symm)
    exact hp (by rw [hpg, hd', zero_mul])
  have hp' : p.coeff ≠ 0 := fun h => hp
    (AddMonoidAlgebra.coeff_injective (h.trans AddMonoidAlgebra.coeff_zero.symm))
  refine ⟨d, g, hpg, hg, ?_, ?_⟩
  · intro z hz
    rw [← basisLaurentEvaluation_zero_phase b L g z]
    change basisLaurentEvaluation b (basisLaurentPhasePoint b L (fun _ => (0 : ℂ)) z) g ≠ 0
    simpa only [Complex.ofReal_zero] using hroot (fun _ => 0) z hz
  · ext T
    simp only [mem_distributionalMeyerPairSpace_iff]
    constructor
    · rintro ⟨hT, hFT⟩
      refine ⟨?_, hFT⟩
      obtain ⟨r, hr⟩ := originalFourierPair_exists_finite_numerator L hL p.coeff hp'
        A B T hT hFT hA 0
      let R : AddMonoidAlgebra ℂ G := AddMonoidAlgebra.ofCoeff r
      have hR : cutArrayNumerator L p.coeff 0 (originalFourierArray L B T) =
          (fun n => R.coeff n) := funext (fun n => (hr n).1.symm)
      have hrec := originalFourierArray_annihilated L p.coeff A B T hT hFT hA
      obtain ⟨Q, hQ⟩ := hdiv A B hB T hT hFT hA 0 R hR
      rw [hpg] at hrec hR
      rw [hQ] at hR
      have hred := (laurentRecurrence_cancel_common_factor L hL d g Q hd _
        (originalFourierArray_frequencyLocallyFinite L hL B T) 0 hrec hR).1
      exact originalPair_atomicOn_zeroSubcarrier_of_arrayRecurrence L hL g A B hB T hT hFT hred
    · rintro ⟨hT, hFT⟩
      have hsub : (annihilatorZeroSubcarrier L g.coeff A).carrier ⊆ A.carrier := by
        intro x hx
        exact hx.1
      exact ⟨hT.mono hsub, hFT⟩

end

end MeyerGeneralProblem
