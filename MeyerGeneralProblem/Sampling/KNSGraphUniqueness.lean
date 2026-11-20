module

public import MeyerGeneralProblem.Sampling.KNSGraphRepresentative
public import MeyerGeneralProblem.Sampling.KNSClassicalUniqueness

@[expose] public section

/-!
# Graph uniqueness from genuine representative point zeros

The full graph supplies all regularity and moment hypotheses required by
classical reciprocal-gap uniqueness. Genuine cofinite zeros of the chosen
representative and its actual Fourier integral therefore force the graph
element to vanish. No bounded sampler or sampler-kernel identification is
assumed to have been constructed by this theorem.
-/

namespace MeyerGeneralProblem
namespace KNSGraphSpace

open MeasureTheory
open scoped FourierTransform

/-- Genuine cofinite point zeros of the actual representative Fourier pair
force the full graph element to vanish. No completed sampler is asserted. -/
theorem eq_zero_of_representative_zeros
    {k : ℕ} (hk : 2 ≤ k) {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (Λ M : TwoSidedCarrier) (F J G L : Finset ℤ)
    (hgapΛ : ∀ j : ℤ, j ∉ J → max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ ρ)
    (hgapM : ∀ j : ℤ, j ∉ L → max |M j| |M (j+1)| * (M (j+1)-M j) ≤ ρ)
    (v : KNSGraphSpace k)
    (hzΛ : ∀ j : ℤ, j ∉ F → representative k v (Λ j) = 0)
    (hzM : ∀ j : ℤ, j ∉ G → 𝓕 (representative k v) (M j) = 0) :
    v = 0 := by
  obtain ⟨hae, _, hf, hF, hf1, hF1, hf2, _, hx2, hξ2⟩ :=
    representative_properties hk v
  have hz := knsClassicalUniqueness_of_reciprocal_gaps hρ hρhalf
    Λ M F J G L hgapΛ hgapM hf hF hf1 hF1 hf2 hx2 hξ2 hzΛ hzM
  apply KNSGraphSpace.physical_injective k
  rw [map_zero]
  apply Lp.ext
  rw [hz] at hae
  exact hae.symm.trans (Lp.coeFn_zero ℂ 2 volume).symm

end KNSGraphSpace
end MeyerGeneralProblem
