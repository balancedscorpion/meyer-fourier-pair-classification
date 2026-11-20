module

public import MeyerGeneralProblem.Sampling.GroupedCorrectedKernels
public import MeyerGeneralProblem.Sampling.GroupedDensityColouring
public import MeyerGeneralProblem.Sampling.GroupedRieszLower

@[expose] public section

/-!
# Density-sharp lower bounds for genuine grouped exponentials

Strict numerical upper density pays for whole-cluster insertion, finite
colour convolution and one fixed positive smoother. Corrected Newton data
restore exact biorthogonality; the proved Bessel estimate and Hilbert duality
yield one lower constant before every finite grouped subfamily.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory

/-- Genuine grouped exponential lower bounds under the strict numerical
density threshold. Groups retain their given ordered initial prefixes; only
inter-group separation, bounded diameter and bounded size enter the constant.
There is no lower bound on individual gaps within a group. -/
theorem exists_groupedExponentialInitial_uniform_lower_of_upperDensity_lt
    (S : LocallyFiniteCarrier) (q : ℕ) {W d D : ℝ}
    (hW : 0 < W) (hd : 0 < d) (hD : 0 ≤ D)
    (hS : upperUniformBeurlingDensity S < ENNReal.ofReal (2 * W)) :
    ∃ A : ℝ, 0 < A ∧ ∀ N (size : Fin N → ℕ),
      (∀ g, 0 < size g) → (∀ g, size g ≤ q) →
      ∀ nodes : (g : Fin N) → Fin (size g) → ℝ,
      (∀ g, Function.Injective (nodes g)) → (∀ g i, nodes g i ∈ S.carrier) →
      (∀ g i j, dist (nodes g i) (nodes g j) ≤ D) →
      (∀ g h, g ≠ h → ∀ i j, d ≤ |nodes g i-nodes h j|) →
      ∀ c : (g : Fin N) → Fin (size g) → ℂ,
        A * (∑ g, ∑ j, ‖c g j‖^2) ≤
          ∫ t : ℝ in Set.Icc (-W) W,
            ‖∑ g, ∑ j, c g j * groupedExponentialInitial (nodes g) j t‖^2 := by
  obtain ⟨R, η, C, _hR, hη, hbudget, hC, hraw⟩ :=
    exists_uniform_finite_grouped_kernels_of_upperDensity_lt S q hW hd hD hS
  obtain ⟨G, hGs, _hG0, hGpos, hfloor⟩ :=
    exists_compact_positive_fourier_band_smoothing hη hD
  obtain ⟨B, hB, hsmooth⟩ := exists_uniform_corrected_grouped_schwartz_kernels
    q G (R := R) hη hd hD hC hGs hGpos hfloor
  refine ⟨B⁻¹, inv_pos.mpr hB, ?_⟩
  intro N size hpos hsize nodes hnodes hmem hdiam hsep c
  let first (g : Fin N) : Fin (size g) := ⟨0, hpos g⟩
  let anchor (g : Fin N) := nodes g (first g)
  have ha : PairwiseFrequencySeparated anchor d :=
    fun g h hgh => hsep g h hgh (first g) (first h)
  have hc (g : Fin N) (i : Fin (size g)) : |nodes g i-anchor g| ≤ D := by
    simpa only [anchor, Real.dist_eq] using hdiam g i (first g)
  obtain ⟨ρ, hi, hs, ht, ho, hm⟩ := hraw N size hsize nodes hnodes hmem hdiam hsep
  obtain ⟨v, hvs, hvt, hvo, hvb⟩ :=
    hsmooth N size hsize nodes hnodes anchor ha hc ρ hi hs ht ho hm
  have hvsW (g : Fin N) (i : Fin (size g)) :
      Function.support (v g i) ⊆ Set.Icc (-W) W := by
    intro t ht
    obtain ⟨hl, hu⟩ := hvs g i ht
    exact ⟨by linarith, by linarith⟩
  exact finite_groupedWindow_lowerBound_of_schwartz_bessel size nodes hnodes hB v
    hvsW hvt hvo hvb c

end

end MeyerGeneralProblem
