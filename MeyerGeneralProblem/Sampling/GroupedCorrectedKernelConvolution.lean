module

public import MeyerGeneralProblem.Sampling.GroupedCorrectedKernels

@[expose] public section

/-! # Convolution witnesses for corrected grouped Schwartz kernels -/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory
open scoped FourierTransform

/-- Genuine supported raw delta kernels become exact Schwartz delta kernels
with one Bessel constant before every finite family. The correction is the
actual centered Newton data of the polynomial divided by the smoother.
The raw convolution factors retain one common integrable mass bound. -/
theorem exists_uniform_corrected_grouped_schwartz_kernels_with_convolution
    (q : ℕ) (G : SchwartzMap ℝ ℂ) {R r d D C : ℝ}
    (hr : 0 < r) (hd : 0 < d) (hD : 0 ≤ D) (hC : 0 < C)
    (hGs : Function.support G ⊆ Set.Icc (-r) r)
    (hGpos : ∀ w, ∃ z : ℝ, 0 ≤ z ∧ FourierTransform.fourier (G : ℝ → ℂ) w = z)
    (hfloor : ∀ w, |w| ≤ D → (1/4:ℝ) ≤
      (FourierTransform.fourier (G : ℝ → ℂ) w).re) :
    ∃ B M : ℝ, 0 < B ∧ 0 ≤ M ∧ ∀ N (size : Fin N → ℕ), (∀ g, size g ≤ q) →
      ∀ (nodes : (g : Fin N) → Fin (size g) → ℝ),
      (∀ g, Function.Injective (nodes g)) → ∀ (anchor : Fin N → ℝ),
      PairwiseFrequencySeparated anchor d → (∀ g i, |nodes g i-anchor g| ≤ D) →
      ∀ ρ : (g : Fin N) → Fin (size g) → ℝ → ℂ,
      (∀ g i, Integrable (ρ g i)) →
      (∀ g i, Function.support (ρ g i) ⊆ Set.Icc (-R) R) →
      (∀ g (i j : Fin (size g)), analyticDividedDifference (finiteNodeSequence (nodes g)) j
        (FourierTransform.fourier (ρ g i)) = if i = j then 1 else 0) →
      (∀ g h, g ≠ h → ∀ (i : Fin (size g)) (j : Fin (size h)),
        analyticDividedDifference (finiteNodeSequence (nodes h)) j
          (FourierTransform.fourier (ρ g i)) = 0) →
      (∀ g i, (∫ t : ℝ, ‖ρ g i t‖)^2 ≤ C) →
      ∃ v : (g : Fin N) → Fin (size g) → SchwartzMap ℝ ℂ,
        (∀ g i, Function.support (v g i) ⊆ Set.Icc (-(R+r)) (R+r)) ∧
        (∀ g (i j : Fin (size g)), analyticDividedDifference (finiteNodeSequence (nodes g)) j
          (FourierTransform.fourier (v g i : ℝ → ℂ)) = if i = j then 1 else 0) ∧
        (∀ g h, g ≠ h → ∀ (i : Fin (size g)) (j : Fin (size h)),
          analyticDividedDifference (finiteNodeSequence (nodes h)) j
            (FourierTransform.fourier (v g i : ℝ → ℂ)) = 0) ∧
        (∀ c : (g : Fin N) → Fin (size g) → ℂ,
          (∫ t : ℝ, ‖(∑ g, ∑ j, c g j • v g j : SchwartzMap ℝ ℂ) t‖^2) ≤
            B * ∑ g, ∑ j, ‖c g j‖^2) ∧
        ∀ g i, ∃ κ : ℝ → ℂ, Integrable κ ∧ Function.support κ ⊆ Set.Icc (-R) R ∧
          (∫ t : ℝ, ‖κ t‖) ≤ M ∧
          (v g i : ℝ → ℂ) = fourierKernelConvolution κ (fun t => G t * gramPhase (anchor g) t) := by
  classical
  obtain ⟨K, hK, hcorrection⟩ := exists_uniform_centeredCorrectedData_bound G q hD
  let C' := (((q:ℝ)+1)*K)^2*C
  have hC' : 0 < C' := by dsimp [C']; positivity
  obtain ⟨B, hB, hbessel⟩ := exists_uniform_grouped_smoothed_kernel_bessel
    q G (R := R) hr hd hC' hGs hGpos
  refine ⟨B, Real.sqrt C', hB, Real.sqrt_nonneg _, ?_⟩
  intro N size hsize nodes hnodes anchor hsep hcenter ρ hint hsupp htarget hoff hmass
  let data (g : Fin N) (i j : Fin (size g)) : ℂ := if i = j then 1 else 0
  let a (g : Fin N) (i : Fin (size g)) : Fin (size g) → ℂ :=
    groupedCenteredCorrectedData G (nodes g) (anchor g) (data g i)
  let κ (g : Fin N) (i : Fin (size g)) := groupedKernelCombination (ρ g) (a g i)
  have ha (g : Fin N) (i j : Fin (size g)) : ‖a g i j‖ ≤ K := by
    have h := hcorrection (size g) (hsize g) (nodes g) (anchor g) (hcenter g) (data g i) j
    simpa [a, data, apply_ite] using h
  have hκ (g : Fin N) (i : Fin (size g)) : Integrable (κ g i) :=
    integrable_groupedKernelCombination (ρ g) (hint g) (a g i)
  have hκs (g : Fin N) (i : Fin (size g)) :
      Function.support (κ g i) ⊆ Set.Icc (-R) R :=
    support_groupedKernelCombination_subset (ρ g) (a g i) (hsupp g)
  have hκmass (g : Fin N) (i : Fin (size g)) : (∫ t : ℝ, ‖κ g i t‖)^2 ≤ C' := by
    have h := integral_norm_groupedKernelCombination_sq_le (hsize g) (ρ g) (hint g)
      (a g i) hC.le hK.le (hmass g) (ha g i)
    apply h.trans
    dsimp [C']
    gcongr
    linarith
  have hκdata (g : Fin N) (i j : Fin (size g)) :
      analyticDividedDifference (finiteNodeSequence (nodes g)) j
        (FourierTransform.fourier (κ g i)) = a g i j :=
    initialData_fourier_groupedKernelCombination_of_delta (nodes g) (hnodes g)
      (ρ g) (hint g) (htarget g) (a g i) j
  have hκoff (g h : Fin N) (hgh : g ≠ h) (i : Fin (size g)) (j : Fin (size h)) :
      analyticDividedDifference (finiteNodeSequence (nodes h)) j
        (FourierTransform.fourier (κ g i)) = 0 := by
    rw [initialData_fourier_groupedKernelCombination (nodes h) (hnodes h) (ρ g)
      (hint g) (a g i) j]
    simp only [hoff g h hgh, mul_zero, Finset.sum_const_zero]
  obtain ⟨v, hvs, hv, hvbound⟩ := hbessel N size hsize anchor hsep κ hκ hκs hκmass
  have hvfourier (g : Fin N) (i : Fin (size g)) (w : ℝ) :
      FourierTransform.fourier (v g i : ℝ → ℂ) w =
        FourierTransform.fourier (κ g i) w *
          FourierTransform.fourier (G : ℝ → ℂ) (w-anchor g) := by
    rw [hv g i, fourier_fourierKernelConvolution (hκ g i), fourier_mul_gramPhase]
    exact G.integrable.mul_bdd (by unfold gramPhase; fun_prop)
      (Filter.Eventually.of_forall (fun t => (norm_gramPhase (anchor g) t).le))
  refine ⟨v, hvs, ?_, ?_, hvbound, ?_⟩
  · intro g i j
    rw [show FourierTransform.fourier (v g i : ℝ → ℂ) = _ from
      funext (hvfourier g i)]
    exact initialData_mul_shifted_fourier_eq_of_correctedData G (nodes g) (hnodes g)
      (anchor g) (data g i) _ (hκdata g i) (fun l => hfloor _ (hcenter g l)) j
  · intro g h hgh i j
    have hz (l : Fin (size h)) : FourierTransform.fourier (κ g i) (nodes h l) = 0 := by
      have he := values_eq_of_initialData_eq (nodes h) (hnodes h)
        (FourierTransform.fourier (κ g i)) (fun _ => 0)
        (fun k => (hκoff g h hgh i k).trans (initialData_zero (nodes h) k).symm) l
      exact he
    rw [initialData_eq_of_values_eq (nodes h) (hnodes h) _ (fun _ => 0)
      (fun l => by rw [hvfourier g i, hz l, zero_mul]) j]
    exact initialData_zero (nodes h) j
  · intro g i
    refine ⟨κ g i, hκ g i, hκs g i, ?_, hv g i⟩
    apply (sq_le_sq₀ (integral_nonneg (fun t => norm_nonneg _)) (Real.sqrt_nonneg _)).mp
    simpa only [Real.sq_sqrt hC'.le] using hκmass g i

end
end MeyerGeneralProblem
