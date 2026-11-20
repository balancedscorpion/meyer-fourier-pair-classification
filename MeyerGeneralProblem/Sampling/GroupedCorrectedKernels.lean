module

public import MeyerGeneralProblem.Sampling.GroupedSmoothingCorrection
public import MeyerGeneralProblem.Sampling.GroupedKernelBessel

@[expose] public section

/-!
# Actual finite corrected kernels

Finite linear combinations of supported interpolation kernels realize the
centered reciprocal-corrected data. Fourier cancellation after convolution
then recovers the original initial Newton coordinates exactly.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory
open scoped FourierTransform

/-- The actual finite kernel realizing a linear combination of data. -/
def groupedKernelCombination {n : ℕ} (ρ : Fin n → ℝ → ℂ) (a : Fin n → ℂ)
    (t : ℝ) : ℂ := ∑ i, a i * ρ i t

/-- Finite combinations of integrable kernels are genuinely integrable. -/
theorem integrable_groupedKernelCombination {n : ℕ} (ρ : Fin n → ℝ → ℂ)
    (hρ : ∀ i, Integrable (ρ i)) (a : Fin n → ℂ) :
    Integrable (groupedKernelCombination ρ a) :=
  integrable_finsetSum _ (fun i _ => (hρ i).const_mul (a i))

/-- Fourier transformation of an actual finite integrable combination. -/
theorem fourier_groupedKernelCombination {n : ℕ} (ρ : Fin n → ℝ → ℂ)
    (hρ : ∀ i, Integrable (ρ i)) (a : Fin n → ℂ) (w : ℝ) :
    FourierTransform.fourier (groupedKernelCombination ρ a) w =
      ∑ i, a i * FourierTransform.fourier (ρ i) w := by
  have hphase : Continuous (gramPhase (-w)) := by unfold gramPhase; fun_prop
  have hint (i : Fin n) : Integrable (fun t => gramPhase (-w) t * ρ i t) :=
    (hρ i).bdd_mul hphase.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => (norm_gramPhase (-w) t).le))
  rw [fourier_eq_integral_gramPhase]
  simp only [groupedKernelCombination, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [fourier_eq_integral_gramPhase, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by ring)
  · intro i hi
    convert (hint i).const_mul (a i) using 1
    ext t
    ring

/-- The support budget is unchanged by the finite data combination. -/
theorem support_groupedKernelCombination_subset {n : ℕ} (ρ : Fin n → ℝ → ℂ)
    (a : Fin n → ℂ) {R : ℝ}
    (hs : ∀ i, Function.support (ρ i) ⊆ Set.Icc (-R) R) :
    Function.support (groupedKernelCombination ρ a) ⊆ Set.Icc (-R) R := by
  intro t ht
  by_contra hn
  have hz (i : Fin n) : ρ i t = 0 := by
    by_contra h
    exact hn (hs i h)
  exact ht (by simp [groupedKernelCombination, hz])

/-- The mass of a finite combination costs only the sum of its own data
coefficients, not the number of other clusters. -/
theorem integral_norm_groupedKernelCombination_le {n : ℕ}
    (ρ : Fin n → ℝ → ℂ) (hρ : ∀ i, Integrable (ρ i)) (a : Fin n → ℂ) :
    (∫ t : ℝ, ‖groupedKernelCombination ρ a t‖) ≤
      ∑ i, ‖a i‖ * ∫ t : ℝ, ‖ρ i t‖ := by
  calc
    _ ≤ ∫ t : ℝ, ∑ i, ‖a i‖ * ‖ρ i t‖ := by
      apply integral_mono (integrable_groupedKernelCombination ρ hρ a).norm
        (integrable_finsetSum _ (fun i _ => (hρ i).norm.const_mul ‖a i‖))
      intro t
      simpa only [groupedKernelCombination, norm_mul] using norm_sum_le Finset.univ (fun i => a i * ρ i t)
    _ = _ := by rw [integral_finsetSum _ (fun i _ => (hρ i).norm.const_mul ‖a i‖)]
                simp only [integral_const_mul]

/-- Actual initial divided differences are linear on arbitrary functions at
distinct nodes, by the exact finite Newton equivalence. -/
theorem initialData_finite_linear_combination {n k : ℕ}
    (nodes : Fin n → ℝ) (hnodes : Function.Injective nodes)
    (f : Fin k → ℝ → ℂ) (a : Fin k → ℂ) (j : Fin n) :
    analyticDividedDifference (finiteNodeSequence nodes) j (fun t => ∑ i, a i * f i t) =
      ∑ i, a i * analyticDividedDifference (finiteNodeSequence nodes) j (f i) := by
  simp only [analyticDividedDifference_eq_dividedDifferences nodes hnodes,
    dividedDifferences_eq_groupedNewtonWeights, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- A finite combination realizes its actual prescribed Newton data. -/
theorem initialData_fourier_groupedKernelCombination {n k : ℕ}
    (nodes : Fin n → ℝ) (hnodes : Function.Injective nodes)
    (ρ : Fin k → ℝ → ℂ) (hρ : ∀ i, Integrable (ρ i))
    (a : Fin k → ℂ) (j : Fin n) :
    analyticDividedDifference (finiteNodeSequence nodes) j
      (FourierTransform.fourier (groupedKernelCombination ρ a)) =
        ∑ i, a i * analyticDividedDifference (finiteNodeSequence nodes) j
          (FourierTransform.fourier (ρ i)) := by
  rw [show FourierTransform.fourier (groupedKernelCombination ρ a) =
      (fun w => ∑ i, a i * FourierTransform.fourier (ρ i) w) from
    funext (fourier_groupedKernelCombination ρ hρ a)]
  exact initialData_finite_linear_combination nodes hnodes _ a j

/-- Delta-data kernels realize every prescribed finite data vector exactly. -/
theorem initialData_fourier_groupedKernelCombination_of_delta {n : ℕ}
    (nodes : Fin n → ℝ) (hnodes : Function.Injective nodes)
    (ρ : Fin n → ℝ → ℂ) (hρ : ∀ i, Integrable (ρ i))
    (hdata : ∀ i j : Fin n, analyticDividedDifference (finiteNodeSequence nodes) j
      (FourierTransform.fourier (ρ i)) = if i = j then 1 else 0)
    (a : Fin n → ℂ) (j : Fin n) :
    analyticDividedDifference (finiteNodeSequence nodes) j
      (FourierTransform.fourier (groupedKernelCombination ρ a)) = a j := by
  rw [initialData_fourier_groupedKernelCombination nodes hnodes ρ hρ a j]
  simp [hdata]

/-- Uniform raw masses and uniformly bounded correction data give a common
mass bound for every corrected coordinate, with at most the cluster-size loss. -/
theorem integral_norm_groupedKernelCombination_sq_le {n q : ℕ} (hn : n ≤ q)
    (ρ : Fin n → ℝ → ℂ) (hρ : ∀ i, Integrable (ρ i))
    (a : Fin n → ℂ) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hmass : ∀ i, (∫ t : ℝ, ‖ρ i t‖)^2 ≤ C) (ha : ∀ i, ‖a i‖ ≤ K) :
    (∫ t : ℝ, ‖groupedKernelCombination ρ a t‖)^2 ≤ ((q:ℝ)*K)^2*C := by
  have hroot (i : Fin n) : (∫ t : ℝ, ‖ρ i t‖) ≤ Real.sqrt C := by
    apply (sq_le_sq₀ (integral_nonneg (fun t => norm_nonneg _)) (Real.sqrt_nonneg _)).1
    simpa only [Real.sq_sqrt hC] using hmass i
  have hsum : (∑ i, ‖a i‖ * ∫ t : ℝ, ‖ρ i t‖) ≤ (q:ℝ)*K*Real.sqrt C := by
    calc
      _ ≤ ∑ _i : Fin n, K * Real.sqrt C := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul (ha i) (hroot i) (integral_nonneg (fun t => norm_nonneg _)) hK
      _ = (n:ℝ)*K*Real.sqrt C := by simp; ring
      _ ≤ _ := by gcongr
  have hh := (integral_norm_groupedKernelCombination_le ρ hρ a).trans hsum
  have hs := (sq_le_sq₀ (integral_nonneg (fun t => norm_nonneg _))
    (by positivity : 0 ≤ (q:ℝ)*K*Real.sqrt C)).2 hh
  simpa only [mul_pow, Real.sq_sqrt hC] using hs

/-- Genuine supported raw delta kernels become exact Schwartz delta kernels
with one Bessel constant before every finite family. The correction is the
actual centered Newton data of the polynomial divided by the smoother. -/
theorem exists_uniform_corrected_grouped_schwartz_kernels
    (q : ℕ) (G : SchwartzMap ℝ ℂ) {R r d D C : ℝ}
    (hr : 0 < r) (hd : 0 < d) (hD : 0 ≤ D) (hC : 0 < C)
    (hGs : Function.support G ⊆ Set.Icc (-r) r)
    (hGpos : ∀ w, ∃ z : ℝ, 0 ≤ z ∧ FourierTransform.fourier (G : ℝ → ℂ) w = z)
    (hfloor : ∀ w, |w| ≤ D → (1/4:ℝ) ≤
      (FourierTransform.fourier (G : ℝ → ℂ) w).re) :
    ∃ B : ℝ, 0 < B ∧ ∀ N (size : Fin N → ℕ), (∀ g, size g ≤ q) →
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
        ∀ c : (g : Fin N) → Fin (size g) → ℂ,
          (∫ t : ℝ, ‖(∑ g, ∑ j, c g j • v g j : SchwartzMap ℝ ℂ) t‖^2) ≤
            B * ∑ g, ∑ j, ‖c g j‖^2 := by
  classical
  obtain ⟨K, hK, hcorrection⟩ := exists_uniform_centeredCorrectedData_bound G q hD
  let C' := (((q:ℝ)+1)*K)^2*C
  have hC' : 0 < C' := by dsimp [C']; positivity
  obtain ⟨B, hB, hbessel⟩ := exists_uniform_grouped_smoothed_kernel_bessel
    q G (R := R) hr hd hC' hGs hGpos
  refine ⟨B, hB, ?_⟩
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
  refine ⟨v, hvs, ?_, ?_, hvbound⟩
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

end

end MeyerGeneralProblem
