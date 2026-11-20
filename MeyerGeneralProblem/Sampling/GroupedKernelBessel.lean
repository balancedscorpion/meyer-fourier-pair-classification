module

public import MeyerGeneralProblem.Sampling.BeurlingSmoothing
public import MeyerGeneralProblem.Sampling.GroupedExponentialUpper

@[expose] public section

/-!
# Dimension-independent Bessel bounds for smoothed grouped kernels

Each cluster has at most `q` coordinates. Uniformly bounded raw kernel masses
give a common nonnegative Fourier majorant after convolution with a fixed
positive smoother. Grouping coordinates at each separated anchor costs only
`q`; the upper large sieve then controls all anchors without a factor in
their number. No interpolation identity or lower bound is assumed here.
-/

namespace MeyerGeneralProblem

open MeasureTheory
open scoped SchwartzMap FourierTransform

noncomputable section

/-- Fourier-majorant domination is invariant under arbitrary finite reindexing. -/
theorem schwartz_fintype_synthesis_norm_sq_le_of_fourier_domination
    {ι : Type*} [Fintype ι] (v g : ι → SchwartzMap ℝ ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hpos : ∀ i w, ∃ z : ℝ, 0 ≤ z ∧ (𝓕 (g i)) w = (z : ℂ))
    (hdom : ∀ i w, ‖(𝓕 (v i)) w‖ ≤ Real.sqrt C * ‖(𝓕 (g i)) w‖)
    (c : ι → ℂ) :
    (∫ t : ℝ, ‖(∑ i, c i • v i : SchwartzMap ℝ ℂ) t‖ ^ 2) ≤
      C * ∫ t : ℝ, ‖(∑ i, (‖c i‖ : ℂ) • g i : SchwartzMap ℝ ℂ) t‖ ^ 2 := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hv := e.sum_comp (fun i => c i • v i)
  have hg := e.sum_comp (fun i => (‖c i‖ : ℂ) • g i)
  simpa only [hv, hg] using
    schwartz_synthesis_norm_sq_le_of_fourier_domination
      (fun i => v (e i)) (fun i => g (e i)) hC
      (fun i => hpos (e i)) (fun i => hdom (e i)) (fun i => c (e i))

/-- Cauchy--Schwarz is applied inside each actual cluster only. -/
theorem grouped_absoluteCoefficient_sq_le {k q : ℕ} (hk : k ≤ q) (c : Fin k → ℂ) :
    (∑ j, ‖c j‖) ^ 2 ≤ (q : ℝ) * ∑ j, ‖c j‖ ^ 2 := by
  have h : (∑ j, ‖c j‖) ^ 2 ≤ (k : ℝ) * ∑ j, ‖c j‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖c j‖)
  exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hk)
    (Finset.sum_nonneg (fun j hj => sq_nonneg _)))

/-- A common positive Fourier majorant at each separated anchor gives an
actual synthesis bound for variable-sized clusters. Only their maximum size
appears, never the total number of clusters or any internal node gap. -/
theorem schwartz_grouped_synthesis_norm_sq_le_of_fourier_domination
    {n q : ℕ} (size : Fin n → ℕ) (hsize : ∀ i, size i ≤ q)
    (s : Fin n → ℝ) {d r M C : ℝ} (hd : 0 < d) (hr : 0 ≤ r)
    (hsep : PairwiseFrequencySeparated s d) (G : SchwartzMap ℝ ℂ)
    (hGs : Function.support G ⊆ Set.Icc (-r) r) (hM : 0 ≤ M)
    (hGM : ∀ t, ‖G t‖ ≤ M) (hC : 0 ≤ C)
    (g : Fin n → SchwartzMap ℝ ℂ) (hg : ∀ i t, g i t = G t * gramPhase (s i) t)
    (hpos : ∀ i w, ∃ z : ℝ, 0 ≤ z ∧ (𝓕 (g i)) w = (z : ℂ))
    (v : (i : Fin n) → Fin (size i) → SchwartzMap ℝ ℂ)
    (hdom : ∀ i j w, ‖(𝓕 (v i j)) w‖ ≤ Real.sqrt C * ‖(𝓕 (g i)) w‖)
    (c : (i : Fin n) → Fin (size i) → ℂ) :
    (∫ t : ℝ, ‖(∑ i, ∑ j, c i j • v i j : SchwartzMap ℝ ℂ) t‖ ^ 2) ≤
      (q : ℝ) * C * (M ^ 2 * (fourierIntervalLargeSieveConstant * (2 * r + d⁻¹))) *
        ∑ i, ∑ j, ‖c i j‖ ^ 2 := by
  classical
  let a : Fin n → ℝ := fun i => ∑ j, ‖c i j‖
  have ha (i : Fin n) : 0 ≤ a i := Finset.sum_nonneg (fun j hj => norm_nonneg _)
  have hmajorant : (∑ x : Σ i, Fin (size i), (‖c x.1 x.2‖ : ℂ) • g x.1) =
      (∑ i, (a i : ℂ) • g i : SchwartzMap ℝ ℂ) := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i hi
    change (∑ j, (‖c i j‖ : ℂ) • g i) = (a i : ℂ) • g i
    rw [← Finset.sum_smul, ← Complex.ofReal_sum]
  have hfirst := schwartz_fintype_synthesis_norm_sq_le_of_fourier_domination
    (fun x : Σ i, Fin (size i) => v x.1 x.2) (fun x => g x.1) hC
    (fun x => hpos x.1) (fun x => hdom x.1 x.2) (fun x => c x.1 x.2)
  rw [hmajorant, Fintype.sum_sigma] at hfirst
  let K := M ^ 2 * (fourierIntervalLargeSieveConstant * (2 * r + d⁻¹))
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg _)
    (mul_nonneg fourierIntervalLargeSieveConstant_pos.le (by positivity))
  have hsecond : (∫ t : ℝ, ‖(∑ i, (a i : ℂ) • g i : SchwartzMap ℝ ℂ) t‖ ^ 2) ≤
      K * ∑ i, a i ^ 2 := by
    simpa only [K, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha _)] using
      schwartz_modulation_synthesis_norm_sq_le s hd hr hsep G hGs hM hGM g hg
        (fun i => (a i : ℂ))
  have hcoeff : (∑ i, a i ^ 2) ≤ (q : ℝ) * ∑ i, ∑ j, ‖c i j‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => grouped_absoluteCoefficient_sq_le (hsize i) (c i))
  calc
    _ ≤ C * (K * ∑ i, a i ^ 2) := hfirst.trans (mul_le_mul_of_nonneg_left hsecond hC)
    _ ≤ C * (K * ((q : ℝ) * ∑ i, ∑ j, ‖c i j‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcoeff hK) hC
    _ = _ := by ring

/-- Actual convolution with one modulated positive smoother supplies the
required Fourier domination directly from each raw kernel's `L¹` mass. -/
theorem schwartz_grouped_convolution_synthesis_norm_sq_le
    {n q : ℕ} (size : Fin n → ℕ) (hsize : ∀ i, size i ≤ q)
    (s : Fin n → ℝ) {d r M C : ℝ} (hd : 0 < d) (hr : 0 ≤ r)
    (hsep : PairwiseFrequencySeparated s d) (G : SchwartzMap ℝ ℂ)
    (hGs : Function.support G ⊆ Set.Icc (-r) r) (hM : 0 ≤ M)
    (hGM : ∀ t, ‖G t‖ ≤ M) (hC : 0 ≤ C)
    (hGpos : ∀ w, ∃ z : ℝ, 0 ≤ z ∧ FourierTransform.fourier (G : ℝ → ℂ) w = (z : ℂ))
    (g : Fin n → SchwartzMap ℝ ℂ) (hg : ∀ i t, g i t = G t * gramPhase (s i) t)
    (κ : (i : Fin n) → Fin (size i) → ℝ → ℂ) (hκ : ∀ i j, Integrable (κ i j))
    (hmass : ∀ i j, (∫ t : ℝ, ‖κ i j t‖) ^ 2 ≤ C)
    (v : (i : Fin n) → Fin (size i) → SchwartzMap ℝ ℂ)
    (hv : ∀ i j, (v i j : ℝ → ℂ) = fourierKernelConvolution (κ i j) (g i))
    (c : (i : Fin n) → Fin (size i) → ℂ) :
    (∫ t : ℝ, ‖(∑ i, ∑ j, c i j • v i j : SchwartzMap ℝ ℂ) t‖ ^ 2) ≤
      (q : ℝ) * C * (M ^ 2 * (fourierIntervalLargeSieveConstant * (2 * r + d⁻¹))) *
        ∑ i, ∑ j, ‖c i j‖ ^ 2 := by
  have hpos (i : Fin n) (w : ℝ) : ∃ z : ℝ, 0 ≤ z ∧ (𝓕 (g i)) w = (z : ℂ) := by
    change ∃ z : ℝ, 0 ≤ z ∧ FourierTransform.fourier (g i : ℝ → ℂ) w = (z : ℂ)
    rw [show (g i : ℝ → ℂ) = (fun t => G t * gramPhase (s i) t) from funext (hg i),
      fourier_mul_gramPhase]
    exact hGpos _
  apply schwartz_grouped_synthesis_norm_sq_le_of_fourier_domination size hsize s hd hr
    hsep G hGs hM hGM hC g hg hpos v _ c
  intro i j w
  have hm : (∫ t : ℝ, ‖κ i j t‖) ≤ Real.sqrt C := by
    apply (sq_le_sq₀ (integral_nonneg (fun t => norm_nonneg _)) (Real.sqrt_nonneg _)).1
    simpa only [Real.sq_sqrt hC] using hmass i j
  change ‖FourierTransform.fourier (v i j : ℝ → ℂ) w‖ ≤ _
  rw [hv i j, fourier_fourierKernelConvolution (hκ i j) (g i).integrable, norm_mul]
  exact mul_le_mul_of_nonneg_right
    ((norm_fourier_le_integral_norm (κ i j) w).trans hm) (norm_nonneg _)

/-- A fixed positive smoother turns every uniformly supported, uniformly
`L¹`-bounded grouped kernel family into genuine Schwartz functions with one
positive Bessel constant chosen before the finite cluster configuration.
The output retains the exact convolution formula for interpolation proofs. -/
theorem exists_uniform_grouped_smoothed_kernel_bessel
    (q : ℕ) (G : SchwartzMap ℝ ℂ) {R r d C : ℝ}
    (hr : 0 < r) (hd : 0 < d) (hC : 0 < C)
    (hGs : Function.support G ⊆ Set.Icc (-r) r)
    (hGpos : ∀ w, ∃ z : ℝ, 0 ≤ z ∧ FourierTransform.fourier (G : ℝ → ℂ) w = (z : ℂ)) :
    ∃ B : ℝ, 0 < B ∧ ∀ (n : ℕ) (size : Fin n → ℕ),
      (∀ i, size i ≤ q) → ∀ (s : Fin n → ℝ), PairwiseFrequencySeparated s d →
      ∀ κ : (i : Fin n) → Fin (size i) → ℝ → ℂ,
      (∀ i j, Integrable (κ i j)) →
      (∀ i j, Function.support (κ i j) ⊆ Set.Icc (-R) R) →
      (∀ i j, (∫ t : ℝ, ‖κ i j t‖) ^ 2 ≤ C) →
      ∃ v : (i : Fin n) → Fin (size i) → SchwartzMap ℝ ℂ,
        (∀ i j, Function.support (v i j) ⊆ Set.Icc (-(R + r)) (R + r)) ∧
        (∀ i j, (v i j : ℝ → ℂ) =
          fourierKernelConvolution (κ i j) (fun t => G t * gramPhase (s i) t)) ∧
        ∀ c : (i : Fin n) → Fin (size i) → ℂ,
          (∫ t : ℝ, ‖(∑ i, ∑ j, c i j • v i j : SchwartzMap ℝ ℂ) t‖ ^ 2) ≤
            B * ∑ i, ∑ j, ‖c i j‖ ^ 2 := by
  classical
  let M := SchwartzMap.seminorm ℝ 0 0 G + 1
  have hM : 0 < M := by
    have := (norm_nonneg (G 0)).trans (G.norm_le_seminorm ℝ 0)
    dsimp [M]
    linarith
  have hGM (t : ℝ) : ‖G t‖ ≤ M := (G.norm_le_seminorm ℝ t).trans (by dsimp [M]; linarith)
  let K := M ^ 2 * (fourierIntervalLargeSieveConstant * (2 * r + d⁻¹))
  have hK : 0 < K := mul_pos (sq_pos_of_pos hM)
    (mul_pos fourierIntervalLargeSieveConstant_pos (by positivity))
  refine ⟨((q : ℝ) + 1) * C * K, by positivity, ?_⟩
  intro n size hsize s hsep κ hκ hsupp hmass
  choose g hg hgs using fun i => exists_schwartz_modulation G hGs (s i)
  choose v hv hvs using fun i j => exists_schwartz_fourierKernelConvolution
    (hκ i j) (hsupp i j) (hgs i) ((g i).smooth (⊤ : ℕ∞))
  refine ⟨v, hvs, ?_, ?_⟩
  · intro i j
    rw [hv i j, show (g i : ℝ → ℂ) = (fun t => G t * gramPhase (s i) t) from funext (hg i)]
  · intro c
    have h := schwartz_grouped_convolution_synthesis_norm_sq_le size hsize s hd hr.le
      hsep G hGs hM.le hGM hC.le hGpos g hg κ hκ hmass v hv c
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun i hi =>
      Finset.sum_nonneg (fun j hj => sq_nonneg _)))
    dsimp [K]
    nlinarith

end

end MeyerGeneralProblem
