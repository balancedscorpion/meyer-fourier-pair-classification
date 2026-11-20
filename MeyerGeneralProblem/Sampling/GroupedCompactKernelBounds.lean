module

public import MeyerGeneralProblem.Sampling.GroupedCorrectedKernelConvolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section

/-!
# Uniform seminorm bounds for compact spectral smoothing

The derivative acts on the fixed smooth factor. The supported smoothed
kernel and its Fourier transform have seminorms controlled by the raw
spectral kernel mass.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff FourierTransform SchwartzMap Topology

/-- A bounded smoothing factor gives a pointwise bound by the raw kernel mass. -/
theorem norm_fourierKernelConvolution_le_mass_mul
    (f g : ℝ → ℂ) (hf : Integrable f) (C : ℝ) (hC : ∀ x, ‖g x‖ ≤ C) (x : ℝ) :
    ‖fourierKernelConvolution f g x‖ ≤ (∫ t : ℝ, ‖f t‖) * C := by
  have h := norm_integral_le_of_norm_le (hf.norm.mul_const C)
    (Eventually.of_forall (fun t : ℝ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC (x - t)) (norm_nonneg _)) :
      ∀ᵐ t : ℝ, ‖f t * g (x - t)‖ ≤ ‖f t‖ * C)
  simpa only [fourierKernelConvolution, convolution_def, ContinuousLinearMap.mul_apply',
    integral_mul_const] using h

/-- Physical differentiation of a smooth compact kernel stays on the
smoothing factor in the actual convolution. -/
theorem iteratedDeriv_fourierKernelConvolution_right
    (f : ℝ → ℂ) (hf : Integrable f) (g : SchwartzMap ℝ ℂ)
    (hgc : HasCompactSupport (g : ℝ → ℂ)) (n : ℕ) :
    iteratedDeriv n (fourierKernelConvolution f g) =
      fourierKernelConvolution f (iteratedDeriv n (g : ℝ → ℂ)) := by
  let D (n : ℕ) := ((SchwartzMap.derivCLM ℂ ℂ)^[n]) g
  have hD (n : ℕ) : (D n : ℝ → ℂ) = iteratedDeriv n (g : ℝ → ℂ) := by
    induction n with
    | zero => simp [D]
    | succ n ih =>
        rw [iteratedDeriv_succ, ← ih]
        funext x
        rw [show D (n + 1) = SchwartzMap.derivCLM ℂ ℂ (D n) from Function.iterate_succ_apply' _ _ _]
        exact SchwartzMap.derivCLM_apply ℂ _ _
  have hDC (n : ℕ) : HasCompactSupport (D n : ℝ → ℂ) := by
    induction n with
    | zero => exact hgc
    | succ n ih =>
        rw [hD, iteratedDeriv_succ, ← hD]
        exact ih.deriv
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih, ← hD, iteratedDeriv_succ, ← hD]
      funext x
      have h := (hDC n).hasDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
        hf.locallyIntegrable ((D n).smooth 1) x
      exact h.deriv

/-- Every Schwartz seminorm of a compact smoothing is controlled by the
integrable mass of its raw kernel. -/
theorem schwartz_seminorm_fourierKernelConvolution_le
    (f : ℝ → ℂ) (hf : Integrable f) (g v : SchwartzMap ℝ ℂ)
    (hgc : HasCompactSupport (g : ℝ → ℂ))
    (hEq : (v : ℝ → ℂ) = fourierKernelConvolution f g)
    (W : ℝ) (hW : 0 ≤ W) (hvs : Function.support v ⊆ Icc (-W) W) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n v ≤
      (W ^ k * SchwartzMap.seminorm ℂ 0 n g) * ∫ t : ℝ, ‖f t‖ := by
  have hMass : 0 ≤ ∫ t : ℝ, ‖f t‖ := integral_nonneg (fun _ => norm_nonneg _)
  refine SchwartzMap.seminorm_le_bound' ℂ k n v (by positivity) ?_
  intro x
  by_cases hx : x ∈ Icc (-W) W
  · have hBound (t : ℝ) : ‖iteratedDeriv n (g : ℝ → ℂ) t‖ ≤ SchwartzMap.seminorm ℂ 0 n g := by
      simpa only [pow_zero, one_mul] using SchwartzMap.le_seminorm' ℂ 0 n g t
    have hDeriv := norm_fourierKernelConvolution_le_mass_mul f _ hf _ hBound x
    have hNorm : ‖iteratedDeriv n (v : ℝ → ℂ) x‖ ≤
        (∫ t : ℝ, ‖f t‖) * SchwartzMap.seminorm ℂ 0 n g := by
      rw [hEq, iteratedDeriv_fourierKernelConvolution_right f hf g hgc]
      exact hDeriv
    calc
      _ ≤ W ^ k * ((∫ t : ℝ, ‖f t‖) * SchwartzMap.seminorm ℂ 0 n g) :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (abs_le.mpr hx) _) hNorm (norm_nonneg _)
          (pow_nonneg hW _)
      _ = _ := by ring
  · have hNear : (v : ℝ → ℂ) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds (show x ∈ (Icc (-W) W)ᶜ from hx)] with t ht
      by_contra h
      exact ht (hvs h)
    rw [hNear.iteratedDeriv_eq n, iteratedDeriv_const]
    simp only [ite_self, norm_zero, mul_zero]
    positivity

/-- For a fixed smoothing, the physical Fourier tests all have uniform
Schwartz seminorms when the raw spectral mass is uniformly bounded. -/
theorem exists_schwartz_seminorm_fourier_smoothedKernel_bound
    (g : SchwartzMap ℝ ℂ) (hgc : HasCompactSupport (g : ℝ → ℂ))
    (W : ℝ) (hW : 0 ≤ W) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ → ℂ), Integrable f → ∀ v : SchwartzMap ℝ ℂ,
      (v : ℝ → ℂ) = fourierKernelConvolution f g →
      Function.support v ⊆ Icc (-W) W →
      SchwartzMap.seminorm ℂ k n (𝓕 v) ≤ C * ∫ t : ℝ, ‖f t‖ := by
  let p := (SchwartzMap.seminorm ℂ k n).comp
    (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ)).toLinearMap
  have hp : Continuous p := ((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (k, n)).comp
    (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ)).continuous
  obtain ⟨s, C, _, h⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) p hp
  let H (i : ℕ × ℕ) := W ^ i.1 * SchwartzMap.seminorm ℂ 0 i.2 g
  let M := ∑ i ∈ s, H i
  have hH (i : ℕ × ℕ) : 0 ≤ H i := by dsimp [H]; positivity
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => hH i
  refine ⟨(C : ℝ) * M, mul_nonneg C.coe_nonneg hM, fun f hf v hEq hvs => ?_⟩
  have hMass : 0 ≤ ∫ t : ℝ, ‖f t‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hS : (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) v ≤ M * ∫ t : ℝ, ‖f t‖ := by
    refine Seminorm.finset_sup_apply_le (mul_nonneg hM hMass) (fun i hi => ?_)
    exact (schwartz_seminorm_fourierKernelConvolution_le f hf g v hgc hEq W hW hvs i.1 i.2).trans
      (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => hH i) hi) hMass)
  exact (h v).trans ((mul_le_mul_of_nonneg_left hS C.coe_nonneg).trans_eq (mul_assoc _ _ _).symm)

end
end MeyerGeneralProblem
