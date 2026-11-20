module

public import MeyerGeneralProblem.Sampling.BeurlingSmoothing

@[expose] public section

/-!
# Compact Fourier window tests with finitely many prescribed zeros

Applying a constant-coefficient first derivative in the test variable
inserts a linear factor in its Fourier transform. This places additional
zeros at finitely many nearby sites without enlarging the test window.
-/

namespace MeyerGeneralProblem

noncomputable section

open SchwartzMap
open scoped SchwartzMap FourierTransform

private def windowKill (x : ℝ) (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.derivCLM ℂ ℂ f - (2 * Real.pi * Complex.I * x : ℂ) • f

private theorem windowKill_support_subset (x : ℝ) (f : SchwartzMap ℝ ℂ) :
    Function.support (windowKill x f) ⊆ tsupport f := by
  intro t ht
  by_contra hn
  have hf : f t = 0 := by
    by_contra h
    exact hn (subset_tsupport f h)
  have hd : SchwartzMap.derivCLM ℂ ℂ f t = 0 := by
    by_contra h
    apply hn
    exact SchwartzMap.tsupport_derivCLM_subset ℂ f (subset_tsupport _ h)
  exact ht (by simp [windowKill, sub_apply, smul_apply, hf, hd])

private theorem fourier_windowKill (x y : ℝ) (f : SchwartzMap ℝ ℂ) :
    (𝓕 (windowKill x f)) y = (2 * Real.pi * Complex.I * ((y : ℂ) - x)) * (𝓕 f) y := by
  have hderiv : (SchwartzMap.derivCLM ℂ ℂ f : ℝ → ℂ) = deriv (f : ℝ → ℂ) :=
    funext (SchwartzMap.derivCLM_apply ℂ f)
  have hFourier :
      (𝓕 (SchwartzMap.derivCLM ℂ ℂ f)) y = (2 * Real.pi * Complex.I * y : ℂ) * (𝓕 f) y := by
    rw [SchwartzMap.fourier_coe, hderiv, Real.fourier_deriv f.integrable f.differentiable
      (hderiv ▸ (SchwartzMap.derivCLM ℂ ℂ f).integrable)]
    rw [SchwartzMap.fourier_coe]
    rfl
  change (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ) (_ - _)) y = _
  rw [map_sub, sub_apply]
  change (𝓕 (SchwartzMap.derivCLM ℂ ℂ f)) y - (𝓕 ((2 * Real.pi * Complex.I * x : ℂ) • f)) y = _
  rw [FourierTransform.fourier_smul, smul_apply, smul_eq_mul, hFourier]
  ring

/-- Prescribe finitely many further zeros while retaining the original
Fourier zeros and preserving the test support bound. The Fourier value at
the distinguished point stays nonzero if it was nonzero originally. -/
theorem exists_schwartz_fourier_kill_finite (f : SchwartzMap ℝ ℂ)
    (Z : Finset ℝ) (x : ℝ) (hx : x ∉ Z) (hfx : (𝓕 f) x ≠ 0)
    {K : Set ℝ} (hK : IsClosed K) (hf : Function.support f ⊆ K) :
    ∃ g : SchwartzMap ℝ ℂ, Function.support g ⊆ K ∧ (𝓕 g) x ≠ 0 ∧
      ∀ y, y ∈ Z ∨ (𝓕 f) y = 0 → (𝓕 g) y = 0 := by
  classical
  induction Z using Finset.induction_on with
  | empty => exact ⟨f, hf, hfx, fun y hy => hy.resolve_left (Finset.notMem_empty y)⟩
  | insert z Z hz ih =>
    have hxz : x ≠ z := fun h => hx (h ▸ Finset.mem_insert_self z Z)
    have hxZ : x ∉ Z := fun h => hx (Finset.mem_insert_of_mem h)
    obtain ⟨g, hgs, hgx, hgZ⟩ := ih hxZ
    refine ⟨windowKill z g, (windowKill_support_subset z g).trans (closure_minimal hgs hK),
      ?_, ?_⟩
    · rw [fourier_windowKill]
      have hdiff : (x : ℂ) - z ≠ 0 := sub_ne_zero.mpr (fun h => hxz (Complex.ofReal_injective h))
      exact mul_ne_zero (mul_ne_zero (by
        apply mul_ne_zero
        · exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
        · exact Complex.I_ne_zero) hdiff) hgx
    · intro y hy
      rw [fourier_windowKill]
      rcases hy with hy | hy
      · rcases Finset.mem_insert.mp hy with rfl | hy
        · simp
        · rw [hgZ y (Or.inl hy), mul_zero]
      · rw [hgZ y (Or.inr hy), mul_zero]

end

end MeyerGeneralProblem
