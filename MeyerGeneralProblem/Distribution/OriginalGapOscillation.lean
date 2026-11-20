module

public import MeyerGeneralProblem.Distribution.HalfLineFourierGap
public import MeyerGeneralProblem.Distribution.IntegrableFourierGapOscillation
public import MeyerGeneralProblem.Distribution.OriginalRayHeatTransfer

@[expose] public section

/-!
# Original two-ray oscillation

The open Fourier gap gives unbounded nonzero support on the positive
ray. Reflection transfers the positive-ray argument to the negative
ray and yields the atomic lower-ray density theorem.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Set
open scoped FourierTransform

private theorem fourier_comp_real_neg (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => f (-x)) ξ = 𝓕 f (-ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  let I (x : ℝ) := Complex.exp (↑(-2 * Real.pi * x * -ξ) * Complex.I) • f x
  have h :
      (∫ x : ℝ, I (-x)) = ∫ x : ℝ, I x :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
      (Homeomorph.neg ℝ).measurableEmbedding I
  calc
    _ = ∫ x : ℝ, I (-x) := by
      apply integral_congr_ae
      filter_upwards with x
      have hx : -2 * Real.pi * -x * -ξ = -2 * Real.pi * x * ξ := by ring
      simp only [I, hx]
    _ = _ := h

private theorem hasSignAlternations_negative_ray_of_reflect {f : ℝ → ℝ} {r : ℝ} {n : ℕ}
    (h : HasSignAlternations (fun x => f (-x)) (Icc 0 r) n) :
    HasSignAlternations f (Icc (-r) 0) n := by
  obtain ⟨x, hx, hMem, hSign⟩ := h
  refine ⟨fun i => -x i.rev, ?_, ?_, ?_⟩
  · intro i j hij
    exact neg_lt_neg (hx (Fin.rev_strictAnti hij))
  · intro i
    exact ⟨neg_le_neg (hMem i.rev).2, neg_nonpos.mpr (hMem i.rev).1⟩
  · intro i
    simpa only [Fin.rev_castSucc, Fin.rev_succ, mul_comm] using hSign i.rev

/-- Both original rays of a nonzero continuous integrable real density
with a centered Fourier gap have the claimed asymptotic sign counts. -/
theorem integrableFourierGapSignAlternations : IntegrableFourierGapSignAlternations := by
  intro f s hs hf hInt hf₀ hGap positive c hc
  have hRight {g : ℝ → ℝ} (hg : Continuous g) (hgInt : Integrable g) (hg₀ : g ≠ 0)
      (hgGap : EqOn (𝓕 (fun x : ℝ => (g x : ℂ))) 0 (Ioo (-s) s)) :
      ∀ᶠ r : ℝ in atTop, ∃ n : ℕ, c * r ≤ (n : ℝ) ∧ HasSignAlternations g (Icc 0 r) n := by
    have hComplex : (fun x : ℝ => (g x : ℂ)) ≠ 0 := by
      intro h
      apply hg₀
      funext x
      exact Complex.ofReal_eq_zero.mp (congrFun h x)
    have hSupport (a : ℝ) : ∃ x > a, g x ≠ 0 := by
      obtain ⟨x, hx, hx₀⟩ := exists_nonzero_to_right_of_fourier_gap
        (Complex.continuous_ofReal.comp hg) hgInt.ofReal hComplex hs hgGap a
      exact ⟨x, hx, fun he => hx₀ (Complex.ofReal_eq_zero.mpr he)⟩
    exact eventually_original_positive_ray_signAlternations_of_unbounded_nonzero
      hgInt hg hg₀ hs hgGap hSupport hc
  cases positive
  · let g (x : ℝ) := f (-x)
    have hg : Continuous g := hf.comp continuous_neg
    have hgInt : Integrable g :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hInt
    have hg₀ : g ≠ 0 := by
      intro h
      apply hf₀
      funext x
      simpa only [g, neg_neg, Pi.zero_apply] using congrFun h (-x)
    have hgGap : EqOn (𝓕 (fun x : ℝ => (g x : ℂ))) 0 (Ioo (-s) s) := by
      intro ξ hξ
      have hFourier : 𝓕 (fun x : ℝ => (g x : ℂ)) ξ = 𝓕 (fun x : ℝ => (f x : ℂ)) (-ξ) :=
        fourier_comp_real_neg (fun x : ℝ => (f x : ℂ)) ξ
      rw [hFourier]
      exact hGap ⟨by linarith only [hξ.2], by linarith only [hξ.1]⟩
    filter_upwards [hRight hg hgInt hg₀ hgGap] with r hr
    obtain ⟨n, hn, hAlt⟩ := hr
    exact ⟨n, hn, hasSignAlternations_negative_ray_of_reflect hAlt⟩
  · exact hRight hf hInt hf₀ hGap

/-- The lower count on either ray of an original atomic Fourier-gap
distribution follows without additional oscillation or support premises. -/
theorem atomicFourierGapRayLowerBound : AtomicFourierGapRayLowerBound :=
  atomicFourierGapRayLowerBound_of_integrable_signAlternations
    integrableFourierGapSignAlternations

end
end MeyerGeneralProblem
