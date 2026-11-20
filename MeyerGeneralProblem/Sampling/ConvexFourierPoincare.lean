module

public import MeyerGeneralProblem.Sampling.ConvexPoincare

@[expose] public section

/-!
# Convex Poincare for the actual classical Fourier integral

Compactly supported C1 localizations have integrable functions and derivatives.
On this genuine common domain the usual positive angular derivative formula
and Plancherel identify the second frequency moment with no reflection choice.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set
open scoped FourierTransform

/-- The classical Fourier integral of actual L1 C1 data with L2 derivative has
finite second moment with the exact positive angular normalization. -/
theorem classicalFourier_secondMoment_of_deriv
    {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hD : MemLp (deriv f) 2)
    (hL1 : Integrable f) (hD1 : Integrable (deriv f)) :
    Integrable (fun x => x^2*‖𝓕 f x‖^2) ∧
      (∫ x, ‖deriv f x‖^2) = (2*Real.pi)^2*(∫ x, x^2*‖𝓕 f x‖^2) := by
  obtain ⟨hFD,hFDnorm⟩ := memLp_fourier_norm_eq_of_integrable hD1 hD
  have hderiv := Real.fourier_deriv hL1 (hf.differentiable (by norm_num)) hD1
  have he (x : ℝ) : ‖𝓕 (deriv f) x‖^2 = (2*Real.pi)^2*(x^2*‖𝓕 f x‖^2) := by
    rw [hderiv]
    simp only [norm_smul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one,
      mul_pow, sq_abs]
    ring
  have hM := integrable_norm_sq_of_memLp_complex hFD
  have hefun : (fun x => x^2*‖𝓕 f x‖^2) =
      fun x => ((2*Real.pi)^2)⁻¹*‖𝓕 (deriv f) x‖^2 := by
    funext x
    rw [he]
    field_simp
  have hxi : Integrable (fun x => x^2*‖𝓕 f x‖^2) := by
    rw [hefun]
    exact hM.const_mul _
  refine ⟨hxi, ?_⟩
  have hnorm' : (∫ x, ‖𝓕 (deriv f) x‖^2) = ∫ x, ‖deriv f x‖^2 := by
    rw [integral_norm_sq_eq_toLp_norm_sq_complex hFD, hFDnorm,
      integral_norm_sq_eq_toLp_norm_sq_complex hD]
  rw [← hnorm']
  simp_rw [he]
  exact integral_const_mul _ _

/-- The sharp convex zero-gap inequality for the actual classical
Fourier integral. Only active gaps need bounds, so the finite core can
be inactive under localization; all weighted integrability is explicit. -/
theorem convex_classicalFourier_poincare_of_active_twoSided_zeros
    (Λ : TwoSidedCarrier) {t : ℝ} (ht : 0 < t)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hzero : ∀ j : ℤ, f (Λ j) = 0)
    (hgap : ∀ j : ℤ, (∃ x ∈ Ioc (Λ j) (Λ (j+1)), f x ≠ 0) →
      Λ (j+1)-Λ j ≤ (2*t)⁻¹)
    (hF : MemLp f 2) (hD : MemLp (deriv f) 2)
    (hL1 : Integrable f) (hD1 : Integrable (deriv f))
    (Φ : ℝ → ℝ) (hΦ : ConvexOn ℝ (Ici 0) Φ) (hmono : MonotoneOn Φ (Ici 0))
    (hd : DifferentiableAt ℝ Φ (t^2))
    (hΦi : Integrable (fun x => Φ (x^2)*‖𝓕 f x‖^2)) :
    Φ (t^2)*(∫ x, ‖f x‖^2) ≤ ∫ x, Φ (x^2)*‖𝓕 f x‖^2 := by
  obtain ⟨hG,hGnorm⟩ := memLp_fourier_norm_eq_of_integrable hL1 hF
  have hmass : (∫ x, ‖𝓕 f x‖^2) = ∫ x, ‖f x‖^2 := by
    rw [integral_norm_sq_eq_toLp_norm_sq_complex hG, hGnorm,
      integral_norm_sq_eq_toLp_norm_sq_complex hF]
  obtain ⟨hxi,henergy⟩ := classicalFourier_secondMoment_of_deriv hf hD hL1 hD1
  have hp := complex_poincare_of_active_twoSided_zeros Λ (by positivity) f hf hzero hgap
    (integrable_norm_sq_of_memLp_complex hF) (integrable_norm_sq_of_memLp_complex hD)
  rw [henergy] at hp
  have hsecond : t^2*(∫ x, ‖𝓕 f x‖^2) ≤ ∫ x, x^2*‖𝓕 f x‖^2 := by
    rw [hmass]
    have hmul := mul_le_mul_of_nonneg_left hp (sq_nonneg (2*t))
    have hp0 : Real.pi ≠ 0 := Real.pi_ne_zero
    have ht0 : t ≠ 0 := ht.ne'
    field_simp at hmul
    nlinarith [sq_pos_of_pos Real.pi_pos]
  have h := convex_weighted_integral_of_secondMoment (fun x => ‖𝓕 f x‖^2)
    (fun _ => sq_nonneg _) (integrable_norm_sq_of_memLp_complex hG) hxi
    (sq_pos_of_pos ht) hsecond Φ hΦ hmono hd hΦi
  rwa [hmass] at h

end

end MeyerGeneralProblem
