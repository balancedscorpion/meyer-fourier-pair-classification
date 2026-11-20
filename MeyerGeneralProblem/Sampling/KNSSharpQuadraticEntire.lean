module

public import MeyerGeneralProblem.Sampling.KNSQuadraticEntire

@[expose] public section

/-!
# Sharp quadratic Fourier bounds from actual pointwise Gaussian decay

Completing the square in the exact negative-frequency phase gives the
reciprocal coefficient without a Young-inequality loss. The measurable
Fourier-Laplace integrand is proved integrable separately. The normalized
and polar statements use a given positive pointwise decay rate; no optimal
rate, indicator, sector estimate, or uniqueness hypothesis is involved.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory

private theorem sharp_gaussian_complete_square {a : ℝ} (ha : 0 < a) (b x : ℝ) :
    -a*x^2+b*x = b^2/(4*a)+(-a)*(x-b/(2*a))^2 := by
  field_simp
  ring

private theorem sharp_gaussian_linear_integrable {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-a*x^2+b*x)) := by
  simp_rw [sharp_gaussian_complete_square ha b, Real.exp_add]
  exact ((integrable_exp_neg_mul_sq ha).comp_sub_right (b/(2*a))).const_mul
    (Real.exp (b^2/(4*a)))

private theorem sharp_gaussian_linear_integral {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (∫ x : ℝ, Real.exp (-a*x^2+b*x)) =
      Real.exp (b^2/(4*a))*Real.sqrt (Real.pi/a) := by
  simp_rw [sharp_gaussian_complete_square ha b, Real.exp_add]
  rw [integral_const_mul,
    integral_sub_right_eq_self (fun x : ℝ => Real.exp (-a*x^2)) (b/(2*a)),
    integral_gaussian]

private theorem sharp_gaussian_integrand_bound {a C : ℝ} {g : ℝ → ℂ}
    (hdecay : ∀ x : ℝ, ‖g x‖ ≤ C*Real.exp (-a*x^2)) (z : ℂ) (x : ℝ) :
    ‖Complex.exp (((-2*Real.pi*x : ℝ) : ℂ)*Complex.I*z)*g x‖ ≤
      C*Real.exp (-a*x^2+(2*Real.pi*z.im)*x) := by
  rw [norm_mul, norm_knsFourierLaplace_phase]
  calc
    _ ≤ Real.exp (2*Real.pi*x*z.im)*(C*Real.exp (-a*x^2)) :=
      mul_le_mul_of_nonneg_left (hdecay x) (Real.exp_pos _).le
    _ = C*(Real.exp (-a*x^2)*Real.exp (2*Real.pi*x*z.im)) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring

/-- A measurable function with an actual positive Gaussian norm bound has
a genuinely integrable Fourier-Laplace integrand at every complex point. -/
theorem integrable_bandFourierExtension_integrand_of_gaussianBound
    {a C : ℝ} (ha : 0 < a) {g : ℝ → ℂ}
    (hgmeas : AEStronglyMeasurable g volume)
    (hdecay : ∀ x : ℝ, ‖g x‖ ≤ C*Real.exp (-a*x^2)) (z : ℂ) :
    Integrable (fun x : ℝ =>
      Complex.exp (((-2*Real.pi*x : ℝ) : ℂ)*Complex.I*z)*g x) := by
  apply ((sharp_gaussian_linear_integrable ha (2*Real.pi*z.im)).const_mul C).mono'
    ((show Continuous (fun x : ℝ =>
      Complex.exp (((-2*Real.pi*x : ℝ) : ℂ)*Complex.I*z)) by
        fun_prop).aestronglyMeasurable.mul hgmeas)
  exact Filter.Eventually.of_forall (sharp_gaussian_integrand_bound hdecay z)

/-- Exact completion of the square gives the sharp coefficient `pi^2/a`
from a pointwise Gaussian bound, with the full Gaussian integral prefactor. -/
theorem norm_bandFourierExtension_le_of_gaussianBound
    {a C : ℝ} (ha : 0 < a) {g : ℝ → ℂ}
    (hgmeas : AEStronglyMeasurable g volume)
    (hdecay : ∀ x : ℝ, ‖g x‖ ≤ C*Real.exp (-a*x^2)) (z : ℂ) :
    ‖bandFourierExtension g z‖ ≤
      C*Real.sqrt (Real.pi/a)*Real.exp ((Real.pi^2/a)*z.im^2) := by
  have hint := integrable_bandFourierExtension_integrand_of_gaussianBound ha hgmeas hdecay z
  have h := (norm_integral_le_integral_norm _).trans
    (integral_mono hint.norm
      ((sharp_gaussian_linear_integrable ha (2*Real.pi*z.im)).const_mul C)
      (sharp_gaussian_integrand_bound hdecay z))
  change ‖bandFourierExtension g z‖ ≤ _ at h
  refine h.trans_eq ?_
  rw [integral_const_mul, sharp_gaussian_linear_integral ha]
  have he : (2*Real.pi*z.im)^2/(4*a) = (Real.pi^2/a)*z.im^2 := by
    field_simp
    ring
  rw [he]
  ring

/-- The normalized decay `exp(-2*pi*kappa*x^2)` supplies actual integrability
of the Fourier-Laplace integrand, independently of the norm estimate. -/
theorem integrable_bandFourierExtension_integrand_of_pointwiseGaussian
    {κ C : ℝ} (hκ : 0 < κ) {g : ℝ → ℂ}
    (hgmeas : AEStronglyMeasurable g volume)
    (hdecay : ∀ x : ℝ, ‖g x‖ ≤ C*Real.exp (-2*Real.pi*κ*x^2)) (z : ℂ) :
    Integrable (fun x : ℝ =>
      Complex.exp (((-2*Real.pi*x : ℝ) : ℂ)*Complex.I*z)*g x) := by
  apply integrable_bandFourierExtension_integrand_of_gaussianBound
    (a := 2*Real.pi*κ) (by positivity) hgmeas
  simpa only [neg_mul] using hdecay

/-- The exact KNS normalization gives prefactor `sqrt(1/(2*kappa))` and
imaginary-direction coefficient `pi/(2*kappa)` for each given positive rate. -/
theorem norm_bandFourierExtension_le_of_pointwiseGaussian
    {κ C : ℝ} (hκ : 0 < κ) (hC : 0 ≤ C) {g : ℝ → ℂ}
    (hgmeas : AEStronglyMeasurable g volume)
    (hdecay : ∀ x : ℝ, ‖g x‖ ≤ C*Real.exp (-2*Real.pi*κ*x^2)) (z : ℂ) :
    ‖bandFourierExtension g z‖ ≤
      C*Real.sqrt (1/(2*κ))*Real.exp ((Real.pi/(2*κ))*z.im^2) := by
  have h := norm_bandFourierExtension_le_of_gaussianBound
    (a := 2*Real.pi*κ) (by positivity) hgmeas (by simpa only [neg_mul] using hdecay) z
  have hroot : Real.pi/(2*Real.pi*κ) = 1/(2*κ) := by
    field_simp
  have hexp : Real.pi^2/(2*Real.pi*κ) = Real.pi/(2*κ) := by
    field_simp
  rw [hexp] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by rw [hroot]) hC) (Real.exp_pos _).le)

/-- On every polar ray the normalized quadratic coefficient is exactly
`2*pi*(sin(theta)^2/(4*kappa))`. The identity also covers radius zero and
negative real radius, without an angular or sector restriction. -/
theorem norm_bandFourierExtension_ray_le_of_pointwiseGaussian
    {κ C : ℝ} (hκ : 0 < κ) (hC : 0 ≤ C) {g : ℝ → ℂ}
    (hgmeas : AEStronglyMeasurable g volume)
    (hdecay : ∀ x : ℝ, ‖g x‖ ≤ C*Real.exp (-2*Real.pi*κ*x^2)) (r θ : ℝ) :
    ‖bandFourierExtension g ((r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I))‖ ≤
      C*Real.sqrt (1/(2*κ))*
        Real.exp ((2*Real.pi*(Real.sin θ^2/(4*κ)))*r^2) := by
  have h := norm_bandFourierExtension_le_of_pointwiseGaussian hκ hC hgmeas hdecay
    ((r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I))
  have him : ((r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I)).im = r*Real.sin θ := by
    simp [Complex.exp_im]
  rw [him] at h
  have he : (Real.pi/(2*κ))*(r*Real.sin θ)^2 =
      (2*Real.pi*(Real.sin θ^2/(4*κ)))*r^2 := by
    field_simp
    ring
  rwa [he] at h

end

end MeyerGeneralProblem
