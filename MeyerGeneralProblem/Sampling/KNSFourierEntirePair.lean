module

public import MeyerGeneralProblem.Sampling.KNSQuadraticEntire

@[expose] public section

/-!
# Actual physical and Fourier entire representatives

The Fourier representative is the genuine negative-phase Fourier integral.
The physical representative applies that integral to the Fourier transform
and reflects its complex argument, as required by double Fourier inversion.
Positive Gaussian square integrability proves actual entire differentiability
and a radial quadratic bound for both representatives. No parity, root
composition, sector estimate or optimal-rate assertion is built into them.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory
open scoped FourierTransform

/-- The actual entire candidate whose real restriction is the Fourier transform. -/
def knsFourierEntire (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  bandFourierExtension f z

/-- The physical entire candidate has a reflected complex argument. This
reflection compensates for the repository's double-Fourier convention. -/
def knsPhysicalEntire (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  bandFourierExtension (𝓕 f) (-z)

/-- The frequency-side representative restricts to the ordinary Fourier integral. -/
theorem knsFourierEntire_ofReal (f : ℝ → ℂ) (x : ℝ) :
    knsFourierEntire f (x : ℂ) = 𝓕 f x :=
  bandFourierExtension_ofReal f x

/-- Actual continuous Fourier inversion, not an evenness assumption, makes
the reflected representative restrict to the original physical function. -/
theorem knsPhysicalEntire_ofReal {f : ℝ → ℂ} (hf : Continuous f)
    (hf1 : Integrable f) (hF1 : Integrable (𝓕 f)) (x : ℝ) :
    knsPhysicalEntire f (x : ℂ) = f x := by
  dsimp only [knsPhysicalEntire]
  rw [← Complex.ofReal_neg, bandFourierExtension_ofReal,
    kns_fourier_fourier_eq_reflection hf hf1 hF1, neg_neg]

/-- A positive Gaussian square weight makes the actual frequency representative entire. -/
theorem differentiable_knsFourierEntire {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hgauss : Integrable (fun x => Real.exp (a*x^2)*‖f x‖^2)) :
    Differentiable ℂ (knsFourierEntire f) :=
  differentiable_knsFourierLaplace ha hf hgauss

/-- A positive Gaussian square weight on the actual Fourier transform makes
the reflected physical representative entire. -/
theorem differentiable_knsPhysicalEntire {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hF : AEStronglyMeasurable (𝓕 f) volume)
    (hgauss : Integrable (fun x => Real.exp (a*x^2)*‖𝓕 f x‖^2)) :
    Differentiable ℂ (knsPhysicalEntire f) :=
  (differentiable_knsFourierLaplace ha hF hgauss).comp differentiable_neg

private theorem exists_bandFourierExtension_radial_quadratic
    {a : ℝ} (ha : 0 < a) {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g volume)
    (hgauss : Integrable (fun x => Real.exp (a*x^2)*‖g x‖^2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖bandFourierExtension g z‖ ≤ C * Real.exp ((8*Real.pi^2/a)*‖z‖^2) := by
  obtain ⟨_, _, C, hC, hbound⟩ := knsGaussian_fourier_entire ha hg hgauss
  refine ⟨C, hC, fun z => (hbound z).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 8*Real.pi^2/a)
  have him := Complex.abs_im_le_norm z
  have hs := (sq_le_sq₀ (abs_nonneg z.im) (norm_nonneg z)).2 him
  simpa only [sq_abs] using hs

/-- The frequency representative has a genuine positive radial quadratic
bound constant, derived from the supplied Gaussian square integral. -/
theorem exists_knsFourierEntire_quadraticBound
    {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume)
    (hgauss : Integrable (fun x => Real.exp (a*x^2)*‖f x‖^2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖knsFourierEntire f z‖ ≤ C * Real.exp ((8*Real.pi^2/a)*‖z‖^2) :=
  exists_bandFourierExtension_radial_quadratic ha hf hgauss

/-- Reflection preserves the radial quadratic bound for the actual physical
representative; no Fourier-sign or carrier symmetry assumption is used. -/
theorem exists_knsPhysicalEntire_quadraticBound
    {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hF : AEStronglyMeasurable (𝓕 f) volume)
    (hgauss : Integrable (fun x => Real.exp (a*x^2)*‖𝓕 f x‖^2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖knsPhysicalEntire f z‖ ≤ C * Real.exp ((8*Real.pi^2/a)*‖z‖^2) := by
  obtain ⟨C, hC, hbound⟩ := exists_bandFourierExtension_radial_quadratic ha hF hgauss
  refine ⟨C, hC, fun z => ?_⟩
  simpa only [knsPhysicalEntire, norm_neg] using hbound (-z)

end

end MeyerGeneralProblem
