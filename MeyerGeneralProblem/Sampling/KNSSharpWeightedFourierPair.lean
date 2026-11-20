module

public import MeyerGeneralProblem.Sampling.KNSFourierEntirePair
public import MeyerGeneralProblem.Sampling.KNSSharpWeightedRoot
public import MeyerGeneralProblem.Sampling.KNSWeightedRootContinuity

@[expose] public section

/-!
# Sharp weighted-root bounds for the actual Fourier pair

The independent opposite-side Gaussian rate supplies the exact prefactor and
imaginary-direction bound. Actual positive Gaussian square integrability is
retained separately to prove the entire-input and boundary-continuity claims.
The physical representative keeps its reflected argument and actual Fourier
inversion assumptions. No equality of rates, parity, optimal-rate attainment,
or Phragmen-Lindelof sector estimate is assumed or concluded.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory
open scoped FourierTransform

/-- A whole-line pointwise Gaussian bound on the actual physical data gives
the exact sharp imaginary-direction bound for its Fourier representative. -/
theorem norm_knsFourierEntire_le_of_pointwiseGaussian
    {η Cη : ℝ} (hη : 0 < η) (hCη : 0 ≤ Cη) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume)
    (hpoint : ∀ t : ℝ, ‖f t‖ ≤ Cη * Real.exp (-2 * Real.pi * η * t ^ 2))
    (z : ℂ) :
    ‖knsFourierEntire f z‖ ≤ Cη * Real.sqrt (1 / (2 * η)) *
      Real.exp ((Real.pi / (2 * η)) * z.im ^ 2) :=
  norm_bandFourierExtension_le_of_pointwiseGaussian hη hCη hf hpoint z

/-- The sharp bound for the actual reflected physical representative comes
from a whole-line Gaussian bound on the Fourier data. Reflection preserves
the squared imaginary part; no parity assumption is used. -/
theorem norm_knsPhysicalEntire_le_of_pointwiseGaussian
    {η Cη : ℝ} (hη : 0 < η) (hCη : 0 ≤ Cη) {f : ℝ → ℂ}
    (hF : AEStronglyMeasurable (𝓕 f) volume)
    (hpoint : ∀ t : ℝ, ‖𝓕 f t‖ ≤ Cη * Real.exp (-2 * Real.pi * η * t ^ 2))
    (z : ℂ) :
    ‖knsPhysicalEntire f z‖ ≤ Cη * Real.sqrt (1 / (2 * η)) *
      Real.exp ((Real.pi / (2 * η)) * z.im ^ 2) := by
  simpa only [knsPhysicalEntire, Complex.neg_im, neg_sq] using
    norm_bandFourierExtension_le_of_pointwiseGaussian hη hCη hF hpoint (-z)

/-- The actual frequency-side weighted root has closure continuity, open
analyticity, selected real decay and the three sharp norm estimates. Its
entire input is proved from the displayed Gaussian square integral, while
the independent whole-line rate eta fixes the exact prefactor. The polar
bound is uniform in positive epsilon, not a sector-growth conclusion. -/
theorem knsWeightedFourierRoot_sharp_properties
    {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    {a sgn κ ε η Creal Cη : ℝ} (ha : 0 < a)
    (hgauss : Integrable (fun t => Real.exp (a * t ^ 2) * ‖f t‖ ^ 2))
    (hsgn : sgn = 1 ∨ sgn = -1) (_hκ : 0 < κ) (hε : 0 < ε)
    (hη : 0 < η) (_hCreal : 0 ≤ Creal) (hCη : 0 ≤ Cη)
    (hreal : ∀ t : ℝ, 0 ≤ t →
      ‖𝓕 f (sgn * t)‖ ≤ Creal * Real.exp (-2 * Real.pi * κ * t ^ 2))
    (hpoint : ∀ t : ℝ, ‖f t‖ ≤ Cη * Real.exp (-2 * Real.pi * η * t ^ 2)) :
    let H := knsWeightedPrincipalRoot sgn κ ε (knsFourierEntire f)
    let A := Cη * Real.sqrt (1 / (2 * η))
    ContinuousOn H {w : ℂ | 0 ≤ w.re} ∧
      AnalyticOnNhd ℂ H {w : ℂ | 0 < w.re} ∧
      DiffContOnCl ℂ H {w : ℂ | 0 < w.re} ∧
      (∀ x : ℝ, 0 ≤ x → ‖H (x : ℂ)‖ ≤ Creal * Real.exp (-ε * x)) ∧
      (∀ w : ℂ, ‖H w‖ ≤ A * Real.exp ((Real.pi / (4 * η)) * ‖w‖ +
        (2 * Real.pi * κ - ε - Real.pi / (4 * η)) * w.re)) ∧
      (∀ r θ : ℝ, 0 ≤ r → 0 ≤ Real.cos θ →
        ‖H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤
          A * Real.exp (Real.pi * r * (2 * κ * Real.cos θ +
            (1 - Real.cos θ) / (4 * η)))) ∧
      (∀ w : ℂ, ‖H w‖ ≤ A * Real.exp ((Real.pi / (4 * η) +
        |2 * Real.pi * κ - ε - Real.pi / (4 * η)|) * ‖w‖)) := by
  dsimp only
  have hE := differentiable_knsFourierEntire ha hf hgauss
  have hA : 0 ≤ Cη * Real.sqrt (1 / (2 * η)) :=
    mul_nonneg hCη (Real.sqrt_nonneg _)
  have hsharp := norm_knsFourierEntire_le_of_pointwiseGaussian hη hCη hf hpoint
  have hrealE : ∀ t : ℝ, 0 ≤ t →
      ‖knsFourierEntire f (((sgn * t : ℝ) : ℂ))‖ ≤
        Creal * Real.exp (-2 * Real.pi * κ * t ^ 2) := by
    intro t ht
    simpa only [knsFourierEntire_ofReal] using hreal t ht
  refine ⟨continuousOn_knsWeightedPrincipalRoot_closedRightHalfPlane sgn κ ε hE.continuous,
    analyticOnNhd_knsWeightedPrincipalRoot sgn κ ε hE,
    diffContOnCl_knsWeightedPrincipalRoot sgn κ ε hE, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact norm_knsWeightedPrincipalRoot_real_le sgn κ ε hrealE hx
  · intro w
    exact norm_knsWeightedPrincipalRoot_le_sharp hsgn hη hsharp w
  · intro r θ hr hcos
    exact norm_knsWeightedPrincipalRoot_ray_le_sharp_uniform hsgn hη hA hε.le hsharp hr hcos
  · intro w
    exact norm_knsWeightedPrincipalRoot_le_sharp_linear hsgn hη hA hsharp w

/-- The physical-side sharp package uses the genuine reflected Fourier
representative and retains continuity and both L1 inversion assumptions.
Gaussian square integrability of the Fourier data proves entire regularity;
its independent whole-line pointwise rate gives the exact sharp prefactor.
The selected real bound concerns the original physical function. -/
theorem knsWeightedPhysicalRoot_sharp_properties
    {f : ℝ → ℂ} (hf : Continuous f) (hf1 : Integrable f) (hF1 : Integrable (𝓕 f))
    {a sgn κ ε η Creal Cη : ℝ} (ha : 0 < a)
    (hgauss : Integrable (fun t => Real.exp (a * t ^ 2) * ‖𝓕 f t‖ ^ 2))
    (hsgn : sgn = 1 ∨ sgn = -1) (_hκ : 0 < κ) (hε : 0 < ε)
    (hη : 0 < η) (_hCreal : 0 ≤ Creal) (hCη : 0 ≤ Cη)
    (hreal : ∀ t : ℝ, 0 ≤ t →
      ‖f (sgn * t)‖ ≤ Creal * Real.exp (-2 * Real.pi * κ * t ^ 2))
    (hpoint : ∀ t : ℝ, ‖𝓕 f t‖ ≤ Cη * Real.exp (-2 * Real.pi * η * t ^ 2)) :
    let H := knsWeightedPrincipalRoot sgn κ ε (knsPhysicalEntire f)
    let A := Cη * Real.sqrt (1 / (2 * η))
    ContinuousOn H {w : ℂ | 0 ≤ w.re} ∧
      AnalyticOnNhd ℂ H {w : ℂ | 0 < w.re} ∧
      DiffContOnCl ℂ H {w : ℂ | 0 < w.re} ∧
      (∀ x : ℝ, 0 ≤ x → ‖H (x : ℂ)‖ ≤ Creal * Real.exp (-ε * x)) ∧
      (∀ w : ℂ, ‖H w‖ ≤ A * Real.exp ((Real.pi / (4 * η)) * ‖w‖ +
        (2 * Real.pi * κ - ε - Real.pi / (4 * η)) * w.re)) ∧
      (∀ r θ : ℝ, 0 ≤ r → 0 ≤ Real.cos θ →
        ‖H ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤
          A * Real.exp (Real.pi * r * (2 * κ * Real.cos θ +
            (1 - Real.cos θ) / (4 * η)))) ∧
      (∀ w : ℂ, ‖H w‖ ≤ A * Real.exp ((Real.pi / (4 * η) +
        |2 * Real.pi * κ - ε - Real.pi / (4 * η)|) * ‖w‖)) := by
  dsimp only
  have hE := differentiable_knsPhysicalEntire ha hF1.aestronglyMeasurable hgauss
  have hA : 0 ≤ Cη * Real.sqrt (1 / (2 * η)) :=
    mul_nonneg hCη (Real.sqrt_nonneg _)
  have hsharp := norm_knsPhysicalEntire_le_of_pointwiseGaussian hη hCη
    hF1.aestronglyMeasurable hpoint
  have hrealE : ∀ t : ℝ, 0 ≤ t →
      ‖knsPhysicalEntire f (((sgn * t : ℝ) : ℂ))‖ ≤
        Creal * Real.exp (-2 * Real.pi * κ * t ^ 2) := by
    intro t ht
    simpa only [knsPhysicalEntire_ofReal hf hf1 hF1] using hreal t ht
  refine ⟨continuousOn_knsWeightedPrincipalRoot_closedRightHalfPlane sgn κ ε hE.continuous,
    analyticOnNhd_knsWeightedPrincipalRoot sgn κ ε hE,
    diffContOnCl_knsWeightedPrincipalRoot sgn κ ε hE, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact norm_knsWeightedPrincipalRoot_real_le sgn κ ε hrealE hx
  · intro w
    exact norm_knsWeightedPrincipalRoot_le_sharp hsgn hη hsharp w
  · intro r θ hr hcos
    exact norm_knsWeightedPrincipalRoot_ray_le_sharp_uniform hsgn hη hA hε.le hsharp hr hcos
  · intro w
    exact norm_knsWeightedPrincipalRoot_le_sharp_linear hsgn hη hA hsharp w

end

end MeyerGeneralProblem
