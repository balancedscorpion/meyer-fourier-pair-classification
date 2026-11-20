module

public import MeyerGeneralProblem.Sampling.KNSGaussianRateFiniteness
public import MeyerGeneralProblem.Sampling.KNSFourierEntirePair
public import MeyerGeneralProblem.Sampling.KNSPointwiseGaussian
public import Mathlib.Tactic

@[expose] public section

/-!
# Finite common-rate iteration against the actual quadratic-type theorem

The analytic common-rate closure is an explicit hypothesis. This conditional
consumer does not prove four-sign closure, select optimal rates, or replace
the actual entire-function cap theorem by an assumed cap certificate.
-/

namespace MeyerGeneralProblem
open MeasureTheory
open scoped FourierTransform

/-- One fixed increment propagates the actual paired whole-line predicate
to every finite arithmetic iterate, retaining both components at each step. -/
theorem common_rates_nat {E F : ℂ → ℂ} {κ₀ γ : ℝ} (hγ : 0 ≤ γ)
    (hseed : HasWholeGaussianRate E κ₀ ∧ HasWholeGaussianRate F κ₀)
    (hstep : ∀ κ : ℝ, κ₀ ≤ κ →
      HasWholeGaussianRate E κ → HasWholeGaussianRate F κ →
      HasWholeGaussianRate E (κ+γ) ∧ HasWholeGaussianRate F (κ+γ))
    (n : ℕ) :
    HasWholeGaussianRate E (κ₀+(n : ℝ)*γ) ∧
      HasWholeGaussianRate F (κ₀+(n : ℝ)*γ) := by
  induction n with
  | zero => simpa using hseed
  | succ n ih =>
    have hle : κ₀ ≤ κ₀+(n : ℝ)*γ :=
      le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hγ)
    have hnext := hstep _ hle ih.1 ih.2
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc] using hnext

/-- Actual entire quadratic growth on each component, a common positive
seed, and a fixed positive common-rate closure force both entire functions
to vanish. Each finite cap is obtained from the proved zero-safe theorem. -/
theorem both_zero_of_actual_quadratic_bounds_and_common_step
    {E F : ℂ → ℂ} (hE : Differentiable ℂ E) (hF : Differentiable ℂ F)
    {AE BE AF BF κ₀ γ : ℝ}
    (hAE : 0 ≤ AE) (hBE : 0 ≤ BE) (hAF : 0 ≤ AF) (hBF : 0 ≤ BF)
    (hquadE : ∀ z : ℂ, ‖E z‖ ≤ AE*Real.exp (BE*‖z‖^2))
    (hquadF : ∀ z : ℂ, ‖F z‖ ≤ AF*Real.exp (BF*‖z‖^2))
    (hγ : 0 < γ)
    (hseed : HasWholeGaussianRate E κ₀ ∧ HasWholeGaussianRate F κ₀)
    (hstep : ∀ κ : ℝ, κ₀ ≤ κ →
      HasWholeGaussianRate E κ → HasWholeGaussianRate F κ →
      HasWholeGaussianRate E (κ+γ) ∧ HasWholeGaussianRate F (κ+γ)) :
    E = 0 ∧ F = 0 := by
  have hall := common_rates_nat hγ.le hseed hstep
  have hexceed (L : ℝ) : ∃ n : ℕ, L < κ₀+(n : ℝ)*γ := by
    obtain ⟨n, hn⟩ := exists_nat_gt ((L-κ₀)/γ)
    refine ⟨n, ?_⟩
    have hm := (div_lt_iff₀ hγ).mp hn
    linarith
  constructor
  · rcases eq_zero_or_gaussianRate_le_of_quadraticType hE hAE hBE hquadE with hz | hcap
    · exact hz
    obtain ⟨n, hn⟩ := hexceed (BE/Real.pi)
    exact False.elim ((not_lt_of_ge (hcap _ (hall n).1)) hn)
  · rcases eq_zero_or_gaussianRate_le_of_quadraticType hF hAF hBF hquadF with hz | hcap
    · exact hz
    obtain ⟨n, hn⟩ := hexceed (BF/Real.pi)
    exact False.elim ((not_lt_of_ge (hcap _ (hall n).2)) hn)

/-- Actual continuous Gaussian-square-integrable Fourier pairs vanish if
their common whole-line rates have one fixed positive improvement step.
The Gaussian hypotheses construct the representatives, seed and type bounds;
the common-rate improvement is supplied separately. -/
theorem actual_fourier_pair_zero_of_common_step
    {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ} (hf : Continuous f)
    (hg : Integrable (fun x => Real.exp (a*x^2)*‖f x‖^2))
    (hFg : Integrable (fun x => Real.exp (a*x^2)*‖𝓕 f x‖^2))
    {γ : ℝ} (hγ : 0 < γ)
    (hstep : ∀ κ : ℝ, a/(6*Real.pi) ≤ κ →
      HasWholeGaussianRate (knsPhysicalEntire f) κ →
      HasWholeGaussianRate (knsFourierEntire f) κ →
      HasWholeGaussianRate (knsPhysicalEntire f) (κ+γ) ∧
        HasWholeGaussianRate (knsFourierEntire f) (κ+γ)) :
    f = 0 ∧ knsPhysicalEntire f = 0 ∧ knsFourierEntire f = 0 := by
  have hf1 := integrable_of_gaussian_square ha hf.aestronglyMeasurable hg
  have hFc : Continuous (𝓕 f : ℝ → ℂ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf1
  have hF1 := integrable_of_gaussian_square ha hFc.aestronglyMeasurable hFg
  obtain ⟨AP, hAP, hquadP⟩ := exists_knsPhysicalEntire_quadraticBound ha
    hF1.aestronglyMeasurable hFg
  obtain ⟨AF, hAF, hquadF⟩ := exists_knsFourierEntire_quadraticBound ha
    hf.aestronglyMeasurable hg
  obtain ⟨C, hC, hseed⟩ :=
    exists_pointwise_gaussian_of_gaussian_fourier_pair ha hf hg hFg
  have hk : 0 < a/(6*Real.pi) := by positivity
  have hexp (x : ℝ) : -(a/3)*x^2 = -2*Real.pi*(a/(6*Real.pi))*x^2 := by
    field_simp
    ring
  have hseedP : HasWholeGaussianRate (knsPhysicalEntire f) (a/(6*Real.pi)) := by
    refine ⟨hk,C,hC,?_⟩
    intro x
    rw [knsPhysicalEntire_ofReal hf hf1 hF1]
    simpa only [hexp] using (hseed x).1
  have hseedF : HasWholeGaussianRate (knsFourierEntire f) (a/(6*Real.pi)) := by
    refine ⟨hk,C,hC,?_⟩
    intro x
    rw [knsFourierEntire_ofReal]
    simpa only [hexp] using (hseed x).2
  have hz := both_zero_of_actual_quadratic_bounds_and_common_step
    (differentiable_knsPhysicalEntire ha hF1.aestronglyMeasurable hFg)
    (differentiable_knsFourierEntire ha hf.aestronglyMeasurable hg)
    hAP.le (by positivity) hAF.le (by positivity) hquadP hquadF
    hγ ⟨hseedP,hseedF⟩ hstep
  refine ⟨?_,hz⟩
  funext x
  simpa only [knsPhysicalEntire_ofReal hf hf1 hF1, Pi.zero_apply] using
    congrFun hz.1 (x : ℂ)

end MeyerGeneralProblem
