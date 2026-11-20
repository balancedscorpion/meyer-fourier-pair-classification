module

public import MeyerGeneralProblem.Sampling.KNSCommonRateStep
public import MeyerGeneralProblem.Sampling.KNSFiniteRateIteration
public import MeyerGeneralProblem.Carrier.FoldedSquaredTails

@[expose] public section

/-!
# Classical cofinite Fourier uniqueness from reciprocal gaps

The original carrier gaps and zeros construct all four signed squared tails.
The Gaussian bootstrap constructs the two actual weighted square integrals.
The common-rate closure and finite iteration force vanishing without an
assumed rate step, cap certificate, optimal rate, or reflection symmetry.
This is a classical-function theorem, not a completed-graph sampling theorem.
-/

namespace MeyerGeneralProblem
open MeasureTheory
open scoped FourierTransform

/-- Four independent actual signed squared zero tails with strict gap less than one
force a continuous Gaussian-square-integrable Fourier pair to vanish.
Both the common improvement and finite rate contradiction are derived. -/
theorem eq_zero_of_gaussian_pair_and_signedSquaredZeroTails
    {f : ℝ → ℂ} {a ell : ℝ} (hf : Continuous f) (ha : 0 < a)
    (hg : Integrable (fun x => Real.exp (a*x^2)*‖f x‖^2))
    (hFg : Integrable (fun x => Real.exp (a*x^2)*‖𝓕 f x‖^2))
    (hell0 : 0 < ell) (hell1 : ell < 1)
    (hzerosPhysical : SignedSquaredZeroTails f ell)
    (hzerosFourier : SignedSquaredZeroTails (𝓕 f) ell) :
    f = 0 ∧ knsPhysicalEntire f = 0 ∧ knsFourierEntire f = 0 := by
  obtain ⟨γ, hγ, hstep⟩ := exists_commonRate_step_actualFourierPair
    (κ₀ := a/(6*Real.pi)) hf ha hg hFg hell0 hell1 (by positivity)
    hzerosPhysical hzerosFourier
  exact actual_fourier_pair_zero_of_common_step ha hf hg hFg hγ hstep


/-- Original finite-exception carrier zeros and reciprocal gaps construct
independent ordered cofinal squared zero tails on both signs. -/
theorem signedSquaredZeroTails_of_carrier
    (Λ : TwoSidedCarrier) {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (Fzero Fgap : Finset ℤ)
    (hgap : ∀ j : ℤ, j ∉ Fgap →
      max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ ρ)
    {f : ℝ → ℂ} (hzero : ∀ j : ℤ, j ∉ Fzero → f (Λ j) = 0) :
    SignedSquaredZeroTails f (2*ρ) := by
  obtain ⟨Kpos, Kneg, hp, hn, hmp, htp, hgp, hmn, htn, hgn⟩ :=
    Λ.exists_foldedSquaredTails hρ hρhalf Fzero Fgap hgap
  intro sgn hsgn
  rcases hsgn with rfl | rfl
  · refine ⟨(fun n => Λ (Kpos+(n : ℤ))), 0, 0, hmp, htp,
      (fun n _ => hgp n), ?_⟩
    intro n _
    exact ⟨(hp n).1.le, by simpa only [one_mul] using hzero _ (hp n).2.1⟩
  · refine ⟨(fun n => -Λ (Kneg-(n : ℤ))), 0, 0, hmn, htn,
      (fun n _ => hgn n), ?_⟩
    intro n _
    exact ⟨(hn n).1.le, by simpa only [neg_one_mul, neg_neg] using hzero _ (hn n).2.1⟩

/-- Classical cofinite Fourier uniqueness under the original reciprocal-gap
hypotheses. The actual bootstrap derives both Gaussian square integrals;
the actual carrier constructor derives all four signed zero tails. -/
theorem knsClassicalUniqueness_of_reciprocal_gaps
    {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (Λ M : TwoSidedCarrier) (F J G L : Finset ℤ)
    (hgapΛ : ∀ j : ℤ, j ∉ J → max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ ρ)
    (hgapM : ∀ j : ℤ, j ∉ L → max |M j| |M (j+1)| * (M (j+1)-M j) ≤ ρ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hF : ContDiff ℝ 1 (𝓕 f))
    (hf1 : Integrable f) (hF1 : Integrable (𝓕 f)) (hf2 : MemLp f 2)
    (hx2 : Integrable (fun x => x^2*‖f x‖^2))
    (hξ2 : Integrable (fun ξ => ξ^2*‖𝓕 f ξ‖^2))
    (hzΛ : ∀ j : ℤ, j ∉ F → f (Λ j) = 0)
    (hzM : ∀ j : ℤ, j ∉ G → 𝓕 f (M j) = 0) :
    f = 0 := by
  obtain ⟨hg,hFg⟩ := knsGaussianDecay_of_reciprocal_gaps hρ hρhalf Λ M F J G L
    hgapΛ hgapM hf hF hf1 hF1 hf2 hx2 hξ2 hzΛ hzM
  have ha := (knsGaussianParameter_properties hρ hρhalf).1
  exact (eq_zero_of_gaussian_pair_and_signedSquaredZeroTails hf.continuous ha hg hFg
    (by positivity) (by linarith)
    (signedSquaredZeroTails_of_carrier Λ hρ hρhalf F J hgapΛ hzΛ)
    (signedSquaredZeroTails_of_carrier M hρ hρhalf G L hgapM hzM)).1

end MeyerGeneralProblem
