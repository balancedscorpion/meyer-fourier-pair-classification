module

public import MeyerGeneralProblem.Sampling.KNSUniformRateStep
public import MeyerGeneralProblem.Sampling.KNSClaimThreeGaussianImprovement
public import MeyerGeneralProblem.Sampling.KNSGaussianRateFiniteness
public import MeyerGeneralProblem.Sampling.KNSSharpWeightedFourierPair

@[expose] public section

/-!
# Actual Fourier-pair four-sign common-rate closure

The uniform numerical increment is fixed before the later common rate.
The physical and frequency sharp bounds are derived from the opposite
whole-line membership, using the actual Fourier representatives. Two
independent signed zero tails are used for each representative. This is
a one-step closure, not finite iteration, uniqueness or headline acceptance.
-/

noncomputable section
open Filter MeasureTheory
open scoped FourierTransform

namespace MeyerGeneralProblem


/-- Genuine ordered cofinal squared zero tails for both signs of real data.
The sign quantifier precedes the sequence and its two independent cutoffs;
neither reflection symmetry nor a common positive/negative tail is assumed. -/
def SignedSquaredZeroTails (g : ℝ → ℂ) (ell : ℝ) : Prop :=
  ∀ sgn : ℝ, sgn = 1 ∨ sgn = -1 →
    ∃ t : ℕ → ℝ, ∃ Ngap Nzero : ℕ,
      StrictMono (fun n => (t n)^2) ∧
      Tendsto (fun n => (t n)^2) atTop atTop ∧
      (∀ n ≥ Ngap, (t (n+1))^2-(t n)^2 ≤ ell) ∧
      ∀ n ≥ Nzero, 0 ≤ t n ∧ g (sgn*t n) = 0

/-- Both actual selected-ray bounds imply whole-line membership. The two
positive constants may differ; their maximum controls the whole real line. -/
theorem wholeRate_of_twoRayBounds {E : ℂ → ℂ} {κ : ℝ} (hκ : 0 < κ)
    (hplus : ∃ C > 0, ∀ u : ℝ, 0 ≤ u →
      ‖E (u : ℂ)‖ ≤ C*Real.exp (-2*Real.pi*κ*u^2))
    (hminus : ∃ C > 0, ∀ u : ℝ, 0 ≤ u →
      ‖E ((-u : ℝ) : ℂ)‖ ≤ C*Real.exp (-2*Real.pi*κ*u^2)) :
    HasWholeGaussianRate E κ := by
  obtain ⟨Cp, hCp, hp⟩ := hplus
  obtain ⟨Cm, hCm, hm⟩ := hminus
  refine ⟨hκ, max Cp Cm, hCp.trans_le (le_max_left Cp Cm), ?_⟩
  intro x
  by_cases hx : 0 ≤ x
  · exact (hp x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_left Cp Cm) (Real.exp_pos _).le)
  · have hn := hm (-x) (by linarith)
    simp only [neg_neg, neg_sq] at hn
    exact hn.trans
      (mul_le_mul_of_nonneg_right (le_max_right Cp Cm) (Real.exp_pos _).le)

/-- With fixed numerical parameters, the actual one-sided Claim 3 theorem
is applied separately to both signed zero tails. The sharp-bound input is
explicit here; the actual Fourier-pair theorem below derives it. -/
theorem wholeRate_step_of_sharp_and_signedZeros
    {E : ℂ → ℂ} {κ A ell b d α s : ℝ}
    (hE : Differentiable ℂ E) (hrate : HasWholeGaussianRate E κ)
    (hA : 0 ≤ A) (hell : 0 < ell) (hb : 0 ≤ b) (hbd : b < d)
    (hdell : d < ell⁻¹) (hα0 : 0 < α) (hαhalf : α < Real.pi/2)
    (hs0 : 0 < s) (hs1 : s < 1)
    (hsSector : s*(Real.sin α+Real.cos α) < Real.sin α)
    (hsharp : ∀ z : ℂ, ‖E z‖ ≤ A*Real.exp ((Real.pi/(2*κ))*z.im^2))
    (hdom : 2*κ*Real.cos α+(1-Real.cos α)/(4*κ) ≤ b*Real.sin α)
    (hzeros : SignedSquaredZeroTails (fun x => E (x : ℂ)) ell) :
    HasWholeGaussianRate E (κ+(d-b)*s/(2*Real.pi)) := by
  obtain ⟨hκ, C, hC, hreal⟩ := hrate
  have hgain : 0 < (d-b)*s/(2*Real.pi) := by positivity
  have hselected (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) :
      ∃ C₁ > 0, ∀ u : ℝ, 0 ≤ u →
        ‖E (((sgn*u : ℝ) : ℂ))‖ ≤
          C₁*Real.exp (-2*Real.pi*(κ+(d-b)*s/(2*Real.pi))*u^2) := by
    obtain ⟨t, Ngap, Nzero, htmono, httop, hgap, hzero⟩ := hzeros sgn hsgn
    have hrealSign : ∀ u : ℝ, 0 ≤ u →
        ‖E (((sgn*u : ℝ) : ℂ))‖ ≤ C*Real.exp (-2*Real.pi*κ*u^2) := by
      intro u _hu
      rcases hsgn with rfl | rfl
      · simpa only [one_mul] using hreal u
      · simpa only [neg_one_mul, neg_sq] using hreal (-u)
    exact (exists_globalGaussian_improvement_of_sharpBounds_squaredGapZeros
      hE hsgn hκ hκ hC.le hA hell (hb.trans_lt hbd) hdell hb hbd
      hα0 hαhalf hs0 hs1 hsSector hrealSign hsharp hdom
      htmono httop Ngap Nzero hgap hzero).2
  apply wholeRate_of_twoRayBounds (add_pos hκ hgain)
  · simpa only [one_mul] using hselected 1 (Or.inl rfl)
  · simpa only [neg_one_mul] using hselected (-1) (Or.inr rfl)

/-- For an actual continuous Fourier pair with Gaussian square integrals
and four genuine signed zero tails, one positive increment works at every
later common positive whole-line rate. The opposite-side sharp bounds,
entire regularity, both L1 facts and physical inversion are all derived.
Only the angle and bound constants may vary with the later rate. -/
theorem exists_commonRate_step_actualFourierPair
    {f : ℝ → ℂ} {a ell κ₀ : ℝ} (hf : Continuous f) (ha : 0 < a)
    (hgauss : Integrable (fun x => Real.exp (a*x^2)*‖f x‖^2))
    (hFgauss : Integrable (fun x => Real.exp (a*x^2)*‖𝓕 f x‖^2))
    (hell0 : 0 < ell) (hell1 : ell < 1) (hκ₀ : 0 < κ₀)
    (hzerosPhysical : SignedSquaredZeroTails f ell)
    (hzerosFourier : SignedSquaredZeroTails (𝓕 f) ell) :
    ∃ γ > 0, ∀ κ : ℝ, κ₀ ≤ κ →
      HasWholeGaussianRate (knsPhysicalEntire f) κ →
      HasWholeGaussianRate (knsFourierEntire f) κ →
      HasWholeGaussianRate (knsPhysicalEntire f) (κ+γ) ∧
        HasWholeGaussianRate (knsFourierEntire f) (κ+γ) := by
  have hf1 := integrable_of_gaussian_square ha hf.aestronglyMeasurable hgauss
  have hF : Continuous (𝓕 f : ℝ → ℂ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf1
  have hF1 := integrable_of_gaussian_square ha hF.aestronglyMeasurable hFgauss
  have hEP := differentiable_knsPhysicalEntire ha hF.aestronglyMeasurable hFgauss
  have hEF := differentiable_knsFourierEntire ha hf.aestronglyMeasurable hgauss
  have hzP : SignedSquaredZeroTails (fun x => knsPhysicalEntire f (x : ℂ)) ell := by
    simpa only [knsPhysicalEntire_ofReal hf hf1 hF1] using hzerosPhysical
  have hzF : SignedSquaredZeroTails (fun x => knsFourierEntire f (x : ℂ)) ell := by
    simpa only [knsFourierEntire_ofReal] using hzerosFourier
  obtain ⟨b, d, s, γ, hb, hbd, hdell, hs0, hs1, hγ, hγeq, hparams⟩ :=
    exists_uniform_KNS_rateStep_parameters hell0 hell1 hκ₀
  refine ⟨γ, hγ, ?_⟩
  intro κ hκlower hP hFRate
  obtain ⟨α, hα0, hαhalf, hsSector, hdom⟩ := hparams κ hκlower
  obtain ⟨hκ, CP, hCP, hPbound⟩ := hP
  obtain ⟨_hκF, CF, hCF, hFbound⟩ := hFRate
  have hphysical : ∀ x : ℝ, ‖f x‖ ≤ CP*Real.exp (-2*Real.pi*κ*x^2) := by
    intro x
    simpa only [knsPhysicalEntire_ofReal hf hf1 hF1] using hPbound x
  have hfourier : ∀ x : ℝ, ‖𝓕 f x‖ ≤ CF*Real.exp (-2*Real.pi*κ*x^2) := by
    intro x
    simpa only [knsFourierEntire_ofReal] using hFbound x
  have hsharpP := norm_knsPhysicalEntire_le_of_pointwiseGaussian
    hκ hCF.le hF.aestronglyMeasurable hfourier
  have hsharpF := norm_knsFourierEntire_le_of_pointwiseGaussian
    hκ hCP.le hf.aestronglyMeasurable hphysical
  rw [hγeq]
  constructor
  · exact wholeRate_step_of_sharp_and_signedZeros hEP ⟨hκ, CP, hCP, hPbound⟩
      (mul_nonneg hCF.le (Real.sqrt_nonneg _)) hell0 hb hbd hdell
      hα0 hαhalf hs0 hs1 hsSector hsharpP hdom hzP
  · exact wholeRate_step_of_sharp_and_signedZeros hEF ⟨hκ, CF, hCF, hFbound⟩
      (mul_nonneg hCP.le (Real.sqrt_nonneg _)) hell0 hb hbd hdell
      hα0 hαhalf hs0 hs1 hsSector hsharpF hdom hzF



end MeyerGeneralProblem
