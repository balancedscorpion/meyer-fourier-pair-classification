module

public import MeyerGeneralProblem.Sampling.KNSSharpWeightedFourierPair
public import MeyerGeneralProblem.Sampling.KNSSectorPhragmenLindelof

@[expose] public section

/-!
# Uniform sector input bounds for the actual weighted root

The common boundary constant and angular coefficient are fixed before epsilon.
The independent opposite-side rate and actual entire/Gaussian premises are
retained. The numerical angular dominance remains an explicit input.
-/

namespace MeyerGeneralProblem

noncomputable section

open scoped FourierTransform

private theorem kns_sharp_ray_le_sector_boundary
    {sgn κ ε η A M α a : ℝ} {E : ℂ → ℂ}
    (hsgn : sgn = 1 ∨ sgn = -1) (hη : 0 < η)
    (hA : 0 ≤ A) (hAM : A ≤ M) (hε : 0 ≤ ε)
    (hsharp : ∀ z : ℂ, ‖E z‖ ≤ A * Real.exp ((Real.pi/(2*η))*z.im^2))
    (hα0 : 0 < α) (hαhalf : α < Real.pi/2)
    (hdom : 2*κ*Real.cos α+(1-Real.cos α)/(4*η) ≤ a*Real.sin α)
    {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) (hcosEq : Real.cos θ = Real.cos α) :
    ‖knsWeightedPrincipalRoot sgn κ ε E
      ((r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I))‖ ≤
      M*Real.exp (a*Real.pi*r*Real.sin α) := by
  have hcos : 0 ≤ Real.cos θ := by
    rw [hcosEq]
    exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαhalf⟩).le
  have h := norm_knsWeightedPrincipalRoot_ray_le_sharp_uniform
    (κ := κ) (ε := ε) hsgn hη hA hε hsharp hr hcos
  rw [hcosEq] at h
  have he : Real.pi*r*(2*κ*Real.cos α+(1-Real.cos α)/(4*η)) ≤
      a*Real.pi*r*Real.sin α := by
    calc
      _ ≤ Real.pi*r*(a*Real.sin α) :=
        mul_le_mul_of_nonneg_left hdom (mul_nonneg Real.pi_pos.le hr)
      _ = _ := by ring
  exact h.trans ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hA).trans
    (mul_le_mul_of_nonneg_right hAM (Real.exp_pos _).le))

private theorem kns_weighted_real_le_common
    {sgn κ ε Creal M : ℝ} {E : ℂ → ℂ}
    (hε : 0 ≤ ε) (hCreal : 0 ≤ Creal) (hCM : Creal ≤ M)
    (hreal : ∀ t : ℝ, 0 ≤ t →
      ‖E (((sgn*t : ℝ) : ℂ))‖ ≤ Creal*Real.exp (-2*Real.pi*κ*t^2))
    {r : ℝ} (hr : 0 ≤ r) :
    ‖knsWeightedPrincipalRoot sgn κ ε E (r : ℂ)‖ ≤ M := by
  have h := norm_knsWeightedPrincipalRoot_real_le sgn κ ε hreal hr
  have he : Real.exp (-ε*r) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε) hr)
  exact h.trans ((mul_le_mul_of_nonneg_left he hCreal).trans (by simpa using hCM))

/-- Actual sharp weighted-root data propagate throughout the strict sector
under the displayed numerical boundary dominance. The common constant and
sector coefficient are fixed before every positive epsilon; only the auxiliary
linear-growth coefficient may depend on epsilon. -/
theorem norm_knsWeightedPrincipalRoot_on_sector_le
    {sgn κ η Creal A α a : ℝ} {E : ℂ → ℂ}
    (hE : Differentiable ℂ E) (hsgn : sgn = 1 ∨ sgn = -1)
    (hη : 0 < η) (hCreal : 0 ≤ Creal) (hA : 0 ≤ A)
    (hα0 : 0 < α) (hαhalf : α < Real.pi/2) (ha : 0 ≤ a)
    (hreal : ∀ t : ℝ, 0 ≤ t →
      ‖E (((sgn*t : ℝ) : ℂ))‖ ≤ Creal*Real.exp (-2*Real.pi*κ*t^2))
    (hsharp : ∀ z : ℂ, ‖E z‖ ≤ A*Real.exp ((Real.pi/(2*η))*z.im^2))
    (hdom : 2*κ*Real.cos α+(1-Real.cos α)/(4*η) ≤ a*Real.sin α) :
    ∀ ε : ℝ, 0 < ε → ∀ w ∈ knsOpenSector α,
      ‖knsWeightedPrincipalRoot sgn κ ε E w‖ ≤
        max 1 (max Creal A)*Real.exp (a*Real.pi*|w.im|) := by
  intro ε hε
  have hCM : Creal ≤ max 1 (max Creal A) :=
    (le_max_left Creal A).trans (le_max_right 1 _)
  have hAM : A ≤ max 1 (max Creal A) :=
    (le_max_right Creal A).trans (le_max_right 1 _)
  apply norm_le_on_knsOpenSector_of_boundaryRays
    (A := A) (B := Real.pi/(4*η)+|2*Real.pi*κ-ε-Real.pi/(4*η)|)
    hα0 hαhalf ha (le_max_left 1 _) hA (by positivity)
    (diffContOnCl_knsWeightedPrincipalRoot sgn κ ε hE)
  · exact norm_knsWeightedPrincipalRoot_le_sharp_linear hsgn hη hA hsharp
  · intro r hr
    exact kns_weighted_real_le_common hε.le hCreal hCM hreal hr
  · intro r hr
    exact kns_sharp_ray_le_sector_boundary hsgn hη hA hAM hε.le hsharp
      hα0 hαhalf hdom hr α rfl
  · intro r hr
    simpa only [Complex.ofReal_neg] using
      kns_sharp_ray_le_sector_boundary hsgn hη hA hAM hε.le hsharp
        hα0 hαhalf hdom hr (-α) (Real.cos_neg α)

/-- The actual Fourier-side representative supplies uniform-in-epsilon sector
growth from Gaussian square integrability, its actual selected-ray bound and
the independent whole-line opposite rate. Numerical dominance remains explicit. -/
theorem norm_knsWeightedFourierRoot_on_sector_le
    {f : ℝ → ℂ} (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    {c sgn κ η Creal Cη α a : ℝ} (hc : 0 < c)
    (hgauss : MeasureTheory.Integrable (fun t => Real.exp (c*t^2)*‖f t‖^2))
    (hsgn : sgn = 1 ∨ sgn = -1) (hη : 0 < η)
    (hCreal : 0 ≤ Creal) (hCη : 0 ≤ Cη)
    (hα0 : 0 < α) (hαhalf : α < Real.pi/2) (ha : 0 ≤ a)
    (hreal : ∀ t : ℝ, 0 ≤ t →
      ‖𝓕 f (sgn*t)‖ ≤ Creal*Real.exp (-2*Real.pi*κ*t^2))
    (hpoint : ∀ t : ℝ, ‖f t‖ ≤ Cη*Real.exp (-2*Real.pi*η*t^2))
    (hdom : 2*κ*Real.cos α+(1-Real.cos α)/(4*η) ≤ a*Real.sin α) :
    ∀ ε : ℝ, 0 < ε → ∀ w ∈ knsOpenSector α,
      ‖knsWeightedPrincipalRoot sgn κ ε (knsFourierEntire f) w‖ ≤
        max 1 (max Creal (Cη*Real.sqrt (1/(2*η))))*
          Real.exp (a*Real.pi*|w.im|) := by
  have hrealE : ∀ t : ℝ, 0 ≤ t →
      ‖knsFourierEntire f (((sgn*t : ℝ) : ℂ))‖ ≤
        Creal*Real.exp (-2*Real.pi*κ*t^2) := by
    intro t ht
    simpa only [knsFourierEntire_ofReal] using hreal t ht
  exact norm_knsWeightedPrincipalRoot_on_sector_le
    (differentiable_knsFourierEntire hc hf hgauss) hsgn hη hCreal
    (mul_nonneg hCη (Real.sqrt_nonneg _)) hα0 hαhalf ha hrealE
    (norm_knsFourierEntire_le_of_pointwiseGaussian hη hCη hf hpoint) hdom

/-- The actual physical representative retains its reflected Fourier integral,
continuity and both L1 inversion premises. The entire input is derived from
the Fourier Gaussian square integral, and the output constant is fixed before
epsilon, independently of the auxiliary linear-growth bound. -/
theorem norm_knsWeightedPhysicalRoot_on_sector_le
    {f : ℝ → ℂ} (hf : Continuous f)
    (hf1 : MeasureTheory.Integrable f) (hF1 : MeasureTheory.Integrable (𝓕 f))
    {c sgn κ η Creal Cη α a : ℝ} (hc : 0 < c)
    (hgauss : MeasureTheory.Integrable (fun t => Real.exp (c*t^2)*‖𝓕 f t‖^2))
    (hsgn : sgn = 1 ∨ sgn = -1) (hη : 0 < η)
    (hCreal : 0 ≤ Creal) (hCη : 0 ≤ Cη)
    (hα0 : 0 < α) (hαhalf : α < Real.pi/2) (ha : 0 ≤ a)
    (hreal : ∀ t : ℝ, 0 ≤ t →
      ‖f (sgn*t)‖ ≤ Creal*Real.exp (-2*Real.pi*κ*t^2))
    (hpoint : ∀ t : ℝ, ‖𝓕 f t‖ ≤ Cη*Real.exp (-2*Real.pi*η*t^2))
    (hdom : 2*κ*Real.cos α+(1-Real.cos α)/(4*η) ≤ a*Real.sin α) :
    ∀ ε : ℝ, 0 < ε → ∀ w ∈ knsOpenSector α,
      ‖knsWeightedPrincipalRoot sgn κ ε (knsPhysicalEntire f) w‖ ≤
        max 1 (max Creal (Cη*Real.sqrt (1/(2*η))))*
          Real.exp (a*Real.pi*|w.im|) := by
  have hrealE : ∀ t : ℝ, 0 ≤ t →
      ‖knsPhysicalEntire f (((sgn*t : ℝ) : ℂ))‖ ≤
        Creal*Real.exp (-2*Real.pi*κ*t^2) := by
    intro t ht
    simpa only [knsPhysicalEntire_ofReal hf hf1 hF1] using hreal t ht
  exact norm_knsWeightedPrincipalRoot_on_sector_le
    (differentiable_knsPhysicalEntire hc hF1.aestronglyMeasurable hgauss)
    hsgn hη hCreal (mul_nonneg hCη (Real.sqrt_nonneg _)) hα0 hαhalf ha hrealE
    (norm_knsPhysicalEntire_le_of_pointwiseGaussian hη hCη
      hF1.aestronglyMeasurable hpoint) hdom

end

end MeyerGeneralProblem
