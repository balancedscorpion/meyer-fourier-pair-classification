module

public import MeyerGeneralProblem.Distribution.LowerRayCombClassification
public import MeyerGeneralProblem.Cardinal.Adaptive.SmoothSelectors
public import Mathlib.Analysis.Fourier.Convolution

@[expose] public section

/-!
# Integrable localization of real functions with a Fourier gap

A nonnegative Schwartz multiplier with arbitrarily small Fourier support
preserves signs wherever the product is nonzero. This allows the
polynomial-growth oscillation statement to use the integrable case.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Filter MeasureTheory Set UniformDiscrete
open scoped ComplexConjugate FourierTransform Pointwise RealInnerProductSpace

private theorem tsupport_schwartz_mul_convolution
    (a b : SchwartzMap ℝ ℂ) (r s : ℝ)
    (ha : tsupport (a : ℝ → ℂ) ⊆ Icc (-r) r)
    (hb : tsupport (b : ℝ → ℂ) ⊆ Icc (-s) s) :
    tsupport (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) a b : ℝ → ℂ) ⊆
      Icc (-(r + s)) (r + s) := by
  apply closure_minimal _ isClosed_Icc
  have he := funext (SchwartzMap.convolution_apply (ContinuousLinearMap.mul ℂ ℂ) a b)
  rw [he]
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ :=
    MeasureTheory.support_convolution_subset (ContinuousLinearMap.mul ℂ ℂ) hx
  have hy' := ha (subset_tsupport a hy)
  have hz' := hb (subset_tsupport b hz)
  exact ⟨by linarith [hy'.1, hz'.1], by linarith [hy'.2, hz'.2]⟩

private theorem vanishesOnInterval_fourier_schwartz_multiply
    (G : SchwartzMap ℝ ℂ) (V : TemperedDistribution ℝ ℂ) (δ r R : ℝ)
    (hG : tsupport (G : ℝ → ℂ) ⊆ Icc (-δ) δ) (hr : r + δ < R)
    (hV : VanishesOnInterval (𝓕 V) R) :
    VanishesOnInterval
      (𝓕 (TemperedDistribution.smulLeftCLM ℂ (⇑(𝓕 G : SchwartzMap ℝ ℂ)) V)) r := by
  intro φ _ hφ
  let ψ := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) G φ
  have hSupp : tsupport (ψ : ℝ → ℂ) ⊆ Icc (-(δ + r)) (δ + r) :=
    tsupport_schwartz_mul_convolution G φ δ r hG (hφ.trans Ioo_subset_Icc_self)
  have hc : HasCompactSupport (ψ : ℝ → ℂ) := isCompact_Icc.of_isClosed_subset isClosed_closure hSupp
  have hInt : tsupport (ψ : ℝ → ℂ) ⊆ Ioo (-R) R := by
    intro x hx
    have hy := hSupp hx
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hF : (𝓕 ψ : SchwartzMap ℝ ℂ) =
      SchwartzMap.smulLeftCLM ℂ (⇑(𝓕 G : SchwartzMap ℝ ℂ)) (𝓕 φ) := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply (𝓕 G : SchwartzMap ℝ ℂ).hasTemperateGrowth,
      SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply]
    rfl
  change V (SchwartzMap.smulLeftCLM ℂ (⇑(𝓕 G : SchwartzMap ℝ ℂ)) (𝓕 φ)) = 0
  rw [← hF]
  exact hV ψ hc hInt

private theorem exists_nonnegative_schwartz_multiplier
    (δ x₀ : ℝ) (hδ : 0 < δ) :
    ∃ G : SchwartzMap ℝ ℂ, tsupport (G : ℝ → ℂ) ⊆ Icc (-δ) δ ∧
      ((𝓕 G : SchwartzMap ℝ ℂ) x₀).re = 1 ∧
      ∀ x : ℝ, ∃ t : ℝ, 0 ≤ t ∧ (𝓕 G : SchwartzMap ℝ ℂ) x = (t : ℂ) := by
  let ρ := δ / 2
  let bump := selectorKernelBump ρ (by dsimp [ρ]; positivity)
  let χ : SchwartzMap ℝ ℂ :=
    (bump.hasCompactSupport_normed (μ := volume)).comp_left (g := Complex.ofRealCLM) rfl |>.toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp bump.contDiff_normed)
  let a := combSchwartzModulation x₀ χ
  let b := complexConjugateSchwartz (schwartzReflectionCLM a)
  let G := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) a b
  have ha : tsupport (a : ℝ → ℂ) ⊆ Icc (-ρ) ρ := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    have hb : bump.normed volume x ≠ 0 := by
      intro h
      exact hx (by simp [a, combSchwartzModulation_apply, χ, h])
    have htx := subset_tsupport (bump.normed volume) hb
    rw [bump.tsupport_normed_eq] at htx
    have hAbs : |x| ≤ ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, bump, selectorKernelBump] using htx
    exact abs_le.mp hAbs
  have hb : tsupport (b : ℝ → ℂ) ⊆ Icc (-ρ) ρ := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    have hx' : a (-x) ≠ 0 := by
      intro h
      exact hx (by simp [b, schwartzReflectionCLM_apply, h])
    have ha' := ha (subset_tsupport a hx')
    exact ⟨by linarith [ha'.2], by linarith [ha'.1]⟩
  have hbF : (𝓕 b : SchwartzMap ℝ ℂ) = complexConjugateSchwartz (𝓕 a) := by
    change (𝓕 (complexConjugateSchwartz (schwartzReflectionCLM a)) : SchwartzMap ℝ ℂ) = _
    rw [fourier_complexConjugateSchwartz, ← schwartz_fourier_sq_eq_reflection,
      FourierTransform.fourierInv_fourier_eq]
  have hG (x : ℝ) : (𝓕 G : SchwartzMap ℝ ℂ) x = ((‖(𝓕 a : SchwartzMap ℝ ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    change (𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) a b) :
      SchwartzMap ℝ ℂ) x = _
    rw [SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply, hbF]
    change (𝓕 a : SchwartzMap ℝ ℂ) x * conj ((𝓕 a : SchwartzMap ℝ ℂ) x) = _
    rw [Complex.mul_conj, Complex.sq_norm]
  have hχ : (𝓕 χ : SchwartzMap ℝ ℂ) 0 = 1 := by
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
    change (∫ x : ℝ, (bump.normed volume x : ℂ)) = 1
    rw [integral_complex_ofReal, bump.integral_normed, Complex.ofReal_one]
  have ha₀ : (𝓕 a : SchwartzMap ℝ ℂ) x₀ = 1 := by
    rw [show a = combSchwartzModulation (-(-x₀)) χ by simp [a],
      fourier_combSchwartzModulation_neg, combSchwartzTranslation_apply]
    simpa using hχ
  refine ⟨G, ?_, ?_, fun x => ⟨‖(𝓕 a : SchwartzMap ℝ ℂ) x‖ ^ 2, by positivity, hG x⟩⟩
  · have hSum : ρ + ρ = δ := by dsimp [ρ]; ring
    simpa only [hSum] using tsupport_schwartz_mul_convolution a b ρ ρ ha hb
  · simp [hG, ha₀]

/-- For an integrable density, the distributional centered gap
is a pointwise zero interval of the ordinary Fourier transform. -/
theorem eqOn_fourier_zero_of_integrable_density_distribution_gap
    (V : TemperedDistribution ℝ ℂ) (f : ℝ → ℝ) (hf : Integrable f) (R : ℝ)
    (hRep : ∀ φ : SchwartzMap ℝ ℂ, V φ = ∫ x : ℝ, φ x * (f x : ℂ))
    (hGap : VanishesOnInterval (𝓕 V) R) :
    EqOn (𝓕 (fun x : ℝ => (f x : ℂ))) 0 (Ioo (-R) R) := by
  let F : ℝ → ℂ := fun x => (f x : ℂ)
  have hF : Integrable F := hf.ofReal
  let L : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ := innerₗ ℝ
  have hL : Continuous fun p : ℝ × ℝ => L p.1 p.2 :=
    (innerSL ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).continuous₂
  have hCont : Continuous (𝓕 F) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar hL hF
  have hFlip : L.flip = L := by
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    change inner ℝ y x = inner ℝ x y
    exact real_inner_comm x y
  refine continuous_eqOn_Ioo_of_schwartz_integral_eq (𝓕 F) (fun _ => 0)
    hCont continuous_const (-R) R ?_
  intro φ hCompact hSupp
  have hSwap := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) (L := L)
    Real.continuous_fourierChar hL φ.integrable hF
  rw [hFlip] at hSwap
  have hAct := hGap φ hCompact hSupp
  rw [TemperedDistribution.fourier_apply, hRep] at hAct
  change (∫ x : ℝ, (𝓕 φ : SchwartzMap ℝ ℂ) x * (f x : ℂ)) = 0 at hAct
  rw [SchwartzMap.fourier_coe] at hAct
  change (∫ x : ℝ, 𝓕 (φ : ℝ → ℂ) x * F x) = ∫ x : ℝ, φ x * 𝓕 F x at hSwap
  change (∫ x : ℝ, φ x * 𝓕 F x) = ∫ x : ℝ, φ x * (0 : ℂ)
  simp only [mul_zero, integral_zero]
  exact hSwap.symm.trans hAct

/-- The Eremenko–Novikov origin-ray bound for the continuous integrable
real densities and the ordinary Fourier transform. -/
def IntegrableFourierGapSignAlternations : Prop :=
  ∀ (f : ℝ → ℝ) (R : ℝ), 0 < R → Continuous f → Integrable f → f ≠ 0 →
    EqOn (𝓕 (fun x : ℝ => (f x : ℂ))) 0 (Ioo (-R) R) →
    ∀ (positive : Bool) (c : ℝ), c < 2 * R →
      ∀ᶠ r : ℝ in atTop, ∃ n : ℕ,
        c * r ≤ (n : ℝ) ∧ HasSignAlternations f (originalRayWindow positive r) n

/-- A real polynomial-growth density reduces to the integrable
oscillation statement by a nonnegative multiplier with small frequency
support. Every sign alternation of the product is one of the original
density at the same sample points. -/
theorem polynomialGrowthFourierGapSignAlternations_of_integrable
    (hOsc : IntegrableFourierGapSignAlternations) : PolynomialGrowthFourierGapSignAlternations := by
  intro V f q R hR hf hfNonzero hGrowth hRep hGap positive c hc
  obtain ⟨C, _, hBound⟩ := hGrowth
  obtain ⟨a, ha, haR⟩ := exists_between (max_lt (show c / 2 < R by linarith) hR)
  have haPositive : 0 < a := (le_max_right (c / 2) 0).trans_lt ha
  have hc' : c < 2 * a := by linarith [lt_of_le_of_lt (le_max_left (c / 2) 0) ha]
  let δ := (R - a) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδR : a + δ < R := by dsimp [δ]; linarith
  have hExists : ∃ x₀ : ℝ, f x₀ ≠ 0 := by
    by_contra hNone
    apply hfNonzero
    funext x
    by_contra hx
    exact hNone ⟨x, hx⟩
  obtain ⟨x₀, hx₀⟩ := hExists
  obtain ⟨G, hG, hAt, hReal⟩ := exists_nonnegative_schwartz_multiplier δ x₀ hδ
  let W : SchwartzMap ℝ ℂ := 𝓕 G
  let w (x : ℝ) : ℝ := (W x).re
  let g (x : ℝ) : ℝ := w x * f x
  have hw (x : ℝ) : 0 ≤ w x ∧ W x = (w x : ℂ) := by
    obtain ⟨t, ht, hEq⟩ := hReal x
    have hw' : w x = t := by
      change (W x).re = t
      rw [show W x = (t : ℂ) from hEq, Complex.ofReal_re]
    exact ⟨hw' ▸ ht, hw' ▸ hEq⟩
  have hg : Continuous g := (Complex.continuous_re.comp W.continuous).mul hf
  have hgNonzero : g ≠ 0 := by
    intro h
    have he : g x₀ = 0 := congrFun h x₀
    exact hx₀ (by simpa only [g, w, W, hAt, one_mul] using he)
  have hgInt : Integrable g := by
    apply ((integrable_one_add_abs_pow_mul_norm_schwartz W q).const_mul C).mono'
      hg.aestronglyMeasurable
    filter_upwards with x
    change ‖w x * f x‖ ≤ C * ((1 + |x|) ^ q * ‖W x‖)
    have hAbs : |w x| = ‖W x‖ := by rw [(hw x).2, Complex.norm_real, Real.norm_eq_abs]
    rw [Real.norm_eq_abs, abs_mul, hAbs]
    calc
      _ ≤ ‖W x‖ * (C * (1 + |x|) ^ q) :=
        mul_le_mul_of_nonneg_left (hBound x) (norm_nonneg _)
      _ = _ := by ring
  let V' := TemperedDistribution.smulLeftCLM ℂ (⇑W) V
  have hV' : VanishesOnInterval (𝓕 V') a :=
    vanishesOnInterval_fourier_schwartz_multiply G V δ a R hG hδR hGap
  have hRep' (φ : SchwartzMap ℝ ℂ) : V' φ = ∫ x : ℝ, φ x * (g x : ℂ) := by
    change V (SchwartzMap.smulLeftCLM ℂ (⇑W) φ) = _
    rw [hRep]
    apply integral_congr_ae
    filter_upwards with x
    rw [SchwartzMap.smulLeftCLM_apply_apply W.hasTemperateGrowth, smul_eq_mul,
      (hw x).2, show (g x : ℂ) = (w x : ℂ) * (f x : ℂ) from Complex.ofReal_mul _ _]
    ring
  filter_upwards [hOsc g a haPositive hg hgInt hgNonzero
    (eqOn_fourier_zero_of_integrable_density_distribution_gap V' g hgInt a hRep' hV')
    positive c hc'] with r hr
  obtain ⟨n, hn, x, hMono, hMem, hAlt⟩ := hr
  refine ⟨n, hn, x, hMono, hMem, fun i => ?_⟩
  by_contra! hNonneg
  have hSigns := hAlt i
  change (w (x i.castSucc) * f (x i.castSucc)) * (w (x i.succ) * f (x i.succ)) < 0 at hSigns
  rw [mul_mul_mul_comm] at hSigns
  exact (not_lt_of_ge (mul_nonneg (mul_nonneg (hw _).1 (hw _).1) hNonneg)) hSigns

/-- The integrable real-function oscillation bound suffices for the
original value-only atomic lower ray theorem. -/
theorem atomicFourierGapRayLowerBound_of_integrable_signAlternations
    (hOsc : IntegrableFourierGapSignAlternations) : AtomicFourierGapRayLowerBound :=
  atomicFourierGapRayLowerBound_of_polynomialGrowth_signAlternations
    (polynomialGrowthFourierGapSignAlternations_of_integrable hOsc)

end
end MeyerGeneralProblem
