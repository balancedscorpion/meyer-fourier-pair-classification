module

public import MeyerGeneralProblem.Sampling.KNSLocalizedPoincare

@[expose] public section

/-!
# Translation-variable Fourier energy of actual KNS localization

At each fixed frequency, the actual Fourier integral of f times the
translated localizer is a convolution in the translation variable. Its
L1 and L2 properties are consequences of the integrable input and actual
bounded compact kernel. Plancherel then applies to that genuine function.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Convolution
open scoped FourierTransform ContDiff ENNReal

/-- The actual Fourier integral of the localized function, as a function
of the translation variable at fixed frequency. -/
def knsLocalizedFourierSlice (n : ℕ) (u : ℝ) (f : ℝ → ℂ) (ξ v : ℝ) : ℂ :=
  𝓕 (knsLocalizedFunction n u v f) ξ

/-- The actual localized Fourier slice is a convolution with the reflected
localizer, not an assigned frequency-domain surrogate. -/
theorem knsLocalizedFourierSlice_eq_convolution (n : ℕ) (u : ℝ) (f : ℝ → ℂ) (ξ : ℝ) :
    knsLocalizedFourierSlice n u f ξ =
      (fun x => f x * gramPhase (-ξ) x) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (fun x => (knsMomentLocalizer n u (-x) : ℂ)) := by
  funext v
  simp only [knsLocalizedFourierSlice, fourier_eq_integral_gramPhase,
    convolution_def, ContinuousLinearMap.mul_apply', knsLocalizedFunction]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [neg_sub]
  ring

private theorem integrable_knsModulation {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    Integrable (fun x => f x * gramPhase (-ξ) x) := by
  apply hf.norm.mono
    (hf.aestronglyMeasurable.mul (show Continuous (fun x => gramPhase (-ξ) x) by
      unfold gramPhase
      fun_prop).aestronglyMeasurable)
  filter_upwards [] with x
  change ‖f x * gramPhase (-ξ) x‖ ≤ ‖‖f x‖‖
  simp only [norm_mul, norm_gramPhase, mul_one, norm_norm]
  exact le_rfl

/-- The translation slice is integrable whenever the actual unknown is
L1; no global Schwartz or Gaussian condition is imposed. -/
theorem integrable_knsLocalizedFourierSlice (n : ℕ) (u : ℝ)
    {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    Integrable (knsLocalizedFourierSlice n u f ξ) := by
  rw [knsLocalizedFourierSlice_eq_convolution]
  exact (integrable_knsModulation hf ξ).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (integrable_knsMomentLocalizer n u).comp_neg.ofReal

/-- Every actual translation slice is bounded by the L1 mass of the
unknown, using the proved pointwise bound zero ≤ F ≤ one. -/
theorem norm_knsLocalizedFourierSlice_le {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u)
    {f : ℝ → ℂ} (hf : Integrable f) (ξ v : ℝ) :
    ‖knsLocalizedFourierSlice n u f ξ v‖ ≤ ∫ x, ‖f x‖ := by
  rw [knsLocalizedFourierSlice, fourier_eq_integral_gramPhase]
  apply norm_integral_le_of_norm_le hf.norm
  filter_upwards [] with x
  simp only [knsLocalizedFunction, norm_mul, norm_gramPhase, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (knsMomentLocalizer_nonneg n hu (x-v))]
  exact mul_le_of_le_one_right (norm_nonneg _) (knsMomentLocalizer_le_one hn hu (x-v))

/-- L1 plus the actual uniform bound gives L2 for every translation
slice, so Plancherel does not rely on a hidden slice-domain hypothesis. -/
theorem memLp_knsLocalizedFourierSlice {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u)
    {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    MemLp (knsLocalizedFourierSlice n u f ξ) 2 := by
  have hL1 := integrable_knsLocalizedFourierSlice n u hf ξ
  apply (memLp_two_iff_integrable_sq_norm hL1.aestronglyMeasurable).mpr
  apply (hL1.norm.const_mul (∫ x, ‖f x‖)).mono
    (hL1.aestronglyMeasurable.norm.pow 2)
  filter_upwards [] with v
  change |‖knsLocalizedFourierSlice n u f ξ v‖^2| ≤
    |(∫ x, ‖f x‖)*‖knsLocalizedFourierSlice n u f ξ v‖|
  rw [abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (mul_nonneg (integral_nonneg (fun x => norm_nonneg (f x))) (norm_nonneg _))]
  nlinarith [norm_knsLocalizedFourierSlice_le hn hu hf ξ v, norm_nonneg (knsLocalizedFourierSlice n u f ξ v)]

/-- Fourier transformation in the translation variable gives the genuine
product of shifted Fourier data and the reflected localizer transform. -/
theorem fourier_knsLocalizedFourierSlice (n : ℕ) (u : ℝ)
    {f : ℝ → ℂ} (hf : Integrable f) (ξ η : ℝ) :
    𝓕 (knsLocalizedFourierSlice n u f ξ) η =
      𝓕 f (η+ξ) * knsRealFourier (knsMomentLocalizer n u) (-η) := by
  rw [knsLocalizedFourierSlice_eq_convolution]
  calc
    _ = 𝓕 (fun x => f x * gramPhase (-ξ) x) η *
        𝓕 (fun x => (knsMomentLocalizer n u (-x) : ℂ)) η := by
      convert! Real.fourier_mul_convolution_eq (integrable_knsModulation hf ξ)
        (integrable_knsMomentLocalizer n u).comp_neg.ofReal η using 1
    _ = _ := by
      rw [fourier_mul_gramPhase, sub_neg_eq_add]
      congr 1
      exact Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ)
        (fun x => (knsMomentLocalizer n u x : ℂ)) η

/-- The exact translation-variable Plancherel identity at every fixed
frequency, for an actual L1 unknown and the actual KNS localizer. -/
theorem integral_knsLocalizedFourierSlice_sq {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u)
    {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    (∫ v, ‖knsLocalizedFourierSlice n u f ξ v‖^2) =
      ∫ η, ‖𝓕 f (ξ-η)‖^2 * ‖knsRealFourier (knsMomentLocalizer n u) η‖^2 := by
  have hL1 := integrable_knsLocalizedFourierSlice n u hf ξ
  have hL2 := memLp_knsLocalizedFourierSlice hn hu hf ξ
  obtain ⟨hFT, hnorm⟩ := memLp_fourier_norm_eq_of_integrable hL1 hL2
  have he : (∫ v, ‖knsLocalizedFourierSlice n u f ξ v‖^2) =
      ∫ η, ‖𝓕 (knsLocalizedFourierSlice n u f ξ) η‖^2 := by
    rw [integral_norm_sq_eq_toLp_norm_sq_complex hL2,
      integral_norm_sq_eq_toLp_norm_sq_complex hFT, hnorm]
  rw [he, ← integral_neg_eq_self (fun η => ‖𝓕 (knsLocalizedFourierSlice n u f ξ) η‖^2) volume]
  apply integral_congr_ae
  filter_upwards [] with η
  rw [fourier_knsLocalizedFourierSlice n u hf, neg_neg, norm_mul, mul_pow]
  rw [show -η+ξ=ξ-η by ring]

/-- Joint continuity in frequency and translation follows by dominated
convergence with the actual L1 unknown as majorant. -/
theorem continuous_knsLocalizedFourierSlice {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u)
    {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (fun p : ℝ × ℝ => knsLocalizedFourierSlice n u f p.1 p.2) := by
  have hF := continuous_knsMomentLocalizer n hu.le
  simp only [knsLocalizedFourierSlice, fourier_eq_integral_gramPhase, knsLocalizedFunction]
  apply continuous_of_dominated (bound := fun x => ‖f x‖)
  · intro p
    exact (show Continuous (fun x => gramPhase (-p.1) x) by unfold gramPhase; fun_prop).aestronglyMeasurable.mul
      (hf.aestronglyMeasurable.mul (show Continuous (fun x => (knsMomentLocalizer n u (x-p.2) : ℂ)) by
        fun_prop).aestronglyMeasurable)
  · intro p
    filter_upwards [] with x
    simp only [norm_mul, norm_gramPhase, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (knsMomentLocalizer_nonneg n hu (x-p.2))]
    exact mul_le_of_le_one_right (norm_nonneg _) (knsMomentLocalizer_le_one hn hu (x-p.2))
  · exact hf.norm
  · filter_upwards [] with x
    unfold gramPhase
    fun_prop

/-- The fixed-frequency product of the two actual Fourier energies is
integrable as a conclusion of the proved translation-slice Plancherel domain. -/
theorem integrable_knsFourierEnergy_convolution {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u)
    {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    Integrable (fun η => ‖𝓕 f (ξ-η)‖^2 * ‖knsRealFourier (knsMomentLocalizer n u) η‖^2) := by
  obtain ⟨hFT,_⟩ := memLp_fourier_norm_eq_of_integrable
    (integrable_knsLocalizedFourierSlice n u hf ξ) (memLp_knsLocalizedFourierSlice hn hu hf ξ)
  have h := (integrable_norm_sq_of_memLp_complex hFT).comp_neg
  convert! h using 1
  funext η
  rw [fourier_knsLocalizedFourierSlice n u hf, neg_neg, norm_mul, mul_pow,
    show -η+ξ=ξ-η by ring]

/-- Nonnegative-integral form of the exact fixed-frequency identity.
All slice integrability has already been proved from the actual data. -/
theorem lintegral_knsLocalizedFourierSlice_sq {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u)
    {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    (∫⁻ v, ENNReal.ofReal (‖knsLocalizedFourierSlice n u f ξ v‖^2)) =
      ∫⁻ η, ENNReal.ofReal (‖𝓕 f (ξ-η)‖^2) *
        ENNReal.ofReal (‖knsRealFourier (knsMomentLocalizer n u) η‖^2) := by
  have h := congrArg ENNReal.ofReal (integral_knsLocalizedFourierSlice_sq hn hu hf ξ)
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrable_norm_sq_of_memLp_complex (memLp_knsLocalizedFourierSlice hn hu hf ξ))
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),
    ofReal_integral_eq_lintegral_ofReal (integrable_knsFourierEnergy_convolution hn hu hf ξ)
      (Filter.Eventually.of_forall (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))] at h
  simpa only [ENNReal.ofReal_mul (sq_nonneg _)] using h

private theorem lintegral_weighted_shift_identity
    (S : ℝ → ℝ → ℝ≥0∞) (A B W : ℝ → ℝ≥0∞)
    (hS : Measurable (Function.uncurry S)) (hA : Measurable A)
    (hB : Measurable B) (hW : Measurable W)
    (hidentity : ∀ ξ, (∫⁻ v, S ξ v) = ∫⁻ η, A (ξ-η) * B η) :
    (∫⁻ v, ∫⁻ ξ, W ξ * S ξ v) = ∫⁻ ξ, ∫⁻ η, W (ξ+η) * (A ξ * B η) := by
  calc
    _ = ∫⁻ ξ, ∫⁻ v, W ξ * S ξ v := by
      apply lintegral_lintegral_swap
      exact ((hW.comp measurable_snd).mul (hS.comp measurable_swap)).aemeasurable
    _ = ∫⁻ ξ, ∫⁻ η, W ξ * (A (ξ-η) * B η) := by
      apply lintegral_congr
      intro ξ
      have hSξ : Measurable (S ξ) := hS.comp (measurable_prodMk_left (x := ξ))
      have hABξ : Measurable (fun η => A (ξ-η) * B η) :=
        (hA.comp (show Measurable (fun η : ℝ => ξ-η) from measurable_const.sub measurable_id)).mul hB
      rw [lintegral_const_mul (W ξ) hSξ, hidentity ξ]
      exact (lintegral_const_mul (W ξ) hABξ).symm
    _ = ∫⁻ η, ∫⁻ ξ, W ξ * (A (ξ-η) * B η) := by
      apply lintegral_lintegral_swap
      exact ((hW.comp measurable_fst).mul
        ((hA.comp (measurable_fst.sub measurable_snd)).mul (hB.comp measurable_snd))).aemeasurable
    _ = ∫⁻ η, ∫⁻ ξ, W (ξ+η) * (A ξ * B η) := by
      apply lintegral_congr
      intro η
      rw [← lintegral_add_right_eq_self (fun ξ => W ξ * (A (ξ-η) * B η)) η]
      simp only [add_sub_cancel_right]
    _ = _ := by
      apply lintegral_lintegral_swap
      exact ((hW.comp (measurable_snd.add measurable_fst)).mul
        ((hA.comp measurable_snd).mul (hB.comp measurable_fst))).aemeasurable

/-- Exact weighted translation-variable Plancherel and Tonelli identity
for the actual localized Fourier integrals. The nonnegative weight may
have infinite energy; finiteness is not smuggled in through Bochner defaults.
The frequency sum retains the precise translation and reflection signs. -/
theorem lintegral_weighted_knsLocalizedFourierEnergy
    {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u)
    {f : ℝ → ℂ} (hf : Integrable f) (W : ℝ → ℝ≥0∞) (hW : Measurable W) :
    (∫⁻ v, ∫⁻ ξ, W ξ * ENNReal.ofReal (‖knsLocalizedFourierSlice n u f ξ v‖^2)) =
      ∫⁻ ξ, ∫⁻ η, W (ξ+η) * (ENNReal.ofReal (‖𝓕 f ξ‖^2) *
        ENNReal.ofReal (‖knsRealFourier (knsMomentLocalizer n u) η‖^2)) := by
  have hfc : Continuous (𝓕 f : ℝ → ℂ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf
  have hFc : Continuous (knsRealFourier (knsMomentLocalizer n u)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (integrable_knsMomentLocalizer n u).ofReal
  exact lintegral_weighted_shift_identity
    (fun ξ v => ENNReal.ofReal (‖knsLocalizedFourierSlice n u f ξ v‖^2))
    (fun ξ => ENNReal.ofReal (‖𝓕 f ξ‖^2))
    (fun η => ENNReal.ofReal (‖knsRealFourier (knsMomentLocalizer n u) η‖^2)) W
    (((continuous_knsLocalizedFourierSlice hn hu hf).norm.pow 2).measurable.ennreal_ofReal)
    ((hfc.norm.pow 2).measurable.ennreal_ofReal)
    ((hFc.norm.pow 2).measurable.ennreal_ofReal) hW (lintegral_knsLocalizedFourierSlice_sq hn hu hf)

end

end MeyerGeneralProblem
