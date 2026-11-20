module

public import MeyerGeneralProblem.Sampling.KNSStageATranslationBounds

@[expose] public section

/-!
# Physical translation bounds for the initial KNS bootstrap

The exterior translation radius is chosen before both the power and its
truncation. Actual compact support and exact square mass of the localizer
give the physical lower bound by Tonelli, without a higher-moment premise.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter
open scoped FourierTransform ENNReal ContDiff

/-- Convexity at zero gives the lower linear dilation of the actual
tangent-truncated power. This is distinct from its upper power dilation. -/
theorem mul_knsTruncatedPower_le {p : ℕ} (hp : 1 ≤ p) {T x c : ℝ}
    (hT : 0 ≤ T) (hx : 0 ≤ x) (hc : 1 ≤ c) :
    c * knsTruncatedPower p T x ≤ knsTruncatedPower p T (c*x) := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hi0 : 0 ≤ c⁻¹ := inv_nonneg.mpr hc0.le
  have hi1 : c⁻¹ ≤ 1 := (inv_le_one₀ hc0).mpr hc
  have h := (convexOn_knsTruncatedPower p hT).2
    (show (0 : ℝ) ∈ Ici 0 by simp)
    (show c*x ∈ Ici 0 by change 0 ≤ c*x; positivity)
    (show 0 ≤ 1-c⁻¹ by linarith) hi0 (show (1-c⁻¹)+c⁻¹=1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, knsTruncatedPower_zero hp hT] at h
  rw [← mul_assoc, inv_mul_cancel₀ hc0.ne', one_mul] at h
  have h' := mul_le_mul_of_nonneg_left h hc0.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul] using h'

/-- A single exterior radius gives the exact sigma geometry for every
point in the true localizer support, independently of the weight order. -/
theorem exists_radius_kns_physical_geometry {σ r X0 : ℝ}
    (hσ : 1 < σ) :
    ∃ V > r, X0 ≤ V-r ∧ ∀ v : ℝ, V ≤ |v| →
      ∀ x : ℝ, |x-v| ≤ r → σ*x^2 ≤ (σ*(|v|-r))^2 := by
  have hs : 1 < Real.sqrt σ := by
    exact (Real.lt_sqrt (by norm_num)).mpr (by simpa using hσ)
  let V := max (r+max X0 1) (r+2*r/(Real.sqrt σ-1))
  have hV1 : r+max X0 1 ≤ V := le_max_left _ _
  have hV2 : r+2*r/(Real.sqrt σ-1) ≤ V := le_max_right _ _
  have hmax1 : (1 : ℝ) ≤ max X0 1 := le_max_right _ _
  have hmaxX : X0 ≤ max X0 1 := le_max_left _ _
  refine ⟨V, by linarith, by linarith, ?_⟩
  intro v hv x hx
  have hvr : 0 ≤ |v|-r := by linarith
  have hratio : 2*r ≤ (|v|-r)*(Real.sqrt σ-1) := by
    apply (div_le_iff₀ (by linarith : 0 < Real.sqrt σ-1)).mp
    linarith
  have htri : |x| ≤ |v|+r := by
    have h := abs_add_le (x-v) v
    rw [sub_add_cancel] at h
    linarith
  have hlin : |x| ≤ Real.sqrt σ*(|v|-r) := by nlinarith
  have hsq := pow_le_pow_left₀ (abs_nonneg x) hlin 2
  rw [sq_abs, mul_pow, Real.sq_sqrt (by linarith : 0 ≤ σ)] at hsq
  have hmul := mul_le_mul_of_nonneg_left hsq (by linarith : 0 ≤ σ)
  nlinarith

/-- Exact translation square mass of the actual compact localizer,
including translations on the opposite side of the origin. -/
theorem lintegral_knsMomentLocalizer_translate_sq {n : ℕ} (hn : 1 ≤ n)
    {u : ℝ} (hu : 0 < u) (x : ℝ) :
    (∫⁻ v, ENNReal.ofReal (|knsMomentLocalizer n u (x-v)|^2)) =
      ENNReal.ofReal (∫ y, |knsMomentLocalizer n u y|^2) := by
  rw [lintegral_sub_left_eq_self (fun y => ENNReal.ofReal (|knsMomentLocalizer n u y|^2)) x]
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrable_knsMomentLocalizer_sq hn hu)
    (Eventually.of_forall (fun _ => sq_nonneg _))).symm

/-- Outside the enlarged physical center, restricting translations to
the exterior loses none of the genuine localizer square mass. -/
theorem lintegral_knsMomentLocalizer_exterior_sq {n : ℕ} (hn : 1 ≤ n)
    {u V x : ℝ} (hu : 0 < u) (hx : V+3*u/2 ≤ |x|) :
    (∫⁻ v in {v : ℝ | V ≤ |v|}, ENNReal.ofReal (|knsMomentLocalizer n u (x-v)|^2)) =
      ENNReal.ofReal (∫ y, |knsMomentLocalizer n u y|^2) := by
  rw [← lintegral_indicator (measurableSet_le measurable_const continuous_abs.measurable)]
  rw [← lintegral_knsMomentLocalizer_translate_sq hn hu x]
  apply lintegral_congr
  intro v
  by_cases hv : V ≤ |v|
  · simp [hv]
  · have hzero : knsMomentLocalizer n u (x-v) = 0 := by
      by_contra hne
      have hs := support_knsMomentLocalizer_subset hn u hne
      have hdist : |x-v| ≤ 3*u/2 := abs_le.mpr hs
      have htri := abs_add_le (x-v) v
      rw [sub_add_cancel] at htri
      have hv' : |v| < V := lt_of_not_ge hv
      linarith
    simp [hv,hzero]

/-- Tonelli turns the genuine compact localization into a physical
exterior lower bound with its exact mass. Infinite weighted energies
are permitted here; no higher-moment integrability is presumed. -/
theorem lintegral_knsLocalizedFunction_exterior_lower {n : ℕ} (hn : 1 ≤ n)
    {u : ℝ} (hu : 0 < u) (V : ℝ) {f : ℝ → ℂ} (hf : Continuous f)
    (W : ℝ → ℝ≥0∞) (hW : Measurable W) :
    ENNReal.ofReal (∫ y, |knsMomentLocalizer n u y|^2) *
        (∫⁻ x in {x : ℝ | V+3*u/2 ≤ |x|}, W x * ENNReal.ofReal (‖f x‖^2)) ≤
      ∫⁻ v in {v : ℝ | V ≤ |v|}, ∫⁻ x,
        W x * ENNReal.ofReal (‖knsLocalizedFunction n u v f x‖^2) := by
  let g : ℝ → ℝ≥0∞ := fun x => W x * ENNReal.ofReal (‖f x‖^2)
  let K : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (|knsMomentLocalizer n u y|^2)
  have hg : Measurable g := hW.mul ((hf.norm.pow 2).measurable.ennreal_ofReal)
  have hK : Measurable K :=
    (((continuous_knsMomentLocalizer n hu.le).abs.pow 2).measurable.ennreal_ofReal)
  calc
    _ = ∫⁻ x in {x : ℝ | V+3*u/2 ≤ |x|},
        g x * ENNReal.ofReal (∫ y, |knsMomentLocalizer n u y|^2) := by
      rw [lintegral_mul_const _ hg, mul_comm]
    _ = ∫⁻ x in {x : ℝ | V+3*u/2 ≤ |x|},
        ∫⁻ v in {v : ℝ | V ≤ |v|}, g x * K (x-v) := by
      apply setLIntegral_congr_fun (measurableSet_le measurable_const continuous_abs.measurable)
      intro x hx
      have hKx : Measurable (fun v : ℝ => K (x-v)) :=
        hK.comp (measurable_const.sub measurable_id)
      change g x * _ = ∫⁻ v in {v : ℝ | V ≤ |v|}, g x * K (x-v)
      rw [lintegral_const_mul (g x) hKx]
      exact congrArg (g x * ·) (lintegral_knsMomentLocalizer_exterior_sq hn hu hx).symm
    _ ≤ ∫⁻ x, ∫⁻ v in {v : ℝ | V ≤ |v|}, g x * K (x-v) := by
      exact lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ v in {v : ℝ | V ≤ |v|}, ∫⁻ x, g x * K (x-v) := by
      apply lintegral_lintegral_swap
      exact ((hg.comp measurable_fst).mul
        (hK.comp (measurable_fst.sub measurable_snd))).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro v
      apply lintegral_congr
      intro x
      simp only [g, K, knsLocalizedFunction, norm_mul, mul_pow,
        Complex.norm_real, Real.norm_eq_abs, ENNReal.ofReal_mul (sq_nonneg _), mul_assoc]

/-- Restoring the finite physical center costs only the original L2
mass and an explicit untruncated radius power, independent of T. -/
theorem lintegral_knsTruncatedPower_restore_center {p : ℕ} (hp : 1 ≤ p)
    {T R : ℝ} (hT : 0 ≤ T) {f : ℝ → ℂ} (hf : Continuous f) :
    (∫⁻ x, ENNReal.ofReal (knsTruncatedPower p T (x^2)) * ENNReal.ofReal (‖f x‖^2)) ≤
      (∫⁻ x in {x : ℝ | R ≤ |x|},
        ENNReal.ofReal (knsTruncatedPower p T (x^2)) * ENNReal.ofReal (‖f x‖^2)) +
      ENNReal.ofReal (R^(2*p)) * ∫⁻ x, ENNReal.ofReal (‖f x‖^2) := by
  let w : ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (knsTruncatedPower p T (x^2)) * ENNReal.ofReal (‖f x‖^2)
  have hw : Measurable w :=
    (((contDiff_one_knsTruncatedPower p T).continuous.comp (continuous_id.pow 2)).measurable.ennreal_ofReal).mul
      ((hf.norm.pow 2).measurable.ennreal_ofReal)
  have hs : MeasurableSet {x : ℝ | R ≤ |x|} := measurableSet_le measurable_const continuous_abs.measurable
  calc
    _ ≤ ∫⁻ x, {x : ℝ | R ≤ |x|}.indicator w x +
        ENNReal.ofReal (R^(2*p))*ENNReal.ofReal (‖f x‖^2) := by
      apply lintegral_mono
      intro x
      change w x ≤ {x : ℝ | R ≤ |x|}.indicator w x + _
      by_cases hx : R ≤ |x|
      · rw [indicator_of_mem (show x ∈ {x : ℝ | R ≤ |x|} from hx)]
        exact le_add_right le_rfl
      · rw [indicator_of_notMem (show x ∉ {x : ℝ | R ≤ |x|} from hx), zero_add]
        have hsq : x^2 ≤ R^2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (le_of_lt (lt_of_not_ge hx)) 2
        have hpow := pow_le_pow_left₀ (sq_nonneg x) hsq p
        have h := (knsTruncatedPower_le_pow hp hT (sq_nonneg x)).trans hpow
        rw [← pow_mul] at h
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal h) _
    _ = _ := by
      have hfn : Measurable (fun x => ENNReal.ofReal (‖f x‖^2)) :=
        (hf.norm.pow 2).measurable.ennreal_ofReal
      rw [lintegral_add_left (hw.indicator hs), lintegral_indicator hs,
        lintegral_const_mul _ hfn]

private theorem knsTruncatedPower_localized_pointwise_le
    {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n) {T u σ v : ℝ}
    (hT : 0 ≤ T) (hσ : 1 ≤ σ)
    (hgeom : ∀ x : ℝ, |x-v| ≤ 3*u/2 → σ*x^2 ≤ (σ*(|v|-3*u/2))^2)
    (f : ℝ → ℂ) (x : ℝ) :
    σ * knsTruncatedPower p T (x^2) * ‖knsLocalizedFunction n u v f x‖^2 ≤
      knsTruncatedPower p T ((σ*(|v|-3*u/2))^2) * ‖knsLocalizedFunction n u v f x‖^2 := by
  by_cases hF : knsMomentLocalizer n u (x-v) = 0
  · simp [knsLocalizedFunction,hF]
  have hs := abs_le.mpr (support_knsMomentLocalizer_subset hn u hF)
  have hscale := mul_knsTruncatedPower_le hp hT (sq_nonneg x) hσ
  have hσ0 : 0 ≤ σ := by linarith
  have hmono := monotoneOn_knsTruncatedPower p hT
    (mul_nonneg hσ0 (sq_nonneg x))
    (show (σ*(|v|-3*u/2))^2 ∈ Ici 0 by change 0 ≤ (σ*(|v|-3*u/2))^2; positivity)
    (hgeom x hs)
  exact mul_le_mul_of_nonneg_right (hscale.trans hmono) (sq_nonneg _)

private theorem lintegral_knsTruncatedPower_localized_le
    {p n : ℕ} (hp : 1 ≤ p) (hn : 2 ≤ n) {T u σ v : ℝ}
    (hT : 0 ≤ T) (hu : 0 < u) (hσ : 1 ≤ σ)
    (hgeom : ∀ x : ℝ, |x-v| ≤ 3*u/2 → σ*x^2 ≤ (σ*(|v|-3*u/2))^2)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hP : knsTruncatedPower p T ((σ*(|v|-3*u/2))^2) *
        (∫ x, ‖knsLocalizedFunction n u v f x‖^2) ≤
      ∫ ξ, knsTruncatedPower p T (ξ^2) * ‖𝓕 (knsLocalizedFunction n u v f) ξ‖^2) :
    ENNReal.ofReal σ * (∫⁻ x, ENNReal.ofReal (knsTruncatedPower p T (x^2)) *
        ENNReal.ofReal (‖knsLocalizedFunction n u v f x‖^2)) ≤
      ∫⁻ ξ, ENNReal.ofReal (knsTruncatedPower p T (ξ^2)) *
        ENNReal.ofReal (‖𝓕 (knsLocalizedFunction n u v f) ξ‖^2) := by
  let c := knsTruncatedPower p T ((σ*(|v|-3*u/2))^2)
  have hc : 0 ≤ c := knsTruncatedPower_nonneg hp hT (sq_nonneg _)
  have hσ0 : 0 ≤ σ := by linarith
  have hnorm := integrable_norm_sq_of_memLp_complex
    (memLp_knsLocalizedFunction_and_deriv hn hu v hf).1
  have hreal := ENNReal.ofReal_le_ofReal hP
  rw [ENNReal.ofReal_mul hc,
    ofReal_integral_eq_lintegral_ofReal hnorm (Eventually.of_forall (fun _ => sq_nonneg _)),
    ofReal_integral_eq_lintegral_ofReal
      (integrable_knsTruncatedPower_localizedFourier hp hn hT hu v hf)
      (Eventually.of_forall (fun ξ => mul_nonneg
        (knsTruncatedPower_nonneg hp hT (sq_nonneg ξ)) (sq_nonneg _)))] at hreal
  simp only [ENNReal.ofReal_mul (knsTruncatedPower_nonneg hp hT (sq_nonneg _))] at hreal
  apply le_trans _ hreal
  rw [← lintegral_const_mul' (ENNReal.ofReal σ) _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' (ENNReal.ofReal c) _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro x
  have h := ENNReal.ofReal_le_ofReal
    (knsTruncatedPower_localized_pointwise_le (n := n) hp (by omega) hT hσ hgeom f x)
  change ENNReal.ofReal (σ * knsTruncatedPower p T (x^2) * _) ≤ ENNReal.ofReal (c * _) at h
  simpa only [ENNReal.ofReal_mul hσ0, ENNReal.ofReal_mul hc,
    ENNReal.ofReal_mul (mul_nonneg hσ0 (knsTruncatedPower_nonneg hp hT (sq_nonneg x))),
    ENNReal.ofReal_mul (knsTruncatedPower_nonneg hp hT (sq_nonneg x)), mul_assoc] using h

/-- Actual finite-deletion reciprocal-gap geometry yields the physical
translation lower bound. The radius precedes n, the unknown, the power,
and T; the exact square mass is retained, and no higher moment is assumed. -/
theorem exists_radius_knsStageA_physical_lower
    (Λ : TwoSidedCarrier) (F J : Finset ℤ) {σ : ℝ} (hσ : 1 < σ)
    (hgap : ∀ j : ℤ, j ∉ J →
      max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ (2*σ)⁻¹)
    {u : ℝ} (hu : 0 < u) :
    ∃ V > 3*u/2, ∀ (n : ℕ), 2 ≤ n →
      ∀ (f : ℝ → ℂ), ContDiff ℝ 1 f → (∀ j : ℤ, j ∉ F → f (Λ j) = 0) →
      ∀ (p : ℕ), 1 ≤ p → ∀ T : ℝ, 0 ≤ T →
      ENNReal.ofReal σ * ENNReal.ofReal (∫ y, |knsMomentLocalizer n u y|^2) *
          (∫⁻ x in {x : ℝ | V+3*u/2 ≤ |x|},
            ENNReal.ofReal (knsTruncatedPower p T (x^2)) * ENNReal.ofReal (‖f x‖^2)) ≤
        ∫⁻ v, ∫⁻ ξ, ENNReal.ofReal (knsTruncatedPower p T (ξ^2)) *
          ENNReal.ofReal (‖knsLocalizedFourierSlice n u f ξ v‖^2) := by
  obtain ⟨X0,hX0,hP⟩ := exists_radius_truncatedPower_poincare_of_finite_exceptions
    Λ F J (by linarith : 0 < σ) hgap
  obtain ⟨V,hV,hXV,hgeom⟩ := exists_radius_kns_physical_geometry (r := 3*u/2) (X0 := X0) hσ
  refine ⟨V,hV,?_⟩
  intro n hn f hf hz p hp T hT
  let W : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (knsTruncatedPower p T (x^2))
  have hW : Measurable W :=
    ((contDiff_one_knsTruncatedPower p T).continuous.comp (continuous_id.pow 2)).measurable.ennreal_ofReal
  have hbase := lintegral_knsLocalizedFunction_exterior_lower (by omega : 1 ≤ n)
    hu V hf.continuous W hW
  have hbase' := mul_le_mul_right hbase (ENNReal.ofReal σ)
  rw [← mul_assoc] at hbase'
  apply hbase'.trans
  rw [← lintegral_const_mul' (ENNReal.ofReal σ) _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ∫⁻ v in {v : ℝ | V ≤ |v|}, ∫⁻ ξ, W ξ *
        ENNReal.ofReal (‖knsLocalizedFourierSlice n u f ξ v‖^2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_le measurable_const continuous_abs.measurable)] with v hv
      exact lintegral_knsTruncatedPower_localized_le hp hn hT hu hσ.le (hgeom v hv) hf
        (hP n hn u hu v (by change V ≤ |v| at hv; linarith) f hf hz p hp T hT)
    _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl

/-- The full physical truncated energy is bounded by genuine localized
Fourier energy plus an explicit central L2 term. Both constants and the
physical radius are independent of T and of the unknown function. -/
theorem exists_radius_knsStageA_physical_full
    (Λ : TwoSidedCarrier) (F J : Finset ℤ) {σ : ℝ} (hσ : 1 < σ)
    (hgap : ∀ j : ℤ, j ∉ J →
      max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ (2*σ)⁻¹)
    {u : ℝ} (hu : 0 < u) :
    ∃ R > 0, ∀ (n : ℕ), 2 ≤ n →
      ∀ (f : ℝ → ℂ), ContDiff ℝ 1 f → (∀ j : ℤ, j ∉ F → f (Λ j) = 0) →
      ∀ (p : ℕ), 1 ≤ p → ∀ T : ℝ, 0 ≤ T →
      ENNReal.ofReal σ * ENNReal.ofReal (∫ y, |knsMomentLocalizer n u y|^2) *
          (∫⁻ x, ENNReal.ofReal (knsTruncatedPower p T (x^2)) * ENNReal.ofReal (‖f x‖^2)) ≤
        (∫⁻ v, ∫⁻ ξ, ENNReal.ofReal (knsTruncatedPower p T (ξ^2)) *
          ENNReal.ofReal (‖knsLocalizedFourierSlice n u f ξ v‖^2)) +
        ENNReal.ofReal σ * ENNReal.ofReal (∫ y, |knsMomentLocalizer n u y|^2) *
          ENNReal.ofReal (R^(2*p)) * ∫⁻ x, ENNReal.ofReal (‖f x‖^2) := by
  obtain ⟨V,hV,h⟩ := exists_radius_knsStageA_physical_lower Λ F J hσ hgap hu
  refine ⟨V+3*u/2,by linarith,?_⟩
  intro n hn f hf hz p hp T hT
  have hrestore := mul_le_mul_right
    (lintegral_knsTruncatedPower_restore_center (R := V+3*u/2) hp hT hf.continuous)
    (ENNReal.ofReal σ * ENNReal.ofReal (∫ y, |knsMomentLocalizer n u y|^2))
  rw [mul_add, ← mul_assoc] at hrestore
  exact hrestore.trans (add_le_add_left (h n hn f hf hz p hp T hT) _)

/-- Combining the physical bound with the actual translation-variable
Plancherel identity gives the true shifted Fourier energy, with the
finite center restored and no higher-moment assumption on the L1 input. -/
theorem exists_radius_knsStageA_physical_fourier
    (Λ : TwoSidedCarrier) (F J : Finset ℤ) {σ : ℝ} (hσ : 1 < σ)
    (hgap : ∀ j : ℤ, j ∉ J →
      max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ (2*σ)⁻¹)
    {u : ℝ} (hu : 0 < u) :
    ∃ R > 0, ∀ (n : ℕ), 2 ≤ n →
      ∀ (f : ℝ → ℂ), ContDiff ℝ 1 f → Integrable f →
      (∀ j : ℤ, j ∉ F → f (Λ j) = 0) →
      ∀ (p : ℕ), 1 ≤ p → ∀ T : ℝ, 0 ≤ T →
      ENNReal.ofReal σ * ENNReal.ofReal (∫ y, |knsMomentLocalizer n u y|^2) *
          (∫⁻ x, ENNReal.ofReal (knsTruncatedPower p T (x^2)) * ENNReal.ofReal (‖f x‖^2)) ≤
        (∫⁻ ξ, ∫⁻ η, ENNReal.ofReal (knsTruncatedPower p T ((ξ+η)^2)) *
          (ENNReal.ofReal (‖𝓕 f ξ‖^2) *
            ENNReal.ofReal (‖knsRealFourier (knsMomentLocalizer n u) η‖^2))) +
        ENNReal.ofReal σ * ENNReal.ofReal (∫ y, |knsMomentLocalizer n u y|^2) *
          ENNReal.ofReal (R^(2*p)) * ∫⁻ x, ENNReal.ofReal (‖f x‖^2) := by
  obtain ⟨R,hR,h⟩ := exists_radius_knsStageA_physical_full Λ F J hσ hgap hu
  refine ⟨R,hR,?_⟩
  intro n hn f hf hf1 hz p hp T hT
  have hb := h n hn f hf hz p hp T hT
  have hW : Measurable (fun x : ℝ => ENNReal.ofReal (knsTruncatedPower p T (x^2))) :=
    ((contDiff_one_knsTruncatedPower p T).continuous.comp (continuous_id.pow 2)).measurable.ennreal_ofReal
  rw [lintegral_weighted_knsLocalizedFourierEnergy (by omega : 1 ≤ n) hu hf1
    (fun x => ENNReal.ofReal (knsTruncatedPower p T (x^2))) hW] at hb
  exact hb

end

end MeyerGeneralProblem
