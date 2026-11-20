module

public import MeyerGeneralProblem.Sampling.KNSLocalizedFourierEnergy
public import MeyerGeneralProblem.Sampling.KNSTruncatedPower

@[expose] public section

/-!
# Truncation-uniform Fourier translation bounds for the initial KNS bootstrap

Finite-order box convolutions supply the exact finite Fourier moments needed
at each fixed power. The actual shifted tangent-truncated weight is bounded
uniformly in its threshold; no Schwartz property of the unknown is used.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter
open scoped FourierTransform ENNReal Topology

/-- Exact L2 Fourier mass of the actual long box, with its integrability
proved from the indicator rather than assumed as a transform certificate. -/
theorem knsBoxFourier_energy {u : ℝ} (hu : 0 ≤ u) :
    Integrable (fun η => ‖knsRealFourier (knsBox u) η‖^2) ∧
      (∫ η, ‖knsRealFourier (knsBox u) η‖^2) = 2*u := by
  have hbox : Integrable (fun x => (knsBox u x : ℂ)) := (integrable_knsBox u).ofReal
  have he : (fun x => ‖(knsBox u x : ℂ)‖^2) = knsBox u := by
    funext x
    by_cases hx : x ∈ Icc (-u) u <;> simp [knsBox,hx]
  have hbox2 : MemLp (fun x => (knsBox u x : ℂ)) 2 := by
    apply (memLp_two_iff_integrable_sq_norm hbox.aestronglyMeasurable).mpr
    convert! integrable_knsBox u using 1
  obtain ⟨hFT,hnorm⟩ := memLp_fourier_norm_eq_of_integrable hbox hbox2
  refine ⟨integrable_norm_sq_of_memLp_complex hFT,?_⟩
  change (∫ η, ‖𝓕 (fun x => (knsBox u x : ℂ)) η‖^2) = 2*u
  calc
    _ = ‖hFT.toLp‖^2 := by convert! integral_norm_sq_eq_toLp_norm_sq_complex hFT using 1
    _ = ‖hbox2.toLp‖^2 := by rw [hnorm]
    _ = ∫ x, ‖(knsBox u x : ℂ)‖^2 := by
      symm
      convert! integral_norm_sq_eq_toLp_norm_sq_complex hbox2 using 1
    _ = 2*u := by rw [he, integral_knsBox hu]

/-- Actual localizer Fourier energy equals its physical square mass;
in particular it is strictly positive, since that mass is at least u. -/
theorem knsLocalizerFourier_energy {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u) :
    Integrable (fun η => ‖knsRealFourier (knsMomentLocalizer n u) η‖^2) ∧
      (∫ η, ‖knsRealFourier (knsMomentLocalizer n u) η‖^2) =
        (∫ x, |knsMomentLocalizer n u x|^2) ∧
      u ≤ ∫ η, ‖knsRealFourier (knsMomentLocalizer n u) η‖^2 := by
  have hF : Integrable (fun x => (knsMomentLocalizer n u x : ℂ)) :=
    (integrable_knsMomentLocalizer n u).ofReal
  have hF2 : MemLp (fun x => (knsMomentLocalizer n u x : ℂ)) 2 := by
    apply (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mpr
    simpa only [Complex.norm_real, Real.norm_eq_abs] using! integrable_knsMomentLocalizer_sq hn hu
  obtain ⟨hFT,hnorm⟩ := memLp_fourier_norm_eq_of_integrable hF hF2
  have he : (∫ η, ‖knsRealFourier (knsMomentLocalizer n u) η‖^2) =
      ∫ x, |knsMomentLocalizer n u x|^2 := by
    change (∫ η, ‖𝓕 (fun x => (knsMomentLocalizer n u x : ℂ)) η‖^2) = _
    calc
      _ = ‖hFT.toLp‖^2 := by convert! integral_norm_sq_eq_toLp_norm_sq_complex hFT using 1
      _ = ‖hF2.toLp‖^2 := by rw [hnorm]
      _ = ∫ x, ‖(knsMomentLocalizer n u x : ℂ)‖^2 := by
        symm
        convert! integral_norm_sq_eq_toLp_norm_sq_complex hF2 using 1
      _ = _ := by simp only [Complex.norm_real, Real.norm_eq_abs]
  exact ⟨integrable_norm_sq_of_memLp_complex hFT,he,he.symm ▸ integral_knsMomentLocalizer_sq_ge hn hu⟩

/-- The true finite-order sinc factors absorb every polynomial weight
up to that order, with the exact scale n/(pi*u). This works already at n=p. -/
theorem knsLocalizerFourier_weighted_pointwise_le {p n : ℕ} (hn : 1 ≤ n) (hpn : p ≤ n)
    {u : ℝ} (hu : 0 < u) (ξ η : ℝ) :
    (|ξ|+|η|)^(2*p) * ‖knsRealFourier (knsMomentLocalizer n u) η‖^2 ≤
      (|ξ|+n/(Real.pi*u))^(2*p) * ‖knsRealFourier (knsBox u) η‖^2 := by
  let s := |Real.sinc (Real.pi*u*η/n)|
  have hs0 : 0 ≤ s := abs_nonneg _
  have hs1 : s ≤ 1 := Real.abs_sinc_le_one _
  have hsn : s^n ≤ s^p := pow_le_pow_of_le_one hs0 hs1 hpn
  have hnorm : ‖knsRealFourier (knsMomentLocalizer n u) η‖ ≤
      ‖knsRealFourier (knsBox u) η‖ * s^p := by
    rw [knsRealFourier_localizer hn hu, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hsn (norm_nonneg _)
  have hsinc : (|ξ|+|η|)*s ≤ |ξ|+n/(Real.pi*u) := kns_weighted_sinc_le hn hu ξ η
  have hp : (|ξ|+|η|)^p * s^p ≤ (|ξ|+n/(Real.pi*u))^p := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg (by positivity) hs0) hsinc p
  have h : (|ξ|+|η|)^p * ‖knsRealFourier (knsMomentLocalizer n u) η‖ ≤
      ‖knsRealFourier (knsBox u) η‖ * (|ξ|+n/(Real.pi*u))^p := by
    calc
      _ ≤ (|ξ|+|η|)^p * (‖knsRealFourier (knsBox u) η‖ * s^p) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = ‖knsRealFourier (knsBox u) η‖ * ((|ξ|+|η|)^p * s^p) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
  have hh := (sq_le_sq₀ (by positivity) (by positivity)).mpr h
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm, mul_comm] using hh

/-- Every required finite Fourier moment is integrable, with an explicit
constant supplied by the long-box Plancherel mass. -/
theorem knsLocalizerFourier_polynomialMoment {p n : ℕ} (hn : 1 ≤ n) (hpn : p ≤ n)
    {u : ℝ} (hu : 0 < u) :
    Integrable (fun η => (1+|η|)^(2*p) * ‖knsRealFourier (knsMomentLocalizer n u) η‖^2) ∧
      (∫ η, (1+|η|)^(2*p) * ‖knsRealFourier (knsMomentLocalizer n u) η‖^2) ≤
        2*u*(1+n/(Real.pi*u))^(2*p) := by
  obtain ⟨hbox,hboxmass⟩ := knsBoxFourier_energy hu.le
  have hc : Continuous (knsRealFourier (knsMomentLocalizer n u)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (integrable_knsMomentLocalizer n u).ofReal
  have hm : AEStronglyMeasurable (fun η =>
      (1+|η|)^(2*p) * ‖knsRealFourier (knsMomentLocalizer n u) η‖^2) volume :=
    (show Continuous _ by fun_prop).aestronglyMeasurable
  have hb (η : ℝ) := knsLocalizerFourier_weighted_pointwise_le hn hpn hu 1 η
  simp only [abs_one] at hb
  have hint : Integrable (fun η => (1+|η|)^(2*p) *
      ‖knsRealFourier (knsMomentLocalizer n u) η‖^2) := by
    apply (hbox.const_mul ((1+n/(Real.pi*u))^(2*p))).mono' hm
    filter_upwards [] with η
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hb η
  refine ⟨hint,?_⟩
  calc
    _ ≤ ∫ η, (1+n/(Real.pi*u))^(2*p) * ‖knsRealFourier (knsBox u) η‖^2 :=
      integral_mono hint (hbox.const_mul _) hb
    _ = _ := by rw [integral_const_mul,hboxmass]; ring

/-- The actual tangent-truncated shifted weight has the original power
dilation bound uniformly in the threshold, with no division at zero. -/
theorem knsTruncatedPower_shift_le {p : ℕ} (hp : 1 ≤ p) {T ξ : ℝ}
    (hT : 0 ≤ T) (hξ : ξ ≠ 0) (η : ℝ) :
    knsTruncatedPower p T ((ξ+η)^2) ≤
      knsTruncatedPower p T (ξ^2) * (1+|η|/|ξ|)^(2*p) := by
  have hx : 0 < |ξ| := abs_pos.mpr hξ
  have hc : 1 ≤ 1+|η|/|ξ| := by
    have h : 0 ≤ |η|/|ξ| := by positivity
    linarith
  have he : (1+|η|/|ξ|)*|ξ| = |ξ|+|η| := by field_simp
  have he2 := congrArg (fun x : ℝ => x^2) he
  simp only [mul_pow,sq_abs] at he2
  have hsq : (ξ+η)^2 ≤ (1+|η|/|ξ|)^2 * ξ^2 := by
    rw [he2,← sq_abs (ξ+η)]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_add_le ξ η) 2
  have hmono := monotoneOn_knsTruncatedPower p hT (sq_nonneg (ξ+η))
    (by positivity : 0 ≤ (1+|η|/|ξ|)^2 * ξ^2) hsq
  have hscale := knsTruncatedPower_mul_le hp hT (sq_nonneg ξ)
    (show 1 ≤ (1+|η|/|ξ|)^2 by nlinarith)
  exact hmono.trans (by simpa only [← pow_mul,mul_comm] using hscale)

private theorem one_add_scaled_pow_le {m : ℕ} (hm : 1 ≤ m) {a t : ℝ}
    (ha : 0 ≤ a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1+t*a)^m ≤ 1+t*(1+a)^m := by
  have hc : ConvexOn ℝ (Ici 0) (fun x : ℝ => x^m) := by
    simpa only [Real.rpow_natCast] using convexOn_rpow (show (1:ℝ) ≤ m by exact_mod_cast hm)
  have h := hc.2 (show (1:ℝ) ∈ Ici 0 by norm_num)
    (show 1+a ∈ Ici 0 by change 0≤1+a; linarith)
    (show 0≤1-t by linarith) ht0 (show (1-t)+t=1 by ring)
  simp only [smul_eq_mul,one_pow,mul_one] at h
  have he : 1-t+t*(1+a)=1+t*a := by ring
  rw [he] at h
  linarith

/-- The normalized frequency-shift moment has an explicit inverse-radius
error. Its coefficient is independent of the truncation parameter and unknown. -/
theorem knsLocalizerFourier_relativeMoment_le {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hpn : p ≤ n) {u r : ℝ} (hu : 0 < u) (hr : 1 ≤ r) :
    Integrable (fun η => ‖knsRealFourier (knsMomentLocalizer n u) η‖^2 * (1+|η|/r)^(2*p)) ∧
      (∫ η, ‖knsRealFourier (knsMomentLocalizer n u) η‖^2 * (1+|η|/r)^(2*p)) ≤
        (∫ η, ‖knsRealFourier (knsMomentLocalizer n u) η‖^2) +
          (2*u*(1+n/(Real.pi*u))^(2*p))/r := by
  obtain ⟨hM,hMbound⟩ := knsLocalizerFourier_polynomialMoment hn hpn hu
  have hK := (knsLocalizerFourier_energy hn hu).1
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hratio (η : ℝ) : 1+|η|/r ≤ 1+|η| := by
    have h := (div_le_iff₀ hr0).mpr (show |η| ≤ |η| * r by nlinarith [abs_nonneg η])
    linarith
  have hc : Continuous (knsRealFourier (knsMomentLocalizer n u)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (integrable_knsMomentLocalizer n u).ofReal
  have hint : Integrable (fun η => ‖knsRealFourier (knsMomentLocalizer n u) η‖^2 *
      (1+|η|/r)^(2*p)) := by
    apply hM.mono' (show AEStronglyMeasurable _ volume from
      (show Continuous _ by fun_prop).aestronglyMeasurable)
    filter_upwards [] with η
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hpw := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|η|/r) (hratio η) (2*p)
    nlinarith [sq_nonneg (‖knsRealFourier (knsMomentLocalizer n u) η‖)]
  have hpoint (η : ℝ) :
      ‖knsRealFourier (knsMomentLocalizer n u) η‖^2 * (1+|η|/r)^(2*p) ≤
      ‖knsRealFourier (knsMomentLocalizer n u) η‖^2 +
        r⁻¹*((1+|η|)^(2*p) * ‖knsRealFourier (knsMomentLocalizer n u) η‖^2) := by
    have ht : r⁻¹ ≤ 1 := (inv_le_one₀ hr0).mpr hr
    have hh := one_add_scaled_pow_le (by omega : 1 ≤ 2*p) (abs_nonneg η) (inv_nonneg.mpr hr0.le) ht
    have he : 1+r⁻¹*|η| = 1+|η|/r := by ring
    rw [he] at hh
    have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖knsRealFourier (knsMomentLocalizer n u) η‖)
    nlinarith
  refine ⟨hint,?_⟩
  calc
    _ ≤ ∫ η, ‖knsRealFourier (knsMomentLocalizer n u) η‖^2 +
        r⁻¹*((1+|η|)^(2*p) * ‖knsRealFourier (knsMomentLocalizer n u) η‖^2) :=
      integral_mono hint (hK.add (hM.const_mul _)) hpoint
    _ = (∫ η, ‖knsRealFourier (knsMomentLocalizer n u) η‖^2) +
        r⁻¹*(∫ η, (1+|η|)^(2*p) * ‖knsRealFourier (knsMomentLocalizer n u) η‖^2) := by
      rw [integral_add hK (hM.const_mul _),integral_const_mul]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hMbound (inv_nonneg.mpr hr0.le)
      rw [div_eq_mul_inv]
      nlinarith

/-- The central-frequency term also has a genuine bound independent of
T, valid even at zero frequency. Its integrability is a conclusion of the
actual finite-order cutoff, not a higher-moment premise on the unknown. -/
theorem knsTruncatedPower_fourier_shift_bound {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hpn : p ≤ n) {u T : ℝ} (hu : 0 < u) (hT : 0 ≤ T) (ξ : ℝ) :
    Integrable (fun η => knsTruncatedPower p T ((ξ+η)^2) *
      ‖knsRealFourier (knsMomentLocalizer n u) η‖^2) ∧
      (∫ η, knsTruncatedPower p T ((ξ+η)^2) * ‖knsRealFourier (knsMomentLocalizer n u) η‖^2) ≤
        2*u*(|ξ|+n/(Real.pi*u))^(2*p) := by
  obtain ⟨hbox,hboxmass⟩ := knsBoxFourier_energy hu.le
  have hc : Continuous (knsRealFourier (knsMomentLocalizer n u)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (integrable_knsMomentLocalizer n u).ofReal
  have htr := (contDiff_one_knsTruncatedPower p T).continuous
  have hb (η : ℝ) : knsTruncatedPower p T ((ξ+η)^2) *
      ‖knsRealFourier (knsMomentLocalizer n u) η‖^2 ≤
      (|ξ|+n/(Real.pi*u))^(2*p) * ‖knsRealFourier (knsBox u) η‖^2 := by
    have hpow : ((ξ+η)^2)^p ≤ (|ξ|+|η|)^(2*p) := by
      rw [← sq_abs (ξ+η),← pow_mul]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_add_le ξ η) (2*p)
    have h := mul_le_mul_of_nonneg_right
      ((knsTruncatedPower_le_pow hp hT (sq_nonneg (ξ+η))).trans hpow)
      (sq_nonneg ‖knsRealFourier (knsMomentLocalizer n u) η‖)
    exact h.trans (knsLocalizerFourier_weighted_pointwise_le hn hpn hu ξ η)
  have hi : Integrable (fun η => knsTruncatedPower p T ((ξ+η)^2) *
      ‖knsRealFourier (knsMomentLocalizer n u) η‖^2) := by
    apply (hbox.const_mul ((|ξ|+n/(Real.pi*u))^(2*p))).mono'
      (show AEStronglyMeasurable _ volume from (show Continuous _ by fun_prop).aestronglyMeasurable)
    filter_upwards [] with η
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
      (knsTruncatedPower_nonneg hp hT (sq_nonneg (ξ+η))) (sq_nonneg _))]
    exact hb η
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ η, (|ξ|+n/(Real.pi*u))^(2*p) * ‖knsRealFourier (knsBox u) η‖^2 :=
      integral_mono hi (hbox.const_mul _) hb
    _ = _ := by rw [integral_const_mul,hboxmass]; ring

/-- The genuine shifted truncated Fourier weight has a radius-uniform
bound as close to its mass coefficient as desired. The explicit choice
max(1, 2u(1+n/(pi*u))^(2p)/delta) precedes T and the frequency. -/
theorem exists_radius_knsTruncatedPower_fourier_shift_le
    {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n) (hpn : p ≤ n)
    {u δ : ℝ} (hu : 0 < u) (hδ : 0 < δ) :
    ∃ R ≥ 1, ∀ (T : ℝ), 0 ≤ T → ∀ (ξ : ℝ), R ≤ |ξ| →
      Integrable (fun η => knsTruncatedPower p T ((ξ+η)^2) *
        ‖knsRealFourier (knsMomentLocalizer n u) η‖^2) ∧
      (∫ η, knsTruncatedPower p T ((ξ+η)^2) * ‖knsRealFourier (knsMomentLocalizer n u) η‖^2) ≤
        ((∫ η, ‖knsRealFourier (knsMomentLocalizer n u) η‖^2)+δ) *
          knsTruncatedPower p T (ξ^2) := by
  let M := 2*u*(1+n/(Real.pi*u))^(2*p)
  refine ⟨max 1 (M/δ),le_max_left _ _,?_⟩
  intro T hT ξ hξ
  have hξ1 : 1 ≤ |ξ| := (le_max_left _ _).trans hξ
  have hξpos : 0 < |ξ| := lt_of_lt_of_le zero_lt_one hξ1
  have hξne : ξ ≠ 0 := abs_pos.mp hξpos
  have hMξ : M/δ ≤ |ξ| := (le_max_right _ _).trans hξ
  have hMd : M/|ξ| ≤ δ := by
    apply (div_le_iff₀ hξpos).mpr
    have h := (div_le_iff₀ hδ).mp hMξ
    nlinarith
  obtain ⟨hrel,hrelbound⟩ := knsLocalizerFourier_relativeMoment_le hp hn hpn hu hξ1
  have hrel' : (∫ η, ‖knsRealFourier (knsMomentLocalizer n u) η‖^2 * (1+|η|/|ξ|)^(2*p)) ≤
      (∫ η, ‖knsRealFourier (knsMomentLocalizer n u) η‖^2)+δ := by
    dsimp only [M] at hMd
    linarith
  have hΦ : 0 ≤ knsTruncatedPower p T (ξ^2) := knsTruncatedPower_nonneg hp hT (sq_nonneg ξ)
  have hc : Continuous (knsRealFourier (knsMomentLocalizer n u)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (integrable_knsMomentLocalizer n u).ofReal
  have htr := (contDiff_one_knsTruncatedPower p T).continuous
  have hpoint (η : ℝ) : knsTruncatedPower p T ((ξ+η)^2) *
      ‖knsRealFourier (knsMomentLocalizer n u) η‖^2 ≤
      knsTruncatedPower p T (ξ^2) *
        (‖knsRealFourier (knsMomentLocalizer n u) η‖^2 * (1+|η|/|ξ|)^(2*p)) := by
    have h := mul_le_mul_of_nonneg_right (knsTruncatedPower_shift_le hp hT hξne η)
      (sq_nonneg ‖knsRealFourier (knsMomentLocalizer n u) η‖)
    nlinarith
  have hint : Integrable (fun η => knsTruncatedPower p T ((ξ+η)^2) *
      ‖knsRealFourier (knsMomentLocalizer n u) η‖^2) := by
    apply (hrel.const_mul (knsTruncatedPower p T (ξ^2))).mono'
      (show AEStronglyMeasurable _ volume from (show Continuous _ by fun_prop).aestronglyMeasurable)
    filter_upwards [] with η
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
      (knsTruncatedPower_nonneg hp hT (sq_nonneg (ξ+η))) (sq_nonneg _))]
    exact hpoint η
  refine ⟨hint,?_⟩
  calc
    _ ≤ ∫ η, knsTruncatedPower p T (ξ^2) *
        (‖knsRealFourier (knsMomentLocalizer n u) η‖^2 * (1+|η|/|ξ|)^(2*p)) :=
      integral_mono hint (hrel.const_mul _) hpoint
    _ = knsTruncatedPower p T (ξ^2) *
        (∫ η, ‖knsRealFourier (knsMomentLocalizer n u) η‖^2 * (1+|η|/|ξ|)^(2*p)) :=
      integral_const_mul _ _
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hrel' hΦ]

/-- The source's strict supercritical margin supplies the precise
square-root-sigma mass coefficient uniformly in the truncation parameter.
Only a finite Fourier moment of the actual cutoff is needed. -/
theorem exists_radius_knsTruncatedPower_fourier_shift_sqrt_mul
    {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n) (hpn : p ≤ n)
    {u σ : ℝ} (hu : 0 < u) (hσ : 1 < σ) :
    ∃ R ≥ 1, ∀ (T : ℝ), 0 ≤ T → ∀ (ξ : ℝ), R ≤ |ξ| →
      Integrable (fun η => knsTruncatedPower p T ((ξ+η)^2) *
        ‖knsRealFourier (knsMomentLocalizer n u) η‖^2) ∧
      (∫ η, knsTruncatedPower p T ((ξ+η)^2) * ‖knsRealFourier (knsMomentLocalizer n u) η‖^2) ≤
        Real.sqrt σ * (∫ η, ‖knsRealFourier (knsMomentLocalizer n u) η‖^2) *
          knsTruncatedPower p T (ξ^2) := by
  let m := ∫ η, ‖knsRealFourier (knsMomentLocalizer n u) η‖^2
  have hm : 0 < m := hu.trans_le (knsLocalizerFourier_energy hn hu).2.2
  have hsqrt : 1 < Real.sqrt σ := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤1) hσ
    simpa using h
  obtain ⟨R,hR,h⟩ := exists_radius_knsTruncatedPower_fourier_shift_le hp hn hpn hu
    (mul_pos (sub_pos.mpr hsqrt) hm)
  refine ⟨R,hR,?_⟩
  intro T hT ξ hξ
  obtain ⟨hi,hb⟩ := h T hT ξ hξ
  refine ⟨hi,?_⟩
  have he : m+(Real.sqrt σ-1)*m = Real.sqrt σ*m := by ring
  change _ ≤ (m+(Real.sqrt σ-1)*m)*knsTruncatedPower p T (ξ^2) at hb
  rw [he] at hb
  exact hb

end

end MeyerGeneralProblem
