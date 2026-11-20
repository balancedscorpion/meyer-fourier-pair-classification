module

public import MeyerGeneralProblem.Sampling.KNSStageAPhysicalBounds

@[expose] public section

/-!
# Integrated frequency contraction for the initial KNS bootstrap

The actual finite-order localizer yields a square-root-sigma coefficient
outside a fixed frequency center. Integrating the true shifted Fourier
energy retains that coefficient and restores a T-independent central term.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter
open scoped FourierTransform ENNReal ContDiff

/-- The actual tangent-truncated weighted square energy. Nonnegative
integration is used until finiteness follows from the second moment. -/
def knsTruncatedEnergy (p : ℕ) (T : ℝ) (f : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (knsTruncatedPower p T (x^2)) * ENNReal.ofReal (‖f x‖^2)

/-- Finite physical second moment implies that each actual truncation
is finite; no untruncated higher moment occurs in the hypothesis. -/
theorem knsTruncatedEnergy_eq_ofReal_integral {p : ℕ} (hp : 1 ≤ p)
    {T : ℝ} (hT : 0 ≤ T) {f : ℝ → ℂ} (hf : Continuous f)
    (hsecond : Integrable (fun x => x^2*‖f x‖^2)) :
    knsTruncatedEnergy p T f =
      ENNReal.ofReal (∫ x, knsTruncatedPower p T (x^2)*‖f x‖^2) := by
  have hint := integrable_knsTruncatedPower_weight hp hT (fun _ => sq_nonneg _)
    (hf.norm.pow 2).aestronglyMeasurable hsecond
  rw [ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall (fun x => mul_nonneg
      (knsTruncatedPower_nonneg hp hT (sq_nonneg x)) (sq_nonneg _)))]
  simp only [knsTruncatedEnergy,
    ENNReal.ofReal_mul (knsTruncatedPower_nonneg hp hT (sq_nonneg _))]

/-- Exact finite-truncation finiteness from the actual second moment. -/
theorem knsTruncatedEnergy_ne_top {p : ℕ} (hp : 1 ≤ p)
    {T : ℝ} (hT : 0 ≤ T) {f : ℝ → ℂ} (hf : Continuous f)
    (hsecond : Integrable (fun x => x^2*‖f x‖^2)) :
    knsTruncatedEnergy p T f ≠ ⊤ := by
  rw [knsTruncatedEnergy_eq_ofReal_integral hp hT hf hsecond]
  exact ENNReal.ofReal_ne_top

/-- The genuine shifted cutoff integral has a global bound with the
precise square-root-sigma tail coefficient and a T-independent center. -/
theorem exists_constant_knsTruncatedPower_fourier_shift_global
    {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n) (hpn : p ≤ n)
    {u σ : ℝ} (hu : 0 < u) (hσ : 1 < σ) :
    ∃ C > 0, ∀ (T : ℝ), 0 ≤ T → ∀ (ξ : ℝ),
      (∫ η, knsTruncatedPower p T ((ξ+η)^2) *
          ‖knsRealFourier (knsMomentLocalizer n u) η‖^2) ≤
        Real.sqrt σ * (∫ y, |knsMomentLocalizer n u y|^2) *
          knsTruncatedPower p T (ξ^2) + C := by
  obtain ⟨R,hR,h⟩ := exists_radius_knsTruncatedPower_fourier_shift_sqrt_mul hp hn hpn hu hσ
  let C := 2*u*(R+n/(Real.pi*u))^(2*p)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hscale : 0 < n/(Real.pi*u) := div_pos hn0 (mul_pos Real.pi_pos hu)
  have hC : 0 < C := by dsimp [C]; positivity
  have hm : 0 ≤ ∫ y, |knsMomentLocalizer n u y|^2 := integral_nonneg (fun _ => sq_nonneg _)
  refine ⟨C,hC,?_⟩
  intro T hT ξ
  have htail0 : 0 ≤ Real.sqrt σ * (∫ y, |knsMomentLocalizer n u y|^2) *
      knsTruncatedPower p T (ξ^2) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hm) (knsTruncatedPower_nonneg hp hT (sq_nonneg ξ))
  by_cases hξ : R ≤ |ξ|
  · have hb := (h T hT ξ hξ).2
    rw [(knsLocalizerFourier_energy hn hu).2.1] at hb
    linarith
  · have hξR : |ξ| ≤ R := le_of_lt (lt_of_not_ge hξ)
    have hb := (knsTruncatedPower_fourier_shift_bound hp hn hpn hu hT ξ).2
    have hpow := pow_le_pow_left₀ (show 0 ≤ |ξ|+n/(Real.pi*u) by positivity)
      (show |ξ|+n/(Real.pi*u) ≤ R+n/(Real.pi*u) by linarith) (2*p)
    have hc := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 2*u)
    dsimp only [C] at hC ⊢
    linarith

/-- Integrating the true frequency-shift estimate against the actual
Fourier square gives its exact square-root-sigma mass coefficient.
All constants precede T and f, and weighted energy may still be infinite. -/
theorem exists_constant_knsStageA_fourier_energy
    {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n) (hpn : p ≤ n)
    {u σ : ℝ} (hu : 0 < u) (hσ : 1 < σ) :
    ∃ C > 0, ∀ (T : ℝ), 0 ≤ T → ∀ (f : ℝ → ℂ), Integrable f →
      (∫⁻ ξ, ∫⁻ η, ENNReal.ofReal (knsTruncatedPower p T ((ξ+η)^2)) *
        (ENNReal.ofReal (‖𝓕 f ξ‖^2) *
          ENNReal.ofReal (‖knsRealFourier (knsMomentLocalizer n u) η‖^2))) ≤
      ENNReal.ofReal (Real.sqrt σ * (∫ y, |knsMomentLocalizer n u y|^2)) *
        knsTruncatedEnergy p T (𝓕 f) +
      ENNReal.ofReal C * ∫⁻ ξ, ENNReal.ofReal (‖𝓕 f ξ‖^2) := by
  obtain ⟨C,hC,h⟩ := exists_constant_knsTruncatedPower_fourier_shift_global hp hn hpn hu hσ
  refine ⟨C,hC,?_⟩
  intro T hT f hf
  let A : ℝ → ℝ≥0∞ := fun ξ => ENNReal.ofReal (‖𝓕 f ξ‖^2)
  let W : ℝ → ℝ≥0∞ := fun ξ => ENNReal.ofReal (knsTruncatedPower p T (ξ^2))
  let c := Real.sqrt σ * (∫ y, |knsMomentLocalizer n u y|^2)
  have hc : 0 ≤ c := mul_nonneg (Real.sqrt_nonneg _) (integral_nonneg (fun _ => sq_nonneg _))
  have hA : Measurable A := ((VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf).norm.pow 2).measurable.ennreal_ofReal
  have hW : Measurable W :=
    ((contDiff_one_knsTruncatedPower p T).continuous.comp (continuous_id.pow 2)).measurable.ennreal_ofReal
  have hb (ξ : ℝ) : (∫⁻ η, ENNReal.ofReal (knsTruncatedPower p T ((ξ+η)^2)) *
      (A ξ * ENNReal.ofReal (‖knsRealFourier (knsMomentLocalizer n u) η‖^2))) ≤
      ENNReal.ofReal c * (W ξ * A ξ) + ENNReal.ofReal C * A ξ := by
    have hi := (knsTruncatedPower_fourier_shift_bound hp hn hpn hu hT ξ).1
    have he := ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall (fun η => mul_nonneg
        (knsTruncatedPower_nonneg hp hT (sq_nonneg (ξ+η))) (sq_nonneg _)))
    have hb := ENNReal.ofReal_le_ofReal (h T hT ξ)
    rw [he, ENNReal.ofReal_add (mul_nonneg hc (knsTruncatedPower_nonneg hp hT (sq_nonneg ξ))) hC.le,
      ENNReal.ofReal_mul hc] at hb
    simp only [ENNReal.ofReal_mul (knsTruncatedPower_nonneg hp hT (sq_nonneg _))] at hb
    calc
      _ = A ξ * (∫⁻ η, ENNReal.ofReal (knsTruncatedPower p T ((ξ+η)^2)) *
          ENNReal.ofReal (‖knsRealFourier (knsMomentLocalizer n u) η‖^2)) := by
        rw [← lintegral_const_mul' (A ξ) _ ENNReal.ofReal_ne_top]
        apply lintegral_congr
        intro η
        ring
      _ ≤ A ξ * (ENNReal.ofReal c * W ξ + ENNReal.ofReal C) := mul_le_mul_right hb _
      _ = _ := by ring
  calc
    _ ≤ ∫⁻ ξ, ENNReal.ofReal c * (W ξ * A ξ) + ENNReal.ofReal C * A ξ := lintegral_mono hb
    _ = _ := by
      have hWA : Measurable (fun ξ => W ξ * A ξ) := hW.mul hA
      have hcWA : Measurable (fun ξ => ENNReal.ofReal c * (W ξ * A ξ)) := measurable_const.mul hWA
      rw [lintegral_add_left hcWA, lintegral_const_mul _ hWA, lintegral_const_mul _ hA]
      rfl

/-- Actual L1 and L2 Fourier Plancherel preserves the nonnegative square
mass, with no Schwartz hypothesis on the function. -/
theorem lintegral_knsFourier_squareMass {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) :
    (∫⁻ ξ, ENNReal.ofReal (‖𝓕 f ξ‖^2)) = ∫⁻ x, ENNReal.ofReal (‖f x‖^2) := by
  obtain ⟨hF,hN⟩ := memLp_fourier_norm_eq_of_integrable hf1 hf2
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_norm_sq_of_memLp_complex hF)
      (Eventually.of_forall (fun _ => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal (integrable_norm_sq_of_memLp_complex hf2)
      (Eventually.of_forall (fun _ => sq_nonneg _)),
    integral_norm_sq_eq_toLp_norm_sq_complex hF, integral_norm_sq_eq_toLp_norm_sq_complex hf2, hN]

/-- The actual one-row KNS inequality for finite truncations, after
dividing by the genuine positive localizer mass. Its constants precede
the unknown and T, and only the two second moments are required. -/
theorem exists_constant_knsStageA_oneRow
    (Λ : TwoSidedCarrier) (F J : Finset ℤ) {σ : ℝ} (hσ : 1 < σ)
    (hgap : ∀ j : ℤ, j ∉ J →
      max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ (2*σ)⁻¹)
    {p : ℕ} (hp : 1 ≤ p) :
    ∃ C > 0, ∀ (f : ℝ → ℂ), ContDiff ℝ 1 f → Integrable f → MemLp f 2 →
      Integrable (fun x => x^2*‖f x‖^2) → Integrable (fun ξ => ξ^2*‖𝓕 f ξ‖^2) →
      (∀ j : ℤ, j ∉ F → f (Λ j) = 0) → ∀ T : ℝ, 0 ≤ T →
      σ * (∫ x, knsTruncatedPower p T (x^2)*‖f x‖^2) ≤
        Real.sqrt σ * (∫ ξ, knsTruncatedPower p T (ξ^2)*‖𝓕 f ξ‖^2) +
          C * ∫ x, ‖f x‖^2 := by
  let n := max p 2
  have hn : 2 ≤ n := le_max_right _ _
  have hpn : p ≤ n := le_max_left _ _
  let m := ∫ y, |knsMomentLocalizer n 1 y|^2
  have hm : 0 < m := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1)
    (integral_knsMomentLocalizer_sq_ge (by omega : 1 ≤ n) (by norm_num))
  have hσ0 : 0 ≤ σ := by linarith
  obtain ⟨R,hR,hphysical⟩ := exists_radius_knsStageA_physical_fourier Λ F J hσ hgap (by norm_num : (0 : ℝ)<1)
  obtain ⟨C,hC,hfrequency⟩ := exists_constant_knsStageA_fourier_energy hp (by omega : 1 ≤ n)
    hpn (by norm_num : (0 : ℝ)<1) hσ
  let K := (C+σ*m*R^(2*p))/m
  have hK : 0 < K := by dsimp only [K]; positivity
  have hKm : K*m = C+σ*m*R^(2*p) := by dsimp only [K]; field_simp
  refine ⟨K,hK,?_⟩
  intro f hf hf1 hf2 hx2 hξ2 hz T hT
  have hfc : Continuous (𝓕 f : ℝ → ℂ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf1
  have hb := (hphysical n hn f hf hf1 hz p hp T hT).trans
    (add_le_add_left (hfrequency T hT f hf1) _)
  change ENNReal.ofReal σ * ENNReal.ofReal m * knsTruncatedEnergy p T f ≤
    (ENNReal.ofReal (Real.sqrt σ*m)*knsTruncatedEnergy p T (𝓕 f) +
      ENNReal.ofReal C * (∫⁻ ξ, ENNReal.ofReal (‖𝓕 f ξ‖^2))) +
    ENNReal.ofReal σ * ENNReal.ofReal m * ENNReal.ofReal (R^(2*p)) *
      (∫⁻ x, ENNReal.ofReal (‖f x‖^2)) at hb
  rw [lintegral_knsFourier_squareMass hf1 hf2,
    knsTruncatedEnergy_eq_ofReal_integral hp hT hf.continuous hx2,
    knsTruncatedEnergy_eq_ofReal_integral hp hT hfc hξ2,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_norm_sq_of_memLp_complex hf2)
      (Eventually.of_forall (fun _ => sq_nonneg _))] at hb
  let X := ∫ x, knsTruncatedPower p T (x^2)*‖f x‖^2
  let Y := ∫ ξ, knsTruncatedPower p T (ξ^2)*‖𝓕 f ξ‖^2
  let M := ∫ x, ‖f x‖^2
  have hX : 0 ≤ X := integral_nonneg (fun x =>
    mul_nonneg (knsTruncatedPower_nonneg hp hT (sq_nonneg x)) (sq_nonneg _))
  have hY : 0 ≤ Y := integral_nonneg (fun x =>
    mul_nonneg (knsTruncatedPower_nonneg hp hT (sq_nonneg x)) (sq_nonneg _))
  have hM : 0 ≤ M := integral_nonneg (fun _ => sq_nonneg _)
  have heL : ENNReal.ofReal σ * ENNReal.ofReal m * ENNReal.ofReal X = ENNReal.ofReal (σ*m*X) := by
    rw [ENNReal.ofReal_mul (mul_nonneg hσ0 hm.le), ENNReal.ofReal_mul hσ0]
  have heR : (ENNReal.ofReal (Real.sqrt σ*m)*ENNReal.ofReal Y + ENNReal.ofReal C*ENNReal.ofReal M) +
      ENNReal.ofReal σ * ENNReal.ofReal m * ENNReal.ofReal (R^(2*p))*ENNReal.ofReal M =
      ENNReal.ofReal (Real.sqrt σ*m*Y + C*M + σ*m*R^(2*p)*M) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
    simp only [ENNReal.ofReal_mul (mul_nonneg (Real.sqrt_nonneg σ) hm.le),
      ENNReal.ofReal_mul hC.le, ENNReal.ofReal_mul (mul_nonneg hσ0 hm.le),
      ENNReal.ofReal_mul hσ0, ENNReal.ofReal_mul (by positivity : 0 ≤ σ*m*R^(2*p))]
  rw [heL,heR] at hb
  have hreal : σ*m*X ≤ Real.sqrt σ*m*Y + C*M + σ*m*R^(2*p)*M :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb
  change σ*X ≤ Real.sqrt σ*Y+K*M
  apply (mul_le_mul_iff_left₀ hm).mp
  calc
    (σ*X)*m = σ*m*X := by ring
    _ ≤ Real.sqrt σ*m*Y+C*M+σ*m*R^(2*p)*M := hreal
    _ = (Real.sqrt σ*Y+K*M)*m := by
      have hh := congrArg (fun z : ℝ => z*M) hKm
      nlinarith [hh]

end

end MeyerGeneralProblem
