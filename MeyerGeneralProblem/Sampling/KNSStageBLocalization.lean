module

public import MeyerGeneralProblem.Sampling.KNSStageAMoments

@[expose] public section

/-!
# Genuine power localization for the quantitative KNS bootstrap

Passing the actual C1 truncated Poincare inequality to a power weight
avoids presuming arbitrarily high regularity of the box convolution.
All high weighted integrals are nonnegative integrals at this stage.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter
open scoped FourierTransform ENNReal ContDiff Topology

/-- The true localized power Poincare inequality follows by a scalar
limit of the proved tangent truncations. It requires only C1 of the
unknown and n at least two, not a Schwartz or high product-derivative input. -/
theorem exists_radius_knsStageB_localized_power
    (Λ : TwoSidedCarrier) (F J : Finset ℤ) {σ : ℝ} (hσ : 0 < σ)
    (hgap : ∀ j : ℤ, j ∉ J →
      max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ (2*σ)⁻¹) :
    ∃ X0 > 0, ∀ (n : ℕ), 2 ≤ n → ∀ (u : ℝ), 0 < u → ∀ (v : ℝ),
      X0 ≤ |v|-3*u/2 → ∀ (f : ℝ → ℂ), ContDiff ℝ 1 f →
      (∀ j : ℤ, j ∉ F → f (Λ j) = 0) → ∀ (p : ℕ), 1 ≤ p →
      ENNReal.ofReal ((σ*(|v|-3*u/2))^(2*p)) *
          (∫⁻ x, ENNReal.ofReal (‖knsLocalizedFunction n u v f x‖^2)) ≤
        ∫⁻ ξ, ENNReal.ofReal (ξ^(2*p)) *
          ENNReal.ofReal (‖knsLocalizedFourierSlice n u f ξ v‖^2) := by
  obtain ⟨X0,hX0,h⟩ := exists_radius_truncatedPower_poincare_of_finite_exceptions Λ F J hσ hgap
  refine ⟨X0,hX0,?_⟩
  intro n hn u hu v hv f hf hz p hp
  let N := ∫ x, ‖knsLocalizedFunction n u v f x‖^2
  have hN : 0 ≤ N := integral_nonneg (fun _ => sq_nonneg _)
  have hnorm := integrable_norm_sq_of_memLp_complex (memLp_knsLocalizedFunction_and_deriv hn hu v hf).1
  have hb (T : ℝ) (hT : 0 ≤ T) :
      ENNReal.ofReal (knsTruncatedPower p T ((σ*(|v|-3*u/2))^2)*N) ≤
        ∫⁻ ξ, ENNReal.ofReal (ξ^(2*p))*ENNReal.ofReal (‖knsLocalizedFourierSlice n u f ξ v‖^2) := by
    have hP := ENNReal.ofReal_le_ofReal (h n hn u hu v hv f hf hz p hp T hT)
    rw [ofReal_integral_eq_lintegral_ofReal
      (integrable_knsTruncatedPower_localizedFourier hp hn hT hu v hf)
      (Eventually.of_forall (fun ξ => mul_nonneg
        (knsTruncatedPower_nonneg hp hT (sq_nonneg ξ)) (sq_nonneg _)))] at hP
    apply hP.trans
    apply lintegral_mono
    intro ξ
    change ENNReal.ofReal (knsTruncatedPower p T (ξ^2)*
      ‖knsLocalizedFourierSlice n u f ξ v‖^2) ≤ _
    rw [ENNReal.ofReal_mul (knsTruncatedPower_nonneg hp hT (sq_nonneg ξ))]
    have hpow := knsTruncatedPower_le_pow hp hT (sq_nonneg ξ)
    rw [← pow_mul] at hpow
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hpow) _
  have hlim : Tendsto (fun T : ℝ => ENNReal.ofReal
      (knsTruncatedPower p T ((σ*(|v|-3*u/2))^2)*N)) atTop
      (𝓝 (ENNReal.ofReal ((σ*(|v|-3*u/2))^(2*p)*N))) := by
    convert! ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((tendsto_knsTruncatedPower p ((σ*(|v|-3*u/2))^2)).mul_const N) using 1
    simp only [pow_mul]
  have hfinal := le_of_tendsto hlim ((eventually_ge_atTop (0 : ℝ)).mono fun T hT => hb T hT)
  have hpow0 : 0 ≤ (σ*(|v|-3*u/2))^(2*p) := by rw [pow_mul]; positivity
  rw [ENNReal.ofReal_mul hpow0, ofReal_integral_eq_lintegral_ofReal hnorm
    (Eventually.of_forall (fun _ => sq_nonneg _))] at hfinal
  exact hfinal

/-- The K-minus-three support loss is exact: exterior translations
and the actual radius 3u/2 imply the source's uniform physical ratio. -/
theorem knsStageB_support_ratio {K u σ v x : ℝ} (hK : 3 < K) (hσ : 0 ≤ σ)
    (hv : (K-3/2)*u ≤ |v|) (hx : |x-v| ≤ 3*u/2) :
    (σ*(K-3)/K)*|x| ≤ σ*(|v|-3*u/2) := by
  have hK0 : 0 < K := by linarith
  have htri : |x| ≤ |v|+3*u/2 := by
    have h := abs_add_le (x-v) v
    rw [sub_add_cancel] at h
    linarith
  have hb : (K-3)*|x| ≤ K*(|v|-3*u/2) := by
    have hmul := mul_le_mul_of_nonneg_left htri (by linarith : 0 ≤ K-3)
    nlinarith
  apply (mul_le_mul_iff_left₀ hK0).mp
  have h := mul_le_mul_of_nonneg_left hb hσ
  have he : (σ*(K-3)/K)*K=σ*(K-3) := by field_simp
  have he' := congrArg (fun z : ℝ => z*|x|) he
  nlinarith [he']

/-- Sinc absorption bounds the true global localized Fourier power
energy by the shifted pure Fourier moment with the exact factor 2u.
No higher derivative regularity of f times the finite localizer is used. -/
theorem lintegral_knsStageB_fourier_power_le {p n : ℕ} (hn : 1 ≤ n) (hpn : p ≤ n)
    {u : ℝ} (hu : 0 < u) {f : ℝ → ℂ} (hf1 : Integrable f) :
    (∫⁻ v, ∫⁻ ξ, ENNReal.ofReal (ξ^(2*p))*
        ENNReal.ofReal (‖knsLocalizedFourierSlice n u f ξ v‖^2)) ≤
      ENNReal.ofReal (2*u) * ∫⁻ ξ, ENNReal.ofReal ((|ξ|+n/(Real.pi*u))^(2*p))*
        ENNReal.ofReal (‖𝓕 f ξ‖^2) := by
  have hW : Measurable (fun ξ : ℝ => ENNReal.ofReal (ξ^(2*p))) :=
    (continuous_id.pow _).measurable.ennreal_ofReal
  rw [lintegral_weighted_knsLocalizedFourierEnergy hn hu hf1 _ hW]
  let A : ℝ → ℝ≥0∞ := fun ξ => ENNReal.ofReal (‖𝓕 f ξ‖^2)
  let B : ℝ → ℝ≥0∞ := fun η => ENNReal.ofReal (‖knsRealFourier (knsBox u) η‖^2)
  let W : ℝ → ℝ≥0∞ := fun ξ => ENNReal.ofReal ((|ξ|+n/(Real.pi*u))^(2*p))
  have hmass : (∫⁻ η, B η) = ENNReal.ofReal (2*u) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (knsBoxFourier_energy hu.le).1
      (Eventually.of_forall (fun _ => sq_nonneg _)), (knsBoxFourier_energy hu.le).2]
  calc
    _ ≤ ∫⁻ ξ, ∫⁻ η, W ξ * (A ξ * B η) := by
      apply lintegral_mono
      intro ξ
      apply lintegral_mono
      intro η
      have hpow : (ξ+η)^(2*p) ≤ (|ξ|+|η|)^(2*p) := by
        have h := pow_le_pow_left₀ (abs_nonneg (ξ+η)) (abs_add_le ξ η) (2*p)
        simpa only [pow_mul,sq_abs] using h
      have h := (mul_le_mul_of_nonneg_right hpow (sq_nonneg _)).trans
        (knsLocalizerFourier_weighted_pointwise_le hn hpn hu ξ η)
      have hpow0 : 0 ≤ (ξ+η)^(2*p) := by rw [pow_mul]; positivity
      have hreal := ENNReal.ofReal_le_ofReal h
      rw [ENNReal.ofReal_mul hpow0, ENNReal.ofReal_mul (by positivity)] at hreal
      have hh := mul_le_mul_right hreal (A ξ)
      convert! hh using 1 <;> ring
    _ = _ := by
      have hBB (ξ : ℝ) : (∫⁻ η, W ξ * (A ξ * B η)) = W ξ*A ξ*ENNReal.ofReal (2*u) := by
        simp_rw [← mul_assoc]
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),hmass]
      simp_rw [hBB]
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,mul_comm]

/-- Integrating the true power Poincare inequality gives the physical
exterior estimate with precisely sigma times (K minus three) divided by K.
The radius depends only on the original zero and gap exceptions. -/
theorem exists_radius_knsStageB_physical_power
    (Λ : TwoSidedCarrier) (F J : Finset ℤ) {σ : ℝ} (hσ : 0 < σ)
    (hgap : ∀ j : ℤ, j ∉ J →
      max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ (2*σ)⁻¹) :
    ∃ X0 > 0, ∀ (K : ℝ), 4 < K → ∀ (n : ℕ), 2 ≤ n →
      ∀ (u : ℝ), X0 ≤ u → ∀ (f : ℝ → ℂ), ContDiff ℝ 1 f →
      (∀ j : ℤ, j ∉ F → f (Λ j) = 0) → ∀ (p : ℕ), 1 ≤ p →
      ENNReal.ofReal ((σ*(K-3)/K)^(2*p)) *
          ENNReal.ofReal (∫ y, |knsMomentLocalizer n u y|^2) *
          (∫⁻ x in {x : ℝ | K*u ≤ |x|}, ENNReal.ofReal (x^(2*p))*ENNReal.ofReal (‖f x‖^2)) ≤
        ∫⁻ v, ∫⁻ ξ, ENNReal.ofReal (ξ^(2*p))*
          ENNReal.ofReal (‖knsLocalizedFourierSlice n u f ξ v‖^2) := by
  obtain ⟨X0,hX0,hP⟩ := exists_radius_knsStageB_localized_power Λ F J hσ hgap
  refine ⟨X0,hX0,?_⟩
  intro K hK n hn u hu f hf hz p hp
  have hu0 : 0 < u := hX0.trans_le hu
  let V := (K-3/2)*u
  let a := σ*(K-3)/K
  have ha : 0 ≤ a := div_nonneg (mul_nonneg hσ.le (by linarith)) (by linarith)
  let W : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (x^(2*p))
  have hW : Measurable W := (continuous_id.pow _).measurable.ennreal_ofReal
  have hsum : V+3*u/2=K*u := by dsimp only [V]; ring
  have hbase := lintegral_knsLocalizedFunction_exterior_lower (by omega : 1 ≤ n) hu0 V hf.continuous W hW
  rw [hsum] at hbase
  have hbase' := mul_le_mul_right hbase (ENNReal.ofReal (a^(2*p)))
  rw [← mul_assoc] at hbase'
  apply hbase'.trans
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ∫⁻ v in {v : ℝ | V ≤ |v|}, ∫⁻ ξ, W ξ *
        ENNReal.ofReal (‖knsLocalizedFourierSlice n u f ξ v‖^2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_le measurable_const continuous_abs.measurable)] with v hv
      have hv0 : X0 ≤ |v|-3*u/2 := by
        change (K-3/2)*u ≤ |v| at hv
        nlinarith
      have hinner : 0 ≤ σ*(|v|-3*u/2) := mul_nonneg hσ.le (by linarith)
      apply le_trans _ (hP n hn u hu0 v hv0 f hf hz p hp)
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono
      intro x
      by_cases hF : knsMomentLocalizer n u (x-v) = 0
      · simp [knsLocalizedFunction,hF]
      have hdist := abs_le.mpr (support_knsMomentLocalizer_subset (by omega : 1 ≤ n) u hF)
      have hr := knsStageB_support_ratio (by linarith : 3 < K) hσ.le hv hdist
      have hpow := pow_le_pow_left₀ (mul_nonneg ha (abs_nonneg x)) hr (2*p)
      have he : (a*|x|)^(2*p)=a^(2*p)*x^(2*p) := by
        rw [mul_pow,pow_mul (|x|),sq_abs,← pow_mul]
      change (a*|x|)^(2*p) ≤ (σ*(|v|-3*u/2))^(2*p) at hpow
      rw [he] at hpow
      have hh := ENNReal.ofReal_le_ofReal hpow
      rw [ENNReal.ofReal_mul (pow_nonneg ha _)] at hh
      have hhh := mul_le_mul_left hh (ENNReal.ofReal (‖knsLocalizedFunction n u v f x‖^2))
      simpa only [W,mul_assoc] using hhh
    _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl

/-- The actual exterior power moment obeys the quantitative source
estimate before splitting frequencies. The coefficient two comes from
the proved box mass 2u divided by the true localizer mass at least u.
No higher-moment, high-regularity, or recurrence certificate is an input. -/
theorem exists_radius_knsStageB_tail_power
    (Λ : TwoSidedCarrier) (F J : Finset ℤ) {σ : ℝ} (hσ : 0 < σ)
    (hgap : ∀ j : ℤ, j ∉ J →
      max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ (2*σ)⁻¹) :
    ∃ X0 > 0, ∀ (K : ℝ), 4 < K → ∀ (n : ℕ), 2 ≤ n →
      ∀ (u : ℝ), X0 ≤ u → ∀ (f : ℝ → ℂ), ContDiff ℝ 1 f → Integrable f →
      (∀ j : ℤ, j ∉ F → f (Λ j) = 0) → ∀ (p : ℕ), 1 ≤ p → p ≤ n →
      ENNReal.ofReal ((σ*(K-3)/K)^(2*p)) *
          (∫⁻ x in {x : ℝ | K*u ≤ |x|}, ENNReal.ofReal (x^(2*p))*ENNReal.ofReal (‖f x‖^2)) ≤
        2 * ∫⁻ ξ, ENNReal.ofReal ((|ξ|+n/(Real.pi*u))^(2*p))*ENNReal.ofReal (‖𝓕 f ξ‖^2) := by
  obtain ⟨X0,hX0,hP⟩ := exists_radius_knsStageB_physical_power Λ F J hσ hgap
  refine ⟨X0,hX0,?_⟩
  intro K hK n hn u hu f hf hf1 hz p hp hpn
  have hu0 : 0 < u := hX0.trans_le hu
  have h := (hP K hK n hn u hu f hf hz p hp).trans
    (lintegral_knsStageB_fourier_power_le (by omega : 1 ≤ n) hpn hu0 hf1)
  have hm : ENNReal.ofReal u ≤ ENNReal.ofReal (∫ y, |knsMomentLocalizer n u y|^2) :=
    ENNReal.ofReal_le_ofReal (integral_knsMomentLocalizer_sq_ge (by omega : 1 ≤ n) hu0)
  have hsmall := mul_le_mul_left (mul_le_mul_right hm
    (ENNReal.ofReal ((σ*(K-3)/K)^(2*p))))
    (∫⁻ x in {x : ℝ | K*u ≤ |x|}, ENNReal.ofReal (x^(2*p))*ENNReal.ofReal (‖f x‖^2))
  have ht := hsmall.trans h
  apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hu0).ne' ENNReal.ofReal_ne_top).mp
  calc
    _ = ENNReal.ofReal ((σ*(K-3)/K)^(2*p))*ENNReal.ofReal u*
        (∫⁻ x in {x : ℝ | K*u ≤ |x|}, ENNReal.ofReal (x^(2*p))*ENNReal.ofReal (‖f x‖^2)) := by ring
    _ ≤ _ := ht
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]; norm_num; ring

end

end MeyerGeneralProblem
