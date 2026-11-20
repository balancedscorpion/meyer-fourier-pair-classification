module

public import MeyerGeneralProblem.Sampling.KNSStageBLocalization
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# Explicit one-row power inequality for the quantitative KNS bootstrap

The true frequency split and restoration of the physical center retain
their order dependence explicitly. The unknown is never replaced by a
Schwartz surrogate, and no moment recurrence is a premise.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter
open scoped FourierTransform ENNReal ContDiff

/-- The actual untruncated physical square moment as a nonnegative
integral, including the ordinary square mass at order zero. -/
def knsPowerEnergy (p : ℕ) (f : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (x^(2*p))*ENNReal.ofReal (‖f x‖^2)

/-- Actual finite square moments identify the nonnegative power energy
with the genuine real integral, so later absorption cannot cancel infinity. -/
theorem knsPowerEnergy_eq_ofReal_integral (p : ℕ) {f : ℝ → ℂ}
    (hp : Integrable (fun x => x^(2*p)*‖f x‖^2)) :
    knsPowerEnergy p f = ENNReal.ofReal (∫ x, x^(2*p)*‖f x‖^2) := by
  have hx (x : ℝ) : 0 ≤ x^(2*p) := by rw [pow_mul]; positivity
  rw [ofReal_integral_eq_lintegral_ofReal hp
    (Eventually.of_forall (fun x => mul_nonneg (hx x) (sq_nonneg _)))]
  simp only [knsPowerEnergy,ENNReal.ofReal_mul (hx _)]

/-- Exact reflection preserves the actual double-Fourier power energy;
no parity restriction on the unknown is involved. -/
theorem knsPowerEnergy_fourier_fourier {f : ℝ → ℂ} (hf : Continuous f)
    (hf1 : Integrable f) (hF1 : Integrable (𝓕 f)) (p : ℕ) :
    knsPowerEnergy p (𝓕 (𝓕 f)) = knsPowerEnergy p f := by
  rw [knsPowerEnergy,knsPowerEnergy,
    ← lintegral_neg_eq_self (fun x : ℝ => ENNReal.ofReal (x^(2*p))*ENNReal.ofReal (‖f x‖^2))]
  apply lintegral_congr
  intro x
  rw [kns_fourier_fourier_eq_reflection hf hf1 hF1,pow_mul (-x),neg_sq,← pow_mul]

/-- Splitting at K times the shift gives the exact power coefficient
(K plus one) divided by K, with an explicit central frequency error. -/
theorem knsStageB_shifted_power_le (p : ℕ) {K s : ℝ} (hK : 0 < K) (hs : 0 ≤ s) (x : ℝ) :
    (|x|+s)^(2*p) ≤ ((K+1)/K)^(2*p)*x^(2*p) + ((K+1)*s)^(2*p) := by
  have hb : 0 ≤ (K+1)/K := by positivity
  have hxpow : 0 ≤ x^(2*p) := by rw [pow_mul]; positivity
  by_cases hx : K*s ≤ |x|
  · have hlin : |x|+s ≤ ((K+1)/K)*|x| := by
      apply (mul_le_mul_iff_left₀ hK).mp
      have he : ((K+1)/K)*K=K+1 := by field_simp
      have hh := congrArg (fun z : ℝ => z*|x|) he
      nlinarith [hh]
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ |x|+s) hlin (2*p)
    have he : (((K+1)/K)*|x|)^(2*p)=((K+1)/K)^(2*p)*x^(2*p) := by
      rw [mul_pow,pow_mul (|x|),sq_abs,← pow_mul]
    rw [he] at hpow
    have hc : 0 ≤ ((K+1)*s)^(2*p) := by positivity
    linarith
  · have hlin : |x|+s ≤ (K+1)*s := by linarith
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ |x|+s) hlin (2*p)
    have hfirst : 0 ≤ ((K+1)/K)^(2*p)*x^(2*p) := mul_nonneg (pow_nonneg hb _) hxpow
    linarith

/-- The actual shifted square moment satisfies the frequency split,
without an integrability assumption at the higher order. -/
theorem lintegral_knsStageB_shifted_power_le (p : ℕ) {K s : ℝ} (hK : 0 < K) (hs : 0 ≤ s)
    {f : ℝ → ℂ} (hf : Continuous f) :
    (∫⁻ x, ENNReal.ofReal ((|x|+s)^(2*p))*ENNReal.ofReal (‖f x‖^2)) ≤
      ENNReal.ofReal (((K+1)/K)^(2*p))*knsPowerEnergy p f +
        ENNReal.ofReal (((K+1)*s)^(2*p))*∫⁻ x, ENNReal.ofReal (‖f x‖^2) := by
  have hxpow (x : ℝ) : 0 ≤ x^(2*p) := by rw [pow_mul]; positivity
  have hbn : 0 ≤ ((K+1)/K)^(2*p) := by positivity
  have hcn : 0 ≤ ((K+1)*s)^(2*p) := by positivity
  have hA : Measurable (fun x => ENNReal.ofReal (‖f x‖^2)) :=
    (hf.norm.pow 2).measurable.ennreal_ofReal
  have hW : Measurable (fun x : ℝ => ENNReal.ofReal (x^(2*p))*ENNReal.ofReal (‖f x‖^2)) :=
    ((continuous_id.pow _).measurable.ennreal_ofReal).mul hA
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (((K+1)/K)^(2*p)) *
        (ENNReal.ofReal (x^(2*p))*ENNReal.ofReal (‖f x‖^2)) +
        ENNReal.ofReal (((K+1)*s)^(2*p))*ENNReal.ofReal (‖f x‖^2) := by
      apply lintegral_mono
      intro x
      have h := ENNReal.ofReal_le_ofReal (knsStageB_shifted_power_le p hK hs x)
      rw [ENNReal.ofReal_add (mul_nonneg hbn (hxpow x)) hcn, ENNReal.ofReal_mul hbn] at h
      have hh := mul_le_mul_left h (ENNReal.ofReal (‖f x‖^2))
      simpa only [add_mul,mul_assoc] using hh
    _ = _ := by
      have hm : Measurable (fun x : ℝ => ENNReal.ofReal (((K+1)/K)^(2*p)) *
          (ENNReal.ofReal (x^(2*p))*ENNReal.ofReal (‖f x‖^2))) := measurable_const.mul hW
      rw [lintegral_add_left hm,lintegral_const_mul _ hW,lintegral_const_mul _ hA]
      rfl

/-- Restoring the actual physical center costs its explicit radius
power times the original square mass, not a discarded central defect. -/
theorem knsPowerEnergy_restore_center (p : ℕ) (R : ℝ) {f : ℝ → ℂ} (hf : Continuous f) :
    knsPowerEnergy p f ≤
      (∫⁻ x in {x : ℝ | R ≤ |x|}, ENNReal.ofReal (x^(2*p))*ENNReal.ofReal (‖f x‖^2)) +
        ENNReal.ofReal (R^(2*p))*∫⁻ x, ENNReal.ofReal (‖f x‖^2) := by
  let w : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (x^(2*p))*ENNReal.ofReal (‖f x‖^2)
  have hA : Measurable (fun x => ENNReal.ofReal (‖f x‖^2)) :=
    (hf.norm.pow 2).measurable.ennreal_ofReal
  have hw : Measurable w := ((continuous_id.pow _).measurable.ennreal_ofReal).mul hA
  have hs : MeasurableSet {x : ℝ | R ≤ |x|} := measurableSet_le measurable_const continuous_abs.measurable
  calc
    _ ≤ ∫⁻ x, {x : ℝ | R ≤ |x|}.indicator w x +
        ENNReal.ofReal (R^(2*p))*ENNReal.ofReal (‖f x‖^2) := by
      apply lintegral_mono
      intro x
      change w x ≤ {x : ℝ | R ≤ |x|}.indicator w x +
        ENNReal.ofReal (R^(2*p))*ENNReal.ofReal (‖f x‖^2)
      by_cases hx : R ≤ |x|
      · rw [indicator_of_mem (show x ∈ {x : ℝ | R ≤ |x|} from hx)]
        exact le_add_right le_rfl
      · rw [indicator_of_notMem (show x ∉ {x : ℝ | R ≤ |x|} from hx),zero_add]
        have hpow := pow_le_pow_left₀ (abs_nonneg x) (le_of_lt (lt_of_not_ge hx)) (2*p)
        rw [pow_mul (|x|),sq_abs,← pow_mul] at hpow
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hpow) _
    _ = _ := by
      rw [lintegral_add_left (hw.indicator hs),lintegral_indicator hs,lintegral_const_mul _ hA]

/-- The unnormalized actual one-row power estimate, before division by
the positive physical ratio. Every order dependence in both central
terms is displayed, and the geometric radius precedes the order and f. -/
theorem exists_radius_knsStageB_oneRow_scaled
    (Λ : TwoSidedCarrier) (F J : Finset ℤ) {σ : ℝ} (hσ : 0 < σ)
    (hgap : ∀ j : ℤ, j ∉ J →
      max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ (2*σ)⁻¹) :
    ∃ X0 > 0, ∀ (K : ℝ), 4 < K → ∀ (n : ℕ), 2 ≤ n →
      ∀ (u : ℝ), X0 ≤ u → ∀ (f : ℝ → ℂ), ContDiff ℝ 1 f → Integrable f → MemLp f 2 →
      (∀ j : ℤ, j ∉ F → f (Λ j) = 0) →
      ENNReal.ofReal ((σ*(K-3)/K)^(2*n))*knsPowerEnergy n f ≤
        ENNReal.ofReal (2*((K+1)/K)^(2*n))*knsPowerEnergy n (𝓕 f) +
        ENNReal.ofReal (2*((K+1)*(n/(Real.pi*u)))^(2*n) +
          (σ*(K-3)/K)^(2*n)*(K*u)^(2*n)) * ∫⁻ x, ENNReal.ofReal (‖f x‖^2) := by
  obtain ⟨X0,hX0,h⟩ := exists_radius_knsStageB_tail_power Λ F J hσ hgap
  refine ⟨X0,hX0,?_⟩
  intro K hK n hn u hu f hf hf1 hf2 hz
  have hu0 : 0 < u := hX0.trans_le hu
  have hK0 : 0 < K := by linarith
  have hs : 0 ≤ (n : ℝ)/(Real.pi*u) := by positivity
  have hfc : Continuous (𝓕 f : ℝ → ℂ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf1
  have htail := (h K hK n hn u hu f hf hf1 hz n (by omega) le_rfl).trans
    (mul_le_mul_right (lintegral_knsStageB_shifted_power_le n hK0 hs hfc) 2)
  have hcenter := mul_le_mul_right (knsPowerEnergy_restore_center n (K*u) hf.continuous)
    (ENNReal.ofReal ((σ*(K-3)/K)^(2*n)))
  rw [mul_add] at hcenter
  have hfull := hcenter.trans (add_le_add_left htail _)
  rw [lintegral_knsFourier_squareMass hf1 hf2] at hfull
  have ha : 0 ≤ (σ*(K-3)/K)^(2*n) := pow_nonneg
    (div_nonneg (mul_nonneg hσ.le (by linarith)) hK0.le) _
  have hB : 0 ≤ ((K+1)/K)^(2*n) := by positivity
  have hC : 0 ≤ ((K+1)*(n/(Real.pi*u)))^(2*n) := by positivity
  convert! hfull using 1
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2), ENNReal.ofReal_mul ha]
  norm_num
  ring

/-- The source's actual one-row power inequality with every order
dependence explicit. The extra margin is solely a numerical condition on
K and sigma; no sampling, moment, or recurrence bound is assumed. -/
theorem exists_radius_knsStageB_oneRow
    (Λ : TwoSidedCarrier) (F J : Finset ℤ) {σ : ℝ} (hσ : 0 < σ)
    (hgap : ∀ j : ℤ, j ∉ J →
      max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ (2*σ)⁻¹) :
    ∃ X0 > 0, ∀ (K : ℝ), 4 < K → K ≤ σ*(K-3) → ∀ (n : ℕ), 2 ≤ n →
      ∀ (u : ℝ), X0 ≤ u → ∀ (f : ℝ → ℂ), ContDiff ℝ 1 f → Integrable f → MemLp f 2 →
      (∀ j : ℤ, j ∉ F → f (Λ j) = 0) →
      knsPowerEnergy n f ≤
        ENNReal.ofReal (2*((K+1)/(σ*(K-3)))^(2*n))*knsPowerEnergy n (𝓕 f) +
        ENNReal.ofReal (K^(2*n)*u^(2*n)+2*(K+1)^(2*n)*(n/u)^(2*n)) *
          ∫⁻ x, ENNReal.ofReal (‖f x‖^2) := by
  obtain ⟨X0,hX0,h⟩ := exists_radius_knsStageB_oneRow_scaled Λ F J hσ hgap
  refine ⟨X0,hX0,?_⟩
  intro K hK hmargin n hn u hu f hf hf1 hf2 hz
  have hu0 : 0 < u := hX0.trans_le hu
  have hK0 : 0 < K := by linarith
  have hK3 : 0 < K-3 := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  let a := σ*(K-3)/K
  let r := (K+1)/(σ*(K-3))
  let b := (K+1)/K
  let s := (n : ℝ)/(Real.pi*u)
  let t := (n : ℝ)/u
  let E := K^(2*n)*u^(2*n)+2*(K+1)^(2*n)*t^(2*n)
  have ha1 : 1 ≤ a := (le_div_iff₀ hK0).mpr (by simpa using hmargin)
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hs : 0 ≤ s := by dsimp only [s]; positivity
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hst : s ≤ t := by
    apply (div_le_div_iff₀ (mul_pos Real.pi_pos hu0) hu0).mpr
    have hpi := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ Real.pi by linarith [Real.pi_gt_three])
      (mul_nonneg hn0 hu0.le)
    nlinarith
  have har : a*r=b := by
    dsimp only [a,r,b]
    field_simp
  have haPow : 0 < a^(2*n) := pow_pos ha _
  have hcoef : 2*b^(2*n)=a^(2*n)*(2*r^(2*n)) := by rw [← har,mul_pow]; ring
  have hshift : (K+1)*s ≤ a*(K+1)*t := by
    have h1 := mul_le_mul_of_nonneg_left hst (by linarith : 0 ≤ K+1)
    have h2 := mul_le_mul_of_nonneg_right ha1 (mul_nonneg (by linarith : 0 ≤ K+1) ht)
    nlinarith
  have hpow := pow_le_pow_left₀ (mul_nonneg (by linarith : 0 ≤ K+1) hs) hshift (2*n)
  simp only [mul_pow] at hpow
  have herr : 2*((K+1)*s)^(2*n)+a^(2*n)*(K*u)^(2*n) ≤ a^(2*n)*E := by
    dsimp only [E]
    simp only [mul_pow]
    nlinarith
  have hscaled := h K hK n hn u hu f hf hf1 hf2 hz
  change ENNReal.ofReal (a^(2*n))*knsPowerEnergy n f ≤
    ENNReal.ofReal (2*b^(2*n))*knsPowerEnergy n (𝓕 f) +
    ENNReal.ofReal (2*((K+1)*s)^(2*n)+a^(2*n)*(K*u)^(2*n))*
      (∫⁻ x, ENNReal.ofReal (‖f x‖^2)) at hscaled
  change knsPowerEnergy n f ≤ ENNReal.ofReal (2*r^(2*n))*knsPowerEnergy n (𝓕 f) +
    ENNReal.ofReal E*(∫⁻ x, ENNReal.ofReal (‖f x‖^2))
  apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr haPow).ne' ENNReal.ofReal_ne_top).mp
  calc
    _ ≤ _ := hscaled
    _ ≤ ENNReal.ofReal (a^(2*n)*(2*r^(2*n)))*knsPowerEnergy n (𝓕 f) +
        ENNReal.ofReal (a^(2*n)*E)*(∫⁻ x, ENNReal.ofReal (‖f x‖^2)) := by
      rw [hcoef]
      exact add_le_add_right (mul_le_mul_left (ENNReal.ofReal_le_ofReal herr) _) _
    _ = _ := by
      rw [ENNReal.ofReal_mul haPow.le,ENNReal.ofReal_mul haPow.le]
      ring

end

end MeyerGeneralProblem
