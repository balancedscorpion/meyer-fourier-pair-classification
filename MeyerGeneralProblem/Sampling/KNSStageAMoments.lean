module

public import MeyerGeneralProblem.Sampling.KNSStageAFrequencyBounds
public import Mathlib.Analysis.Fourier.Inversion

@[expose] public section

/-!
# All square moments from the initial KNS bootstrap

The two rows concern an actual classical Fourier pair. Fourier inversion
proves the reflection identity; both second moments make the truncations
finite before absorption. Fatou then supplies the higher moments.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter
open scoped FourierTransform ENNReal ContDiff Topology

/-- Actual double classical Fourier transformation is reflection for
continuous L1 data whose Fourier transform is L1. -/
theorem kns_fourier_fourier_eq_reflection {f : ℝ → ℂ} (hf : Continuous f)
    (hf1 : Integrable f) (hF1 : Integrable (𝓕 f)) (x : ℝ) :
    𝓕 (𝓕 f) x = f (-x) := by
  have h := hf1.fourierInv_fourier_eq hF1 (hf.continuousAt (x := -x))
  rw [Real.fourierInv_eq_fourier_neg, neg_neg] at h
  exact h

/-- The actual reflected second Fourier transform has exactly the
original truncated even-weight energy, with no parity assumption on f. -/
theorem integral_knsTruncatedPower_fourier_fourier {f : ℝ → ℂ}
    (hf : Continuous f) (hf1 : Integrable f) (hF1 : Integrable (𝓕 f)) (p : ℕ) (T : ℝ) :
    (∫ x, knsTruncatedPower p T (x^2)*‖𝓕 (𝓕 f) x‖^2) =
      ∫ x, knsTruncatedPower p T (x^2)*‖f x‖^2 := by
  rw [← integral_neg_eq_self (fun x => knsTruncatedPower p T (x^2)*‖f x‖^2) volume]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [kns_fourier_fourier_eq_reflection hf hf1 hF1, neg_sq]

private theorem kns_fourier_squareMass_real {f : ℝ → ℂ}
    (hf1 : Integrable f) (hf2 : MemLp f 2) :
    (∫ ξ, ‖𝓕 f ξ‖^2) = ∫ x, ‖f x‖^2 := by
  obtain ⟨hF,hN⟩ := memLp_fourier_norm_eq_of_integrable hf1 hf2
  rw [integral_norm_sq_eq_toLp_norm_sq_complex hF,
    integral_norm_sq_eq_toLp_norm_sq_complex hf2,hN]

/-- Actual two-carrier Fourier zeros give a uniform bound on the sum
of both finite truncated energies. Only C1, L1, L2, and the two second
moments are inputs; the bound precedes f and T. -/
theorem exists_constant_knsStageA_twoRows
    (Λ M : TwoSidedCarrier) (F J G K : Finset ℤ) {σ : ℝ} (hσ : 1 < σ)
    (hgapΛ : ∀ j : ℤ, j ∉ J →
      max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ (2*σ)⁻¹)
    (hgapM : ∀ j : ℤ, j ∉ K →
      max |M j| |M (j+1)| * (M (j+1)-M j) ≤ (2*σ)⁻¹)
    {p : ℕ} (hp : 1 ≤ p) :
    ∃ C > 0, ∀ (f : ℝ → ℂ), ContDiff ℝ 1 f → ContDiff ℝ 1 (𝓕 f) →
      Integrable f → Integrable (𝓕 f) → MemLp f 2 →
      Integrable (fun x => x^2*‖f x‖^2) → Integrable (fun ξ => ξ^2*‖𝓕 f ξ‖^2) →
      (∀ j : ℤ, j ∉ F → f (Λ j) = 0) → (∀ j : ℤ, j ∉ G → 𝓕 f (M j) = 0) →
      ∀ T : ℝ, 0 ≤ T →
      (∫ x, knsTruncatedPower p T (x^2)*‖f x‖^2) +
          (∫ ξ, knsTruncatedPower p T (ξ^2)*‖𝓕 f ξ‖^2) ≤ C * ∫ x, ‖f x‖^2 := by
  obtain ⟨A,hA,hΛ⟩ := exists_constant_knsStageA_oneRow Λ F J hσ hgapΛ hp
  obtain ⟨B,hB,hM⟩ := exists_constant_knsStageA_oneRow M G K hσ hgapM hp
  have hσ0 : 0 ≤ σ := by linarith
  have hs : 1 < Real.sqrt σ := (Real.lt_sqrt (by norm_num)).mpr (by simpa using hσ)
  have hsq := Real.sq_sqrt hσ0
  have hden : 0 < σ-Real.sqrt σ := by nlinarith
  let C := (A+B)/(σ-Real.sqrt σ)
  have hC : 0 < C := div_pos (by linarith) hden
  have hCeq : C*(σ-Real.sqrt σ)=A+B := by dsimp only [C]; field_simp
  refine ⟨C,hC,?_⟩
  intro f hf hF hf1 hF1 hf2 hx2 hξ2 hzΛ hzM T hT
  have hF2 := (memLp_fourier_norm_eq_of_integrable hf1 hf2).1
  have hdouble : Integrable (fun x => x^2*‖𝓕 (𝓕 f) x‖^2) := by
    have h := hx2.comp_neg
    convert! h using 1
    funext x
    rw [kns_fourier_fourier_eq_reflection hf.continuous hf1 hF1,neg_sq]
  have h1 := hΛ f hf hf1 hf2 hx2 hξ2 hzΛ T hT
  have h2 := hM (𝓕 f) hF hF1 hF2 hξ2 hdouble hzM T hT
  rw [integral_knsTruncatedPower_fourier_fourier hf.continuous hf1 hF1,
    kns_fourier_squareMass_real hf1 hf2] at h2
  have hsum := add_le_add h1 h2
  apply (mul_le_mul_iff_left₀ hden).mp
  have he := congrArg (fun z : ℝ => z*(∫ x, ‖f x‖^2)) hCeq
  nlinarith [he]

private theorem kns_power_integrable_of_uniform_truncations {p : ℕ}
    {f : ℝ → ℂ} (hf : Continuous f) {C : ℝ}
    (hbound : ∀ k : ℕ, knsTruncatedEnergy p k f ≤ ENNReal.ofReal C) :
    Integrable (fun x => x^(2*p)*‖f x‖^2) := by
  let w : ℕ → ℝ → ℝ≥0∞ := fun k x =>
    ENNReal.ofReal (knsTruncatedPower p k (x^2))*ENNReal.ofReal (‖f x‖^2)
  have hw (k : ℕ) : Measurable (w k) :=
    (((contDiff_one_knsTruncatedPower p k).continuous.comp (continuous_id.pow 2)).measurable.ennreal_ofReal).mul
      ((hf.norm.pow 2).measurable.ennreal_ofReal)
  have hlim (x : ℝ) : Tendsto (fun k : ℕ => w k x) atTop
      (𝓝 (ENNReal.ofReal (x^(2*p)*‖f x‖^2))) := by
    apply tendsto_const_nhds.congr'
    have hnat : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    filter_upwards [hnat.eventually (eventually_ge_atTop (x^2))] with k hk
    have hxp : 0 ≤ x^(2*p) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) p
    simp [w,knsTruncatedPower,hk,← pow_mul,ENNReal.ofReal_mul hxp]
  have hfatou := lintegral_liminf_le (μ := (volume : Measure ℝ)) (u := (atTop : Filter ℕ)) hw
  have he : (∫⁻ x, liminf (fun k => w k x) atTop) =
      ∫⁻ x, ENNReal.ofReal (x^(2*p)*‖f x‖^2) := by
    apply lintegral_congr
    intro x
    exact (hlim x).liminf_eq
  rw [he] at hfatou
  have hlimbound : liminf (fun k : ℕ => ∫⁻ x, w k x) atTop ≤ ENNReal.ofReal C :=
    liminf_le_of_frequently_le (Eventually.frequently (Eventually.of_forall hbound))
  refine ⟨(show Continuous (fun x : ℝ => x^(2*p)*‖f x‖^2) by fun_prop).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun x =>
    mul_nonneg (show 0 ≤ x^(2*p) by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) p) (sq_nonneg _)))).mpr
  exact (hfatou.trans hlimbound).trans_lt ENNReal.ofReal_lt_top

/-- The genuine initial KNS bootstrap: actual two-carrier Fourier zeros
and just the two second moments imply every physical and Fourier square
moment. Higher moments are conclusions of finite-truncation absorption
and Fatou, not inputs or recurrence certificates. -/
theorem knsStageA_all_squareMoments
    (Λ M : TwoSidedCarrier) (F J G K : Finset ℤ) {σ : ℝ} (hσ : 1 < σ)
    (hgapΛ : ∀ j : ℤ, j ∉ J →
      max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ (2*σ)⁻¹)
    (hgapM : ∀ j : ℤ, j ∉ K →
      max |M j| |M (j+1)| * (M (j+1)-M j) ≤ (2*σ)⁻¹)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hF : ContDiff ℝ 1 (𝓕 f))
    (hf1 : Integrable f) (hF1 : Integrable (𝓕 f)) (hf2 : MemLp f 2)
    (hx2 : Integrable (fun x => x^2*‖f x‖^2))
    (hξ2 : Integrable (fun ξ => ξ^2*‖𝓕 f ξ‖^2))
    (hzΛ : ∀ j : ℤ, j ∉ F → f (Λ j) = 0)
    (hzM : ∀ j : ℤ, j ∉ G → 𝓕 f (M j) = 0) :
    ∀ p : ℕ, Integrable (fun x => x^(2*p)*‖f x‖^2) ∧
      Integrable (fun ξ => ξ^(2*p)*‖𝓕 f ξ‖^2) := by
  intro p
  by_cases hp0 : p = 0
  · subst p
    simpa using And.intro (integrable_norm_sq_of_memLp_complex hf2)
      (integrable_norm_sq_of_memLp_complex (memLp_fourier_norm_eq_of_integrable hf1 hf2).1)
  have hp : 1 ≤ p := by omega
  obtain ⟨C,hC,h⟩ := exists_constant_knsStageA_twoRows Λ M F J G K hσ hgapΛ hgapM hp
  have hb (T : ℝ) (hT : 0 ≤ T) := h f hf hF hf1 hF1 hf2 hx2 hξ2 hzΛ hzM T hT
  have hxn (T : ℝ) (hT : 0 ≤ T) : 0 ≤ ∫ x, knsTruncatedPower p T (x^2)*‖f x‖^2 :=
    integral_nonneg (fun x => mul_nonneg (knsTruncatedPower_nonneg hp hT (sq_nonneg x)) (sq_nonneg _))
  have hξn (T : ℝ) (hT : 0 ≤ T) : 0 ≤ ∫ ξ, knsTruncatedPower p T (ξ^2)*‖𝓕 f ξ‖^2 :=
    integral_nonneg (fun ξ => mul_nonneg (knsTruncatedPower_nonneg hp hT (sq_nonneg ξ)) (sq_nonneg _))
  constructor
  · apply kns_power_integrable_of_uniform_truncations (C := C * ∫ x, ‖f x‖^2) hf.continuous
    intro k
    rw [knsTruncatedEnergy_eq_ofReal_integral hp (Nat.cast_nonneg k) hf.continuous hx2]
    exact ENNReal.ofReal_le_ofReal (by linarith [hb k (Nat.cast_nonneg k),hξn k (Nat.cast_nonneg k)])
  · apply kns_power_integrable_of_uniform_truncations (C := C * ∫ x, ‖f x‖^2) hF.continuous
    intro k
    rw [knsTruncatedEnergy_eq_ofReal_integral hp (Nat.cast_nonneg k) hF.continuous hξ2]
    exact ENNReal.ofReal_le_ofReal (by linarith [hb k (Nat.cast_nonneg k),hxn k (Nat.cast_nonneg k)])

/-- An actual even square moment is precisely L2 membership of the
corresponding complex power times the function, including p zero. -/
theorem kns_memLp_power_of_squareMoment {f : ℝ → ℂ} (hf : Continuous f) (p : ℕ)
    (hp : Integrable (fun x => x^(2*p)*‖f x‖^2)) :
    MemLp (fun x : ℝ => (x : ℂ)^p * f x) 2 := by
  have hc : Continuous (fun x : ℝ => (x : ℂ)^p * f x) := by fun_prop
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  convert! hp using 1
  funext x
  simp only [norm_mul,mul_pow,norm_pow,Complex.norm_real,Real.norm_eq_abs,← pow_mul]
  rw [Nat.mul_comm p 2,pow_mul,sq_abs,← pow_mul]

/-- Actual power-weighted L2 domains on both sides of the Fourier pair
are consequences of Stage A. No weighted domain beyond the initial
second moments is supplied as a hypothesis. -/
theorem knsStageA_all_power_memLp
    (Λ M : TwoSidedCarrier) (F J G K : Finset ℤ) {σ : ℝ} (hσ : 1 < σ)
    (hgapΛ : ∀ j : ℤ, j ∉ J →
      max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ (2*σ)⁻¹)
    (hgapM : ∀ j : ℤ, j ∉ K →
      max |M j| |M (j+1)| * (M (j+1)-M j) ≤ (2*σ)⁻¹)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hF : ContDiff ℝ 1 (𝓕 f))
    (hf1 : Integrable f) (hF1 : Integrable (𝓕 f)) (hf2 : MemLp f 2)
    (hx2 : Integrable (fun x => x^2*‖f x‖^2))
    (hξ2 : Integrable (fun ξ => ξ^2*‖𝓕 f ξ‖^2))
    (hzΛ : ∀ j : ℤ, j ∉ F → f (Λ j) = 0)
    (hzM : ∀ j : ℤ, j ∉ G → 𝓕 f (M j) = 0) :
    ∀ p : ℕ, MemLp (fun x : ℝ => (x : ℂ)^p * f x) 2 ∧
      MemLp (fun ξ : ℝ => (ξ : ℂ)^p * 𝓕 f ξ) 2 := by
  intro p
  obtain ⟨hphys,hfreq⟩ := knsStageA_all_squareMoments Λ M F J G K hσ hgapΛ hgapM
    hf hF hf1 hF1 hf2 hx2 hξ2 hzΛ hzM p
  exact ⟨kns_memLp_power_of_squareMoment hf.continuous p hphys,
    kns_memLp_power_of_squareMoment hF.continuous p hfreq⟩

end

end MeyerGeneralProblem
