module

public import MeyerGeneralProblem.Sampling.KNSLocalizedPoincare
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

@[expose] public section

/-!
# Tangent-truncated integer powers for the initial KNS bootstrap

The actual weight equals x^n below T and its tangent line above T.
Its linear tail makes every fixed truncation compatible with only a
second Fourier moment; no higher moment is assumed to get started.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter
open scoped Topology FourierTransform

/-- The actual power followed by its tangent-line continuation. -/
def knsTruncatedPower (n : ℕ) (T x : ℝ) : ℝ :=
  if x ≤ T then x^n else T^n+(n:ℝ)*T^(n-1)*(x-T)

/-- Both branches join with the same actual first derivative. -/
theorem hasDerivAt_knsTruncatedPower (n : ℕ) (T x : ℝ) :
    HasDerivAt (knsTruncatedPower n T) ((n:ℝ)*(min x T)^(n-1)) x := by
  have hpow (x : ℝ) := hasDerivAt_pow n x
  have hlin (x : ℝ) : HasDerivAt (fun y : ℝ => T^n+(n:ℝ)*T^(n-1)*(y-T))
      ((n:ℝ)*T^(n-1)) x := by
    convert! (((hasDerivAt_id x).sub_const T).const_mul
      ((n:ℝ)*T^(n-1))).const_add (T^n) using 1
    simp only [mul_one]
  rcases lt_trichotomy x T with hx | hx | hx
  · rw [min_eq_left hx.le]
    apply (hpow x).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    change y < T at hy
    simp [knsTruncatedPower, hy.le]
  · subst x
    rw [min_self]
    have hl : HasDerivWithinAt (knsTruncatedPower n T) ((n:ℝ)*T^(n-1)) (Iic T) T := by
      apply (hpow T).hasDerivWithinAt.congr
      · intro y hy
        change y ≤ T at hy
        simp [knsTruncatedPower, hy]
      · simp [knsTruncatedPower]
    have hr : HasDerivWithinAt (knsTruncatedPower n T) ((n:ℝ)*T^(n-1)) (Ici T) T := by
      apply (hlin T).hasDerivWithinAt.congr
      · intro y hy
        change T ≤ y at hy
        rcases lt_or_eq_of_le hy with hy | hy
        · simp [knsTruncatedPower, not_le.mpr hy]
        · subst y; simp [knsTruncatedPower]
      · simp [knsTruncatedPower]
    have hu := hl.union hr
    rw [Iic_union_Ici] at hu
    exact hu.hasDerivAt (by simp)
  · rw [min_eq_right hx.le]
    apply (hlin x).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    change T < y at hy
    simp [knsTruncatedPower, not_le.mpr hy]

/-- Exact ordinary derivative of the tangent-truncated weight. -/
theorem deriv_knsTruncatedPower (n : ℕ) (T : ℝ) :
    deriv (knsTruncatedPower n T) = fun x => (n:ℝ)*(min x T)^(n-1) :=
  funext (fun x => (hasDerivAt_knsTruncatedPower n T x).deriv)

/-- Tangent truncation is genuinely C1 across its joining point. -/
theorem contDiff_one_knsTruncatedPower (n : ℕ) (T : ℝ) :
    ContDiff ℝ 1 (knsTruncatedPower n T) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (hasDerivAt_knsTruncatedPower n T x).differentiableAt, ?_⟩
  rw [deriv_knsTruncatedPower]
  fun_prop

/-- The derivative is nonnegative on the relevant nonnegative half-line. -/
theorem deriv_knsTruncatedPower_nonneg (n : ℕ) {T x : ℝ} (hT : 0 ≤ T) (hx : 0 ≤ x) :
    0 ≤ deriv (knsTruncatedPower n T) x := by
  rw [deriv_knsTruncatedPower]
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_min hx hT) _)

/-- Each fixed truncation is increasing on the nonnegative half-line. -/
theorem monotoneOn_knsTruncatedPower (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    MonotoneOn (knsTruncatedPower n T) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    (contDiff_one_knsTruncatedPower n T).continuous.continuousOn
    ((contDiff_one_knsTruncatedPower n T).differentiable (by norm_num)).differentiableOn
  intro x hx
  exact deriv_knsTruncatedPower_nonneg n hT (interior_subset hx)

/-- The derivative of the truncated weight is increasing, so the weight
is genuinely convex, including the flat-derivative tail. -/
theorem convexOn_knsTruncatedPower (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ConvexOn ℝ (Ici 0) (knsTruncatedPower n T) := by
  apply MonotoneOn.convexOn_of_deriv (convex_Ici _)
    (contDiff_one_knsTruncatedPower n T).continuous.continuousOn
    ((contDiff_one_knsTruncatedPower n T).differentiable (by norm_num)).differentiableOn
  intro x hx y hy hxy
  rw [deriv_knsTruncatedPower]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact pow_le_pow_left₀ (le_min (interior_subset hx) hT) (min_le_min_right T hxy) _

/-- A positive-order truncation vanishes at zero. -/
theorem knsTruncatedPower_zero {n : ℕ} (hn : 1 ≤ n) {T : ℝ} (hT : 0 ≤ T) :
    knsTruncatedPower n T 0 = 0 := by
  simp [knsTruncatedPower, hT, show n ≠ 0 by omega]

/-- The actual truncated weight is nonnegative on its domain. -/
theorem knsTruncatedPower_nonneg {n : ℕ} (hn : 1 ≤ n) {T x : ℝ} (hT : 0 ≤ T) (hx : 0 ≤ x) :
    0 ≤ knsTruncatedPower n T x := by
  rw [← knsTruncatedPower_zero hn hT]
  exact monotoneOn_knsTruncatedPower n hT (by simp) hx hx

/-- The tangent continuation never exceeds the original nonnegative power. -/
theorem knsTruncatedPower_le_pow {n : ℕ} (hn : 1 ≤ n) {T x : ℝ} (hT : 0 ≤ T) (hx : 0 ≤ x) :
    knsTruncatedPower n T x ≤ x^n := by
  by_cases h : x ≤ T
  · simp [knsTruncatedPower, h]
  · simp only [knsTruncatedPower, h, ite_false]
    have hc : ConvexOn ℝ (Ici 0) (fun x : ℝ => x^n) := by
      have hp := convexOn_rpow (show (1:ℝ) ≤ n by exact_mod_cast hn)
      simpa only [Real.rpow_natCast] using hp
    have ht := convex_tangent_le_on_nonnegative hc hT (hasDerivAt_pow n T).differentiableAt hx
    simpa only [deriv_pow_field] using ht

/-- Every fixed truncation has a true linear upper bound on the entire
nonnegative half-line, not only an asymptotic big-O assertion. -/
theorem knsTruncatedPower_le_linear {n : ℕ} (hn : 1 ≤ n) {T x : ℝ} (hT : 0 ≤ T) (hx : 0 ≤ x) :
    knsTruncatedPower n T x ≤ (n:ℝ)*T^(n-1)*x := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hpow (y : ℝ) : y^n = y^(n-1)*y := by
    rw [← pow_succ]
    congr 1
    omega
  by_cases h : x ≤ T
  · simp only [knsTruncatedPower, h, ite_true]
    rw [hpow]
    have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx h (n-1)) hx
    have he := mul_nonneg (sub_nonneg.mpr hnR) (mul_nonneg (pow_nonneg hT (n-1)) hx)
    nlinarith
  · simp only [knsTruncatedPower, h, ite_false]
    rw [hpow T]
    have he := mul_nonneg (sub_nonneg.mpr hnR) (mul_nonneg (pow_nonneg hT (n-1)) hT)
    nlinarith

/-- A dilation grows the truncated weight by at most its original power.
The constant does not depend on the truncation threshold. -/
theorem knsTruncatedPower_mul_le {n : ℕ} (hn : 1 ≤ n) {T x c : ℝ}
    (hT : 0 ≤ T) (hx : 0 ≤ x) (hc : 1 ≤ c) :
    knsTruncatedPower n T (c*x) ≤ c^n * knsTruncatedPower n T x := by
  have hc0 : 0 ≤ c := by linarith
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hxc : x ≤ c*x := by nlinarith
  by_cases hcx : c*x ≤ T
  · have hxt : x ≤ T := hxc.trans hcx
    simp [knsTruncatedPower, hcx, hxt, mul_pow]
  by_cases hxt : x ≤ T
  · simpa only [knsTruncatedPower, hxt, ite_true, mul_pow] using
      knsTruncatedPower_le_pow hn hT (mul_nonneg hc0 hx)
  have htx : 0 ≤ x-T := by linarith
  have hcn : c ≤ c^n := by
    calc
      c = c^1 := by simp
      _ ≤ c^n := pow_le_pow_right₀ hc hn
  have hb : 1+(n:ℝ)*(c-1) ≤ c^n := by
    simpa only [add_sub_cancel] using one_add_mul_le_pow (a := c-1) (by linarith) n
  have hp : T^n = T^(n-1)*T := by
    rw [← pow_succ]
    congr 1
    omega
  have h1 := mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hcn)) htx
  have h2 := mul_nonneg hT (sub_nonneg.mpr hb)
  have h3 := mul_nonneg (pow_nonneg hT (n-1)) (add_nonneg h1 h2)
  simp only [knsTruncatedPower, hcx, hxt, ite_false]
  rw [hp]
  nlinarith

/-- Increasing the truncation threshold past a fixed point gives exact
equality, hence genuine pointwise convergence to the untruncated power. -/
theorem tendsto_knsTruncatedPower (n : ℕ) (x : ℝ) :
    Tendsto (fun T : ℝ => knsTruncatedPower n T x) atTop (𝓝 (x^n)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop x] with T hT
  simp [knsTruncatedPower, hT]

/-- Finite second moment suffices for every fixed tangent truncation;
the higher untruncated moment is not assumed. -/
theorem integrable_knsTruncatedPower_weight {n : ℕ} (hn : 1 ≤ n) {T : ℝ} (hT : 0 ≤ T)
    {w : ℝ → ℝ} (hw : ∀ x, 0 ≤ w x) (hm : AEStronglyMeasurable w volume)
    (hxi : Integrable (fun x => x^2*w x)) :
    Integrable (fun x => knsTruncatedPower n T (x^2)*w x) := by
  have hc : Continuous (fun x : ℝ => knsTruncatedPower n T (x^2)) :=
    (contDiff_one_knsTruncatedPower n T).continuous.comp (continuous_id.pow 2)
  apply (hxi.const_mul ((n:ℝ)*T^(n-1))).mono' (hc.aestronglyMeasurable.mul hm)
  filter_upwards [] with x
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (knsTruncatedPower_nonneg hn hT (sq_nonneg x)) (hw x))]
  have h := mul_le_mul_of_nonneg_right (knsTruncatedPower_le_linear hn hT (sq_nonneg x)) (hw x)
  nlinarith

/-- The actual localized classical Fourier transform admits every fixed
tangent truncation using only the local C1 domain, not higher moments. -/
theorem integrable_knsTruncatedPower_localizedFourier
    {p n : ℕ} (hp : 1 ≤ p) (hn : 2 ≤ n) {T u : ℝ} (hT : 0 ≤ T) (hu : 0 < u)
    (v : ℝ) {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) :
    Integrable (fun ξ => knsTruncatedPower p T (ξ^2)*
      ‖𝓕 (knsLocalizedFunction n u v f) ξ‖^2) := by
  obtain ⟨hF,hD⟩ := memLp_knsLocalizedFunction_and_deriv hn hu v hf
  obtain ⟨hF1,hD1⟩ := integrable_knsLocalizedFunction_and_deriv hn hu v hf
  have hG := (memLp_fourier_norm_eq_of_integrable hF1 hF).1
  have hsecond := (classicalFourier_secondMoment_of_deriv
    (contDiff_one_knsLocalizedFunction hn hu v hf) hD hF1 hD1).1
  exact integrable_knsTruncatedPower_weight hp hT (fun _ => sq_nonneg _)
    (hG.aestronglyMeasurable.norm.pow 2) hsecond

/-- Every fixed truncated power satisfies the actual localized Fourier
inequality after finite deletions. No higher-weight integrability premise
remains, and the geometric radius precedes both cutoff and weight order. -/
theorem exists_radius_truncatedPower_poincare_of_finite_exceptions
    (Λ : TwoSidedCarrier) (F J : Finset ℤ) {σ : ℝ} (hσ : 0 < σ)
    (hgap : ∀ j : ℤ, j ∉ J →
      max |Λ j| |Λ (j+1)| * (Λ (j+1)-Λ j) ≤ (2*σ)⁻¹) :
    ∃ X0 > 0, ∀ (n : ℕ), 2 ≤ n → ∀ (u : ℝ), 0 < u → ∀ (v : ℝ),
      X0 ≤ |v|-3*u/2 →
      ∀ (f : ℝ → ℂ), ContDiff ℝ 1 f → (∀ j : ℤ, j ∉ F → f (Λ j) = 0) →
      ∀ (p : ℕ), 1 ≤ p → ∀ T : ℝ, 0 ≤ T →
        knsTruncatedPower p T ((σ*(|v|-3*u/2))^2)*
          (∫ x, ‖knsLocalizedFunction n u v f x‖^2) ≤
        ∫ ξ, knsTruncatedPower p T (ξ^2)*‖𝓕 (knsLocalizedFunction n u v f) ξ‖^2 := by
  obtain ⟨R,hR,h⟩ :=
    exists_radius_classicalFourier_poincare_knsLocalizedFunction_of_finite_exceptions Λ F J hσ hgap
  refine ⟨R,hR,?_⟩
  intro n hn u hu v hv f hf hz p hp T hT
  exact h n hn u hu v hv f hf hz (knsTruncatedPower p T)
    (convexOn_knsTruncatedPower p hT) (monotoneOn_knsTruncatedPower p hT)
    (hasDerivAt_knsTruncatedPower p T _).differentiableAt
    (integrable_knsTruncatedPower_localizedFourier hp hn hT hu v hf)

end

end MeyerGeneralProblem
