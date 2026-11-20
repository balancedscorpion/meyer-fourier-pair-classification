module

public import MeyerGeneralProblem.Distribution.GaussianHeatSemigroup
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-!
# The heat equation for the Gaussian convolution

The normalized Gaussian kernel solves the heat equation with spatial
diffusivity one fourth in the convention with exponent `-x²/t`.
Integrable densities inherit the equation by dominated differentiation.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

private def heatNormalizer (t : ℝ) : ℝ := (Real.sqrt (Real.pi * t))⁻¹

private def realHeatKernel (t z : ℝ) : ℝ :=
  heatNormalizer t * Real.exp (-(z ^ 2 / t))

private def realHeatKernelDx (t z : ℝ) : ℝ :=
  (-(2 * z) / t) * realHeatKernel t z

private def realHeatKernelDxx (t z : ℝ) : ℝ :=
  ((4 * (z ^ 2 / t) - 2) / t) * realHeatKernel t z

private theorem heatNormalizer_nonneg (t : ℝ) : 0 ≤ heatNormalizer t := by
  unfold heatNormalizer
  positivity

private theorem hasDerivAt_heatNormalizer {t : ℝ} (ht : 0 < t) :
    HasDerivAt heatNormalizer (-(heatNormalizer t) / (2 * t)) t := by
  have hp : 0 < Real.pi * t := mul_pos Real.pi_pos ht
  have hRoot : HasDerivAt (fun s : ℝ => Real.sqrt (Real.pi * s))
      (Real.pi / (2 * Real.sqrt (Real.pi * t))) t := by
    have h := (Real.hasDerivAt_sqrt hp.ne').comp t ((hasDerivAt_id t).const_mul Real.pi)
    have he : (1 / (2 * Real.sqrt (Real.pi * t))) * (Real.pi * 1) =
        Real.pi / (2 * Real.sqrt (Real.pi * t)) := by ring
    rw [he] at h
    exact h
  have hr : Real.sqrt (Real.pi * t) ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  have h := hRoot.inv hr
  have he : -(Real.pi / (2 * Real.sqrt (Real.pi * t))) / (Real.sqrt (Real.pi * t)) ^ 2 =
      -(heatNormalizer t) / (2 * t) := by
    rw [Real.sq_sqrt hp.le, heatNormalizer]
    field_simp [hr, ht.ne', Real.pi_pos.ne']
  rw [he] at h
  exact h

private theorem hasDerivAt_realHeatKernel_space (t z : ℝ) :
    HasDerivAt (realHeatKernel t) (realHeatKernelDx t z) z := by
  have hArg : HasDerivAt (fun y : ℝ => -(y ^ 2 / t)) (-(2 * z) / t) z := by
    simpa [Pi.pow_apply, neg_div] using
      ((((hasDerivAt_id z).pow 2).div_const t).const_mul (-1 : ℝ))
  have h := hArg.exp.const_mul (heatNormalizer t)
  have he : heatNormalizer t * (Real.exp (-(z ^ 2 / t)) * (-(2 * z) / t)) =
      realHeatKernelDx t z := by
    unfold realHeatKernelDx realHeatKernel
    ring
  rw [he] at h
  exact h

private theorem hasDerivAt_realHeatKernelDx_space (t z : ℝ) :
    HasDerivAt (realHeatKernelDx t) (realHeatKernelDxx t z) z := by
  have hCoef : HasDerivAt (fun y : ℝ => -(2 * y) / t) (-(2 : ℝ) / t) z := by
    simpa only [id_eq, Pi.neg_apply, mul_one] using (((hasDerivAt_id z).const_mul (2 : ℝ)).neg.div_const t)
  have h := hCoef.mul (hasDerivAt_realHeatKernel_space t z)
  have he : (-(2 : ℝ) / t) * realHeatKernel t z + (-(2 * z) / t) * realHeatKernelDx t z =
      realHeatKernelDxx t z := by
    unfold realHeatKernelDx realHeatKernelDxx
    ring
  rw [he] at h
  exact h

private theorem hasDerivAt_realHeatKernel_time {t : ℝ} (ht : 0 < t) (z : ℝ) :
    HasDerivAt (fun s => realHeatKernel s z) (realHeatKernelDxx t z / 4) t := by
  have hArg : HasDerivAt (fun s : ℝ => -(z ^ 2 / s)) (z ^ 2 / t ^ 2) t := by
    have hInv : HasDerivAt (fun s : ℝ => s⁻¹) (-(1 : ℝ) / t ^ 2) t := by
      simpa only [div_eq_mul_inv, neg_one_mul] using hasDerivAt_inv ht.ne'
    have h := hInv.const_mul (-(z ^ 2))
    rw [show -(z ^ 2) * (-(1 : ℝ) / t ^ 2) = z ^ 2 / t ^ 2 by ring] at h
    simpa only [div_eq_mul_inv, neg_mul] using h
  have h := (hasDerivAt_heatNormalizer ht).mul hArg.exp
  have he : (-(heatNormalizer t) / (2 * t)) * Real.exp (-(z ^ 2 / t)) +
      heatNormalizer t * (Real.exp (-(z ^ 2 / t)) * (z ^ 2 / t ^ 2)) =
      realHeatKernelDxx t z / 4 := by
    unfold realHeatKernelDxx realHeatKernel
    field_simp [ht.ne']
    ring
  rw [he] at h
  exact h

private theorem exp_neg_le_one_and_mul_exp_neg_le_one (q : ℝ) (hq : 0 ≤ q) :
    Real.exp (-q) ≤ 1 ∧ q * Real.exp (-q) ≤ 1 := by
  refine ⟨Real.exp_le_one_iff.mpr (neg_nonpos.mpr hq), ?_⟩
  calc
    _ ≤ Real.exp q * Real.exp (-q) :=
      mul_le_mul_of_nonneg_right ((le_add_of_nonneg_right zero_le_one).trans
        (Real.add_one_le_exp q)) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

private theorem norm_realHeatKernel_le {t : ℝ} (ht : 0 < t) (z : ℝ) :
    ‖realHeatKernel t z‖ ≤ heatNormalizer t := by
  rw [realHeatKernel, norm_mul, Real.norm_eq_abs (heatNormalizer t),
    Real.norm_eq_abs (Real.exp _), abs_of_nonneg (heatNormalizer_nonneg t), abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (heatNormalizer_nonneg t)
    (exp_neg_le_one_and_mul_exp_neg_le_one _ (by positivity)).1

private theorem norm_realHeatKernelDx_le {t : ℝ} (ht : 0 < t) (z : ℝ) :
    ‖realHeatKernelDx t z‖ ≤ (2 * (1 / t + 1)) * heatNormalizer t := by
  let q := z ^ 2 / t
  let E := Real.exp (-q)
  have hE := exp_neg_le_one_and_mul_exp_neg_le_one q (by dsimp [q]; positivity)
  have hz : |z| ≤ 1 + z ^ 2 := by
    nlinarith only [sq_nonneg (|z| - 1 / 2), sq_abs z]
  have hz' : |z| / t ≤ 1 / t + q := by
    dsimp [q]
    rw [← add_div]
    exact div_le_div_of_nonneg_right hz ht.le
  have hSl : (|z| / t) * E ≤ 1 / t + 1 := by
    calc
      _ ≤ (1 / t + q) * E := mul_le_mul_of_nonneg_right hz' (Real.exp_pos _).le
      _ = (1 / t) * E + q * E := by ring
      _ ≤ _ := add_le_add (mul_le_of_le_one_right (by positivity) hE.1) hE.2
  calc
    ‖realHeatKernelDx t z‖ = (2 * ((|z| / t) * E)) * heatNormalizer t := by
      simp only [realHeatKernelDx, realHeatKernel, Real.norm_eq_abs, abs_mul, abs_div,
        abs_neg, abs_of_pos ht, abs_of_nonneg (heatNormalizer_nonneg t), abs_of_pos (Real.exp_pos _),
        show |(2 : ℝ)| = 2 by norm_num]
      dsimp [E, q]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hSl (by norm_num)) (heatNormalizer_nonneg t)

private theorem norm_realHeatKernelDxx_le {t : ℝ} (ht : 0 < t) (z : ℝ) :
    ‖realHeatKernelDxx t z‖ ≤ (6 * heatNormalizer t) / t := by
  let q := z ^ 2 / t
  let E := Real.exp (-q)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hE := exp_neg_le_one_and_mul_exp_neg_le_one q hq
  have hAbs : |4 * q - 2| ≤ 4 * q + 2 := by
    have h := abs_add_le (4 * q) (-2)
    rw [abs_of_nonneg (show 0 ≤ 4 * q by positivity), abs_neg,
      show |(2 : ℝ)| = 2 by norm_num, ← sub_eq_add_neg] at h
    exact h
  have hB : |4 * q - 2| * E ≤ 6 := by
    calc
      _ ≤ (4 * q + 2) * E := mul_le_mul_of_nonneg_right hAbs (Real.exp_pos _).le
      _ = 4 * (q * E) + 2 * E := by ring
      _ ≤ 4 * 1 + 2 * 1 := add_le_add
        (mul_le_mul_of_nonneg_left hE.2 (by norm_num))
        (mul_le_mul_of_nonneg_left hE.1 (by norm_num))
      _ = _ := by norm_num
  calc
    ‖realHeatKernelDxx t z‖ = (|4 * q - 2| * E * heatNormalizer t) / t := by
      simp only [realHeatKernelDxx, realHeatKernel, Real.norm_eq_abs, abs_mul, abs_div,
        abs_of_pos ht, abs_of_nonneg (heatNormalizer_nonneg t), abs_of_pos (Real.exp_pos _)]
      dsimp [q, E]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hB (heatNormalizer_nonneg t)) ht.le

private theorem integrable_mul_of_continuous_norm_bound {f g : ℝ → ℝ}
    (hf : Integrable f) (hg : Continuous g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) :
    Integrable (fun x : ℝ => f x * g x) := by
  refine (hf.norm.const_mul C).mono' (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
  filter_upwards with x
  rw [norm_mul, mul_comm ‖f x‖]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

private theorem hasDerivAt_integral_mul_with_bound
    {f : ℝ → ℝ} (hf : Integrable f) (K L : ℝ → ℝ → ℝ) (a : ℝ)
    {s : Set ℝ} (hs : s ∈ 𝓝 a) {M N : ℝ}
    (hK : ∀ b, Continuous (K b)) (hL : Continuous (L a))
    (hM : ∀ x, ‖K a x‖ ≤ M) (hN : ∀ b ∈ s, ∀ x, ‖L b x‖ ≤ N)
    (hD : ∀ b ∈ s, ∀ x, HasDerivAt (fun t => K t x) (L b x) b) :
    HasDerivAt (fun t => ∫ x : ℝ, f x * K t x) (∫ x : ℝ, f x * L a x) a := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Eventually.of_forall fun b => hf.aestronglyMeasurable.mul (hK b).aestronglyMeasurable)
    (integrable_mul_of_continuous_norm_bound hf (hK a) hM)
    (hf.aestronglyMeasurable.mul hL.aestronglyMeasurable)
    (Eventually.of_forall fun x b hb => by
      rw [norm_mul, mul_comm ‖f x‖]
      exact mul_le_mul_of_nonneg_right (hN b hb x) (norm_nonneg _))
    (hf.norm.const_mul N)
    (Eventually.of_forall fun x b hb => (hD b hb x).const_mul (f x))).2

private theorem realGaussianSmoothing_eq_integral_realHeatKernel
    (t : ℝ) (f : ℝ → ℝ) (y : ℝ) :
    realGaussianSmoothing t f y = ∫ x : ℝ, f x * realHeatKernel t (y - x) := by
  unfold realGaussianSmoothing
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [realHeatKernel, heatNormalizer, neg_div, show (y - x) ^ 2 = (x - y) ^ 2 by ring]
  ring

private theorem continuous_realHeatKernel (t : ℝ) : Continuous (realHeatKernel t) := by
  exact continuous_iff_continuousAt.mpr fun z => (hasDerivAt_realHeatKernel_space t z).continuousAt

private theorem continuous_realHeatKernelDx (t : ℝ) : Continuous (realHeatKernelDx t) := by
  exact continuous_iff_continuousAt.mpr fun z => (hasDerivAt_realHeatKernelDx_space t z).continuousAt

private theorem continuous_realHeatKernelDxx (t : ℝ) : Continuous (realHeatKernelDxx t) := by
  unfold realHeatKernelDxx
  exact (show Continuous (fun z : ℝ => (4 * (z ^ 2 / t) - 2) / t) by fun_prop).mul
    (continuous_realHeatKernel t)

private theorem hasDerivAt_realGaussianSmoothing_space {f : ℝ → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (realGaussianSmoothing t f)
      (∫ x : ℝ, f x * realHeatKernelDx t (y - x)) y := by
  rw [funext (realGaussianSmoothing_eq_integral_realHeatKernel t f)]
  refine hasDerivAt_integral_mul_with_bound hf
    (fun z x => realHeatKernel t (z - x)) (fun z x => realHeatKernelDx t (z - x)) y
    (s := univ) univ_mem (M := heatNormalizer t) (N := (2 * (1 / t + 1)) * heatNormalizer t)
    (fun z => (continuous_realHeatKernel t).comp (continuous_const.sub continuous_id))
    ((continuous_realHeatKernelDx t).comp (continuous_const.sub continuous_id))
    (fun x => norm_realHeatKernel_le ht _) (fun z _ x => norm_realHeatKernelDx_le ht _) ?_
  intro z _ x
  simpa only [Function.comp_def, id_eq, mul_one] using
    (hasDerivAt_realHeatKernel_space t (z - x)).comp z ((hasDerivAt_id z).sub_const x)

private theorem hasDerivAt_realGaussianSmoothing_deriv_space {f : ℝ → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (deriv (realGaussianSmoothing t f))
      (∫ x : ℝ, f x * realHeatKernelDxx t (y - x)) y := by
  rw [funext (fun z => (hasDerivAt_realGaussianSmoothing_space hf ht z).deriv)]
  refine hasDerivAt_integral_mul_with_bound hf
    (fun z x => realHeatKernelDx t (z - x)) (fun z x => realHeatKernelDxx t (z - x)) y
    (s := univ) univ_mem (M := (2 * (1 / t + 1)) * heatNormalizer t)
    (N := (6 * heatNormalizer t) / t)
    (fun z => (continuous_realHeatKernelDx t).comp (continuous_const.sub continuous_id))
    ((continuous_realHeatKernelDxx t).comp (continuous_const.sub continuous_id))
    (fun x => norm_realHeatKernelDx_le ht _) (fun z _ x => norm_realHeatKernelDxx_le ht _) ?_
  intro z _ x
  simpa only [Function.comp_def, id_eq, mul_one] using
    (hasDerivAt_realHeatKernelDx_space t (z - x)).comp z ((hasDerivAt_id z).sub_const x)

/-- At every positive time, Gaussian smoothing of integrable data
has two spatial derivatives at each point. -/
theorem differentiableAt_realGaussianSmoothing_twice {f : ℝ → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) (y : ℝ) :
    DifferentiableAt ℝ (realGaussianSmoothing t f) y ∧
      DifferentiableAt ℝ (deriv (realGaussianSmoothing t f)) y :=
  ⟨(hasDerivAt_realGaussianSmoothing_space hf ht y).differentiableAt,
    (hasDerivAt_realGaussianSmoothing_deriv_space hf ht y).differentiableAt⟩

private theorem heatNormalizer_le_of_le {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    heatNormalizer t ≤ heatNormalizer s := by
  simpa only [heatNormalizer, one_div] using one_div_le_one_div_of_le
    (Real.sqrt_pos.2 (mul_pos Real.pi_pos hs))
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hst Real.pi_pos.le))

/-- Gaussian smoothing of every real integrable density solves the
heat equation at positive times, with diffusivity one fourth. -/
theorem hasDerivAt_realGaussianSmoothing_time {f : ℝ → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun s => realGaussianSmoothing s f y)
      (deriv (deriv (realGaussianSmoothing t f)) y / 4) t := by
  rw [(hasDerivAt_realGaussianSmoothing_deriv_space hf ht y).deriv]
  rw [← integral_div]
  have hEq : (fun s => realGaussianSmoothing s f y) =
      fun s => ∫ x : ℝ, f x * realHeatKernel s (y - x) :=
    funext fun s => realGaussianSmoothing_eq_integral_realHeatKernel s f y
  rw [hEq]
  have hRewrite : (∫ x : ℝ, (f x * realHeatKernelDxx t (y - x)) / 4) =
      ∫ x : ℝ, f x * (realHeatKernelDxx t (y - x) / 4) := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hRewrite]
  let a := t / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hat : a < t := by dsimp [a]; linarith
  refine hasDerivAt_integral_mul_with_bound hf
    (fun z x => realHeatKernel z (y - x)) (fun z x => realHeatKernelDxx z (y - x) / 4) t
    (Ioi_mem_nhds hat) (M := heatNormalizer t) (N := (6 * heatNormalizer a / a) / 4)
    (fun z => (continuous_realHeatKernel z).comp (continuous_const.sub continuous_id))
    (((continuous_realHeatKernelDxx t).comp (continuous_const.sub continuous_id)).div_const 4)
    (fun x => norm_realHeatKernel_le ht _) ?_ ?_
  · intro z hz x
    have haz : a < z := hz
    rw [norm_div, Real.norm_of_nonneg (show 0 ≤ (4 : ℝ) by norm_num)]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    calc
      _ ≤ 6 * heatNormalizer z / z := norm_realHeatKernelDxx_le (ha.trans haz) _
      _ ≤ 6 * heatNormalizer a / z := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (heatNormalizer_le_of_le ha haz.le) (by norm_num)) (ha.trans haz).le
      _ ≤ 6 * heatNormalizer a / a :=
        div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (heatNormalizer_nonneg a)) ha haz.le
  · intro z hz x
    exact hasDerivAt_realHeatKernel_time (ha.trans (show a < z from hz)) _

/-- The sum of a shifted and an unshifted Gaussian evolution solves
the same heat equation wherever both heat parameters are positive. -/
theorem hasDerivAt_add_realGaussianSmoothing_shift_time
    {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) (τ : ℝ)
    {t : ℝ} (ht : 0 < t) (hShift : 0 < t + τ) (y : ℝ) :
    HasDerivAt (fun s => realGaussianSmoothing (s + τ) f y + realGaussianSmoothing s g y)
      (deriv (deriv (fun x => realGaussianSmoothing (t + τ) f x +
        realGaussianSmoothing t g x)) y / 4) t := by
  let F := realGaussianSmoothing (t + τ) f
  let G := realGaussianSmoothing t g
  have hD1 : deriv (fun x => F x + G x) = deriv F + deriv G := by
    funext x
    exact deriv_add (hasDerivAt_realGaussianSmoothing_space hf hShift x).differentiableAt
      (hasDerivAt_realGaussianSmoothing_space hg ht x).differentiableAt
  have hD2 : deriv (deriv (fun x => F x + G x)) y =
      deriv (deriv F) y + deriv (deriv G) y := by
    rw [hD1]
    exact deriv_add (hasDerivAt_realGaussianSmoothing_deriv_space hf hShift y).differentiableAt
      (hasDerivAt_realGaussianSmoothing_deriv_space hg ht y).differentiableAt
  have hL : HasDerivAt (fun s => realGaussianSmoothing (s + τ) f y)
      (deriv (deriv F) y / 4) t := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      (hasDerivAt_realGaussianSmoothing_time hf hShift y).comp t ((hasDerivAt_id t).add_const τ)
  change HasDerivAt ((fun s => realGaussianSmoothing (s + τ) f y) +
    (fun s => realGaussianSmoothing s g y)) (deriv (deriv (fun x => F x + G x)) y / 4) t
  rw [hD2, add_div]
  exact hL.add (hasDerivAt_realGaussianSmoothing_time hg ht y)

/-- A density vanishing within distance `δ` of the observation point
contributes at most a constant times the square root of heat time.
The constant depends on the distance and the full integrable norm. -/
theorem norm_realGaussianSmoothing_le_of_ae_zero_near
    {f : ℝ → ℝ} (hf : Integrable f) {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) (y : ℝ)
    (hZero : ∀ᵐ x : ℝ ∂volume, |x - y| < δ → f x = 0) :
    ‖realGaussianSmoothing t f y‖ ≤
      (Real.sqrt t / (Real.sqrt Real.pi * δ ^ 2)) *
        (∫ x : ℝ, ‖f x‖) := by
  let C := heatNormalizer t * (t / δ ^ 2)
  have hKernel (x : ℝ) (hx : δ ≤ |x - y|) : ‖realHeatKernel t (y - x)‖ ≤ C := by
    have hSq : δ ^ 2 ≤ (y - x) ^ 2 := by
      have hs := pow_le_pow_left₀ hδ.le hx 2
      rwa [sq_abs, show (x - y) ^ 2 = (y - x) ^ 2 by ring] at hs
    have hq : δ ^ 2 / t ≤ (y - x) ^ 2 / t := div_le_div_of_nonneg_right hSq ht.le
    have hqPos : 0 < δ ^ 2 / t := by positivity
    have hExp : Real.exp (-((y - x) ^ 2 / t)) ≤ t / δ ^ 2 := by
      have hOne := (exp_neg_le_one_and_mul_exp_neg_le_one ((y - x) ^ 2 / t)
        (by positivity)).2
      have hProd := (mul_le_mul_of_nonneg_right hq (Real.exp_pos _).le).trans hOne
      have hMul : Real.exp (-((y - x) ^ 2 / t)) * (δ ^ 2 / t) ≤ 1 := by
        rw [mul_comm]
        exact hProd
      have h := (le_div_iff₀ hqPos).mpr hMul
      simpa only [one_div_div] using h
    rw [realHeatKernel, norm_mul, Real.norm_eq_abs (heatNormalizer t),
      Real.norm_eq_abs (Real.exp _), abs_of_nonneg (heatNormalizer_nonneg t), abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left hExp (heatNormalizer_nonneg t)
  have hInt : Integrable (fun x : ℝ => f x * realHeatKernel t (y - x)) :=
    integrable_mul_of_continuous_norm_bound hf
      ((continuous_realHeatKernel t).comp (continuous_const.sub continuous_id))
      (fun x => norm_realHeatKernel_le ht (y - x))
  have hDom : ∀ᵐ x : ℝ ∂volume, ‖f x * realHeatKernel t (y - x)‖ ≤ C * ‖f x‖ := by
    filter_upwards [hZero] with x hx
    rcases lt_or_ge |x - y| δ with h | h
    · simp [hx h]
    · rw [norm_mul, mul_comm ‖f x‖]
      exact mul_le_mul_of_nonneg_right (hKernel x h) (norm_nonneg _)
  have hC : C = Real.sqrt t / (Real.sqrt Real.pi * δ ^ 2) := by
    dsimp only [C, heatNormalizer]
    rw [Real.sqrt_mul Real.pi_pos.le]
    field_simp [(Real.sqrt_pos.2 Real.pi_pos).ne', (Real.sqrt_pos.2 ht).ne', hδ.ne']
    nlinarith only [Real.sq_sqrt ht.le]
  rw [realGaussianSmoothing_eq_integral_realHeatKernel, ← hC, ← integral_const_mul]
  exact (norm_integral_le_integral_norm _).trans
    (integral_mono_ae hInt.norm (hf.norm.const_mul C) hDom)

/-- Data vanishing near a spatial point have a zero heat limit there,
jointly as positive time approaches zero and position approaches that point. -/
theorem tendsto_realGaussianSmoothing_zero_of_ae_zero_near
    {f : ℝ → ℝ} (hf : Integrable f) {δ : ℝ} (hδ : 0 < δ) (y : ℝ)
    (hZero : ∀ᵐ x : ℝ ∂volume, |x - y| < δ → f x = 0) :
    Tendsto (fun p : ℝ × ℝ => realGaussianSmoothing p.1 f p.2)
      (𝓝[Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)] (0, y)) (𝓝 0) := by
  let S : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)
  let l := 𝓝[S] (0, y)
  have hFst : Tendsto (Prod.fst : ℝ × ℝ → ℝ) l (𝓝 0) :=
    continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hSnd : Tendsto (Prod.snd : ℝ × ℝ → ℝ) l (𝓝 y) :=
    continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hSqrt : Tendsto (fun p : ℝ × ℝ => Real.sqrt p.1) l (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hFst
  have hLimit : Tendsto (fun p : ℝ × ℝ =>
      (Real.sqrt p.1 / (Real.sqrt Real.pi * (δ / 2) ^ 2)) * (∫ x : ℝ, ‖f x‖)) l (𝓝 0) := by
    simpa only [zero_div, zero_mul] using
      (hSqrt.div_const (Real.sqrt Real.pi * (δ / 2) ^ 2)).mul_const (∫ x : ℝ, ‖f x‖)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hLimit
  filter_upwards [self_mem_nhdsWithin (s := S),
    hSnd.eventually (Metric.ball_mem_nhds y (half_pos hδ))] with p hp hClose
  apply norm_realGaussianSmoothing_le_of_ae_zero_near hf hp.1 (half_pos hδ)
  have hPy : |p.2 - y| < δ / 2 := by simpa only [Metric.mem_ball, Real.dist_eq] using hClose
  filter_upwards [hZero] with x hx hDist
  apply hx
  calc
    |x - y| = |(x - p.2) + (p.2 - y)| := by rw [sub_add_sub_cancel]
    _ ≤ |x - p.2| + |p.2 - y| := abs_add_le _ _
    _ < δ := by linarith

end
end MeyerGeneralProblem
