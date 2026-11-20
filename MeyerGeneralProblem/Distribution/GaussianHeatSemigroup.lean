module

public import MeyerGeneralProblem.Distribution.GaussianSignAlternations
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# The Gaussian smoothing semigroup

The heat parameter is twice the variance of the normalized Gaussian.
The convolution identity of real Gaussian measures therefore composes
the smoothing operators at positive times.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

private def heatVariance (t : ℝ) : ℝ≥0 := (t / 2).toNNReal

private theorem heatVariance_coe {t : ℝ} (ht : 0 ≤ t) :
    (heatVariance t : ℝ) = t / 2 := by
  rw [heatVariance, Real.coe_toNNReal', max_eq_left (by positivity)]

private theorem heatVariance_ne_zero {t : ℝ} (ht : 0 < t) : heatVariance t ≠ 0 := by
  intro h
  have hh := heatVariance_coe ht.le
  rw [h, NNReal.coe_zero] at hh
  linarith

private theorem realGaussianSmoothing_eq_integral_gaussianReal {t : ℝ} (ht : 0 < t)
    (f : ℝ → ℝ) (y : ℝ) :
    realGaussianSmoothing t f y = ∫ x, f x ∂(gaussianReal y (heatVariance t)) := by
  rw [integral_gaussianReal_eq_integral_smul (heatVariance_ne_zero ht), realGaussianSmoothing,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [gaussianPDFReal, smul_eq_mul, heatVariance_coe ht.le,
    show 2 * Real.pi * (t / 2) = Real.pi * t by ring, show 2 * (t / 2) = t by ring]
  ring

private theorem integrable_gaussianReal_of_integrable {f : ℝ → ℝ} (hf : Integrable f volume)
    (x : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : Integrable f (gaussianReal x v) := by
  rw [gaussianReal_of_var_ne_zero _ hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF x v)
      (Eventually.of_forall fun _ => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF, smul_eq_mul]
  refine (hf.norm.const_mul (Real.sqrt (2 * Real.pi * v))⁻¹).mono'
    ((measurable_gaussianPDFReal x v).aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  filter_upwards with y
  rw [norm_mul, Real.norm_eq_abs (gaussianPDFReal x v y), abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
  have hPdf : gaussianPDFReal x v y ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
    rw [gaussianPDFReal]
    apply mul_le_of_le_one_right (by positivity)
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  exact mul_le_mul_of_nonneg_right hPdf (norm_nonneg _)

/-- Smoothing for two positive heat parameters composes by adding them.
The original density only needs to be Lebesgue integrable. -/
theorem realGaussianSmoothing_add_of_integrable {f : ℝ → ℝ} (hf : Integrable f volume)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (y : ℝ) :
    realGaussianSmoothing t (realGaussianSmoothing s f) y = realGaussianSmoothing (t + s) f y := by
  have hSum : heatVariance t + heatVariance s = heatVariance (t + s) := by
    apply NNReal.eq
    rw [NNReal.coe_add, heatVariance_coe ht.le, heatVariance_coe hs.le,
      heatVariance_coe (add_nonneg ht.le hs.le)]
    ring
  have hConv : (gaussianReal y (heatVariance t)) ∗ (gaussianReal 0 (heatVariance s)) =
      gaussianReal y (heatVariance (t + s)) := by
    rw [gaussianReal_conv_gaussianReal, add_zero, hSum]
  have hInt : Integrable f ((gaussianReal y (heatVariance t)) ∗ (gaussianReal 0 (heatVariance s))) := by
    rw [hConv]
    exact integrable_gaussianReal_of_integrable hf y (heatVariance_ne_zero (add_pos ht hs))
  have hInner (x : ℝ) :
      (∫ z, f (x + z) ∂(gaussianReal 0 (heatVariance s))) = realGaussianSmoothing s f x := by
    have hMap :
        (gaussianReal 0 (heatVariance s)).map (fun z => x + z) = gaussianReal x (heatVariance s) := by
      simpa only [zero_add] using gaussianReal_map_const_add (μ := (0 : ℝ)) (v := heatVariance s) x
    have hMeas : AEStronglyMeasurable f ((gaussianReal 0 (heatVariance s)).map (fun z => x + z)) := by
      rw [hMap]
      exact (integrable_gaussianReal_of_integrable hf x (heatVariance_ne_zero hs)).aestronglyMeasurable
    rw [realGaussianSmoothing_eq_integral_gaussianReal hs, ← hMap]
    exact (integral_map (show Measurable (fun z : ℝ => x + z) by fun_prop).aemeasurable hMeas).symm
  rw [realGaussianSmoothing_eq_integral_gaussianReal ht,
    realGaussianSmoothing_eq_integral_gaussianReal (add_pos ht hs), ← hConv, integral_conv hInt]
  exact integral_congr_ae (Eventually.of_forall fun x => (hInner x).symm)

/-- Gaussian smoothing is jointly continuous in positive heat parameter
and physical position for an integrable real density. -/
theorem continuousOn_realGaussianSmoothing_of_integrable {f : ℝ → ℝ} (hf : Integrable f volume) :
    ContinuousOn (fun p : ℝ × ℝ => realGaussianSmoothing p.1 f p.2) (Ioi 0 ×ˢ univ) := by
  let S : Set (ℝ × ℝ) := Ioi 0 ×ˢ univ
  let F (p : ℝ × ℝ) (x : ℝ) := f x * Real.exp (-((x - p.2) ^ 2) / p.1)
  have hIntegral : ContinuousOn (fun p : ℝ × ℝ => ∫ x, F p x) S := by
    refine continuousOn_of_dominated (F := F) (bound := fun x => ‖f x‖) ?_ ?_ hf.norm ?_
    · intro p hp
      have hW : Continuous (fun x : ℝ => Real.exp (-((x - p.2) ^ 2) / p.1)) := by fun_prop
      exact hf.aestronglyMeasurable.mul hW.aestronglyMeasurable
    · intro p hp
      filter_upwards with x
      change ‖f x * Real.exp (-((x - p.2) ^ 2) / p.1)‖ ≤ ‖f x‖
      rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
      have hExp : Real.exp (-((x - p.2) ^ 2) / p.1) ≤ 1 :=
        Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
          (show 0 < p.1 from hp.1).le)
      exact mul_le_of_le_one_right (norm_nonneg _) hExp
    · filter_upwards with x p hp
      have hp' : 0 < p.1 := hp.1
      have hNum : ContinuousAt (fun q : ℝ × ℝ => -((x - q.2) ^ 2)) p := by fun_prop
      have hExp : ContinuousAt (fun q : ℝ × ℝ => Real.exp (-((x - q.2) ^ 2) / q.1)) p :=
        Real.continuous_exp.continuousAt.comp (hNum.div continuous_fst.continuousAt hp'.ne')
      have hFConst : ContinuousAt (fun _ : ℝ × ℝ => f x) p := continuousAt_const
      exact (hFConst.mul hExp).continuousWithinAt
  have hConstant : ContinuousOn (fun p : ℝ × ℝ => (Real.sqrt (Real.pi * p.1))⁻¹) S := by
    intro p hp
    have hRoot : 0 < Real.sqrt (Real.pi * p.1) := Real.sqrt_pos.2 (mul_pos Real.pi_pos hp.1)
    have h : Continuous (fun p : ℝ × ℝ => Real.sqrt (Real.pi * p.1)) := by fun_prop
    exact (h.continuousAt.inv₀ hRoot.ne').continuousWithinAt
  exact hConstant.mul hIntegral

private theorem map_standardGaussian_heat_affine {t : ℝ} (ht : 0 < t) (y : ℝ) :
    (gaussianReal 0 1).map (fun z => y + Real.sqrt (t / 2) * z) =
      gaussianReal y (heatVariance t) := by
  let c := Real.sqrt (t / 2)
  have hSq : NNReal.mk (c ^ 2) (sq_nonneg c) = heatVariance t := by
    apply NNReal.eq
    rw [NNReal.coe_mk, heatVariance_coe ht.le]
    exact Real.sq_sqrt (by positivity)
  have hScale :
      (gaussianReal 0 1).map (fun z => c * z) = gaussianReal 0 (heatVariance t) := by
    calc
      _ = gaussianReal 0 (NNReal.mk (c ^ 2) (sq_nonneg c)) := by
        simpa only [mul_zero, mul_one] using
          gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) c
      _ = _ := congrArg (gaussianReal 0) hSq
  have hMulMeas : Measurable (fun z : ℝ => c * z) := by fun_prop
  have hAddMeas : Measurable (fun z : ℝ => y + z) := by fun_prop
  calc
    (gaussianReal 0 1).map (fun z => y + c * z) =
        ((gaussianReal 0 1).map (fun z => c * z)).map (fun z => y + z) := by
      rw [Measure.map_map hAddMeas hMulMeas]
      rfl
    _ = gaussianReal y (heatVariance t) := by
      rw [hScale]
      simpa only [zero_add] using
        gaussianReal_map_const_add (μ := (0 : ℝ)) (v := heatVariance t) y

/-- Gaussian smoothing is additive on Lebesgue-integrable real data
at every positive heat parameter. -/
theorem realGaussianSmoothing_fun_add {f g : ℝ → ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    realGaussianSmoothing t (fun x => f x + g x) y =
      realGaussianSmoothing t f y + realGaussianSmoothing t g y := by
  simp only [realGaussianSmoothing_eq_integral_gaussianReal ht]
  exact integral_add (integrable_gaussianReal_of_integrable hf y (heatVariance_ne_zero ht))
    (integrable_gaussianReal_of_integrable hg y (heatVariance_ne_zero ht))

/-- Gaussian smoothing tends to the initial value at a continuity point
of a bounded integrable density, jointly in positive time and position. -/
theorem tendsto_realGaussianSmoothing_initial_of_bounded_integrable
    {f : ℝ → ℝ} (hf : Integrable f volume) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C)
    (y : ℝ) (hy : ContinuousAt f y) :
    Tendsto (fun p : ℝ × ℝ => realGaussianSmoothing p.1 f p.2)
      (𝓝[Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)] (0, y)) (𝓝 (f y)) := by
  let S : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)
  let l := 𝓝[S] (0, y)
  let μ : Measure ℝ := gaussianReal 0 1
  let F (p : ℝ × ℝ) (z : ℝ) := p.2 + Real.sqrt (p.1 / 2) * z
  have hF (p : ℝ × ℝ) : Measurable (F p) := by unfold F; fun_prop
  have hMap (p : ℝ × ℝ) (hp : p ∈ S) :
      μ.map (F p) = gaussianReal p.2 (heatVariance p.1) :=
    map_standardGaussian_heat_affine hp.1 p.2
  have hMeas (p : ℝ × ℝ) (hp : p ∈ S) : AEStronglyMeasurable f (μ.map (F p)) := by
    rw [hMap p hp]
    exact (integrable_gaussianReal_of_integrable hf p.2 (heatVariance_ne_zero hp.1)).aestronglyMeasurable
  have hConv (z : ℝ) : Tendsto (fun p => f (F p z)) l (𝓝 (f y)) := by
    have hFz : Continuous (fun p : ℝ × ℝ => F p z) := by unfold F; fun_prop
    have hAt : Tendsto (fun p : ℝ × ℝ => F p z) l (𝓝 y) := by
      have h := (hFz.continuousAt (x := ((0 : ℝ), y))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := S))
      simpa only [F, zero_div, Real.sqrt_zero, zero_mul, add_zero] using h
    simpa only [Function.comp_def] using hy.tendsto.comp hAt
  let _ : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))
  have hPos : ∀ᶠ p in l, p ∈ S := self_mem_nhdsWithin
  have hInt : Tendsto (fun p : ℝ × ℝ => ∫ z, f (F p z) ∂μ) l (𝓝 (f y)) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (l := l) (F := fun p z => f (F p z)) (f := fun _ => f y) (fun _ => C)
      (hPos.mono fun p hp =>
        (hMeas p hp).comp_aemeasurable (hF p).aemeasurable)
      (Eventually.of_forall fun p => Eventually.of_forall fun z => hC (F p z))
      (integrable_const C) (Eventually.of_forall hConv)
    simpa using h
  refine hInt.congr' ?_
  filter_upwards [self_mem_nhdsWithin (s := S)] with p hp
  rw [← integral_map (hF p).aemeasurable (hMeas p hp), hMap p hp,
    realGaussianSmoothing_eq_integral_gaussianReal hp.1]

end
end MeyerGeneralProblem
