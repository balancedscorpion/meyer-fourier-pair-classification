module

public import MeyerGeneralProblem.Sampling.KNSGaussianDecay
public import MeyerGeneralProblem.Sampling.PaleyWienerRepresentative
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

/-!
# Actual entire Fourier integrals from Gaussian square integrability

The existing complex Fourier integral is used without a support condition.
Gaussian domination supplies its integrability, differentiation, and a
quadratic bound in the imaginary coordinate. No pointwise decay or entire
extension is assumed for the input function.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Filter
open scoped Topology FourierTransform

private theorem gaussian_linear_young {a : ℝ} (ha : 0 < a) (b x r : ℝ) (hr : 0 ≤ r) :
    r*Real.exp (b*|x|) ≤ Real.exp (a*x^2)*r^2 +
      Real.exp (2*b^2/a)*Real.exp (-(a/2)*x^2) := by
  let U := r*Real.exp (a*x^2/2)
  let V := Real.exp (-a*x^2/2+b*|x|)
  have hU : U^2 = Real.exp (a*x^2)*r^2 := by
    dsimp only [U]
    rw [mul_pow]
    have he : Real.exp (a*x^2/2)^2=Real.exp (a*x^2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    rw [he,mul_comm]
  have hV : V^2 = Real.exp (-a*x^2+2*b*|x|) := by
    dsimp only [V]
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hUV : U*V = r*Real.exp (b*|x|) := by
    dsimp only [U,V]
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring
  have hquad : -a*x^2+2*b*|x| ≤ 2*b^2/a-(a/2)*x^2 := by
    have hs := sq_nonneg (a*|x|-2*b)
    have he : a*(2*b^2/a)=2*b^2 := by field_simp
    ring_nf at hs
    rw [show |x|^2=x^2 from sq_abs x] at hs
    apply (mul_le_mul_iff_right₀ ha).mp
    nlinarith
  have hVbound : V^2 ≤ Real.exp (2*b^2/a)*Real.exp (-(a/2)*x^2) := by
    rw [hV,← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hyoung := sq_nonneg (U-V)
  have hUV0 : 0 ≤ U*V := by dsimp only [U,V]; positivity
  nlinarith [hU,hUV]

/-- Every linear exponential weight is integrable against the norm of
Gaussian-square-integrable data; measurability of the actual complex data
is the only additional requirement. -/
theorem integrable_norm_mul_exp_abs_of_gaussian {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hgauss : Integrable (fun x => Real.exp (a*x^2)*‖f x‖^2)) (b : ℝ) :
    Integrable (fun x => ‖f x‖*Real.exp (b*|x|)) := by
  have hg := hgauss.add ((integrable_exp_neg_mul_sq (by positivity : 0 < a/2)).const_mul
    (Real.exp (2*b^2/a)))
  apply hg.mono' (hf.norm.mul (show Continuous (fun x : ℝ => Real.exp (b*|x|)) by
    fun_prop).aestronglyMeasurable)
  filter_upwards [] with x
  simp only [Pi.mul_apply,Pi.add_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
  exact gaussian_linear_young ha b x ‖f x‖ (norm_nonneg _)

/-- The same elementary Gaussian domination yields an explicit integral
bound for every linear exponential weight. -/
theorem integral_norm_mul_exp_abs_le_of_gaussian {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hgauss : Integrable (fun x => Real.exp (a*x^2)*‖f x‖^2)) (b : ℝ) :
    (∫ x, ‖f x‖*Real.exp (b*|x|)) ≤
      ((∫ x, Real.exp (a*x^2)*‖f x‖^2)+Real.sqrt (2*Real.pi/a))*
        Real.exp (2*b^2/a) := by
  have hg := (integrable_exp_neg_mul_sq (by positivity : 0 < a/2)).const_mul
    (Real.exp (2*b^2/a))
  have h := integral_mono (integrable_norm_mul_exp_abs_of_gaussian ha hf hgauss b)
    (hgauss.add hg) (fun x => gaussian_linear_young ha b x ‖f x‖ (norm_nonneg _))
  simp only [Pi.add_apply] at h
  rw [integral_add hgauss hg,integral_const_mul,integral_gaussian] at h
  have he : Real.pi/(a/2)=2*Real.pi/a := by ring
  rw [he] at h
  have hE : 0 ≤ ∫ x, Real.exp (a*x^2)*‖f x‖^2 :=
    integral_nonneg (fun x => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  have h1 : 1 ≤ Real.exp (2*b^2/a) := Real.one_le_exp (by positivity)
  have hh := mul_le_mul_of_nonneg_right h1 hE
  nlinarith

/-- Gaussian square integrability in particular implies genuine L1
integrability of the actual measurable complex function. -/
theorem integrable_of_gaussian_square {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hgauss : Integrable (fun x => Real.exp (a*x^2)*‖f x‖^2)) : Integrable f := by
  apply (integrable_norm_iff hf).mp
  simpa only [zero_mul,Real.exp_zero,mul_one] using
    integrable_norm_mul_exp_abs_of_gaussian ha hf hgauss 0

/-- The negative Fourier phase has positive imaginary-direction growth
`exp(2*pi*x*Im(z))`; this fixes both its sign and its normalization. -/
theorem norm_knsFourierLaplace_phase (x : ℝ) (z : ℂ) :
    ‖Complex.exp (((-2*Real.pi*x : ℝ) : ℂ)*Complex.I*z)‖ =
      Real.exp (2*Real.pi*x*z.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im]
  ring

private theorem norm_knsFourierLaplace_phase_le (x : ℝ) (z : ℂ) :
    ‖Complex.exp (((-2*Real.pi*x : ℝ) : ℂ)*Complex.I*z)‖ ≤
      Real.exp ((2*Real.pi*|z.im|)*|x|) := by
  rw [norm_knsFourierLaplace_phase]
  apply Real.exp_le_exp.mpr
  have h := le_abs_self (x*z.im)
  rw [abs_mul] at h
  nlinarith [Real.pi_pos]

/-- The actual Fourier-Laplace integrand is integrable at every complex
argument under Gaussian square integrability. -/
theorem integrable_knsFourierLaplace_integrand {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hgauss : Integrable (fun x => Real.exp (a*x^2)*‖f x‖^2)) (z : ℂ) :
    Integrable (fun x : ℝ =>
      Complex.exp (((-2*Real.pi*x : ℝ) : ℂ)*Complex.I*z)*f x) := by
  apply (integrable_norm_mul_exp_abs_of_gaussian ha hf hgauss (2*Real.pi*|z.im|)).mono'
    ((show Continuous (fun x : ℝ =>
      Complex.exp (((-2*Real.pi*x : ℝ) : ℂ)*Complex.I*z)) by
        fun_prop).aestronglyMeasurable.mul hf)
  filter_upwards [] with x
  simp only [Pi.mul_apply,norm_mul]
  have h := mul_le_mul_of_nonneg_right (norm_knsFourierLaplace_phase_le x z) (norm_nonneg (f x))
  nlinarith

/-- A completely explicit quadratic imaginary-direction bound for the
actual Fourier-Laplace integral. Its constant is the Gaussian square mass
plus a Gaussian integral, not an assumed growth certificate. -/
theorem norm_knsFourierLaplace_le_quadratic {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hgauss : Integrable (fun x => Real.exp (a*x^2)*‖f x‖^2)) (z : ℂ) :
    ‖bandFourierExtension f z‖ ≤
      ((∫ x, Real.exp (a*x^2)*‖f x‖^2)+Real.sqrt (2*Real.pi/a))*
        Real.exp ((8*Real.pi^2/a)*z.im^2) := by
  have hpoint (x : ℝ) :
      ‖Complex.exp (((-2*Real.pi*x : ℝ) : ℂ)*Complex.I*z)*f x‖ ≤
        ‖f x‖*Real.exp ((2*Real.pi*|z.im|)*|x|) := by
    rw [norm_mul]
    have h := mul_le_mul_of_nonneg_right (norm_knsFourierLaplace_phase_le x z) (norm_nonneg (f x))
    nlinarith
  have h := (norm_integral_le_integral_norm _).trans
    (integral_mono (integrable_knsFourierLaplace_integrand ha hf hgauss z).norm
      (integrable_norm_mul_exp_abs_of_gaussian ha hf hgauss (2*Real.pi*|z.im|)) hpoint)
  have hb := integral_norm_mul_exp_abs_le_of_gaussian ha hf hgauss (2*Real.pi*|z.im|)
  have he : 2*(2*Real.pi*|z.im|)^2/a=(8*Real.pi^2/a)*z.im^2 := by
    rw [mul_pow,mul_pow,sq_abs]
    ring
  rw [he] at hb
  exact h.trans hb

private theorem abs_mul_exp_le_exp (b x : ℝ) :
    |x| * Real.exp (b*|x|) ≤ Real.exp ((b+1)*|x|) := by
  have h : |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
  calc
    _ ≤ Real.exp |x| * Real.exp (b*|x|) :=
      mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Genuine complex differentiation under the Gaussian-dominated Fourier
integral, with the exact negative `2*pi*i*x` derivative multiplier. -/
theorem hasDerivAt_knsFourierLaplace {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hgauss : Integrable (fun x => Real.exp (a*x^2)*‖f x‖^2)) (z : ℂ) :
    HasDerivAt (bandFourierExtension f)
      (∫ x : ℝ, (Complex.exp (((-2*Real.pi*x : ℝ) : ℂ)*Complex.I*z)*
        (((-2*Real.pi*x : ℝ) : ℂ)*Complex.I))*f x) z := by
  let c : ℝ → ℂ := fun x => ((-2*Real.pi*x : ℝ) : ℂ)*Complex.I
  let F : ℂ → ℝ → ℂ := fun w x => Complex.exp (c x*w)*f x
  let F' : ℂ → ℝ → ℂ := fun w x => (Complex.exp (c x*w)*c x)*f x
  let B : ℝ := 2*Real.pi*(‖z‖+1)
  have hFm (w : ℂ) : AEStronglyMeasurable (F w) volume :=
    (show Continuous (fun x : ℝ => Complex.exp (c x*w)) by dsimp [c]; fun_prop
      ).aestronglyMeasurable.mul hf
  have hF'm (w : ℂ) : AEStronglyMeasurable (F' w) volume :=
    (show Continuous (fun x : ℝ => Complex.exp (c x*w)*c x) by dsimp [c]; fun_prop
      ).aestronglyMeasurable.mul hf
  have hdiff (x : ℝ) (w : ℂ) : HasDerivAt (fun t => F t x) (F' w x) w := by
    simpa only [F,F',mul_one,id_eq] using
      (((hasDerivAt_id w).const_mul (c x)).cexp.mul_const (f x))
  have hbound : ∀ᵐ x : ℝ, ∀ w ∈ Metric.ball z 1,
      ‖F' w x‖ ≤ (2*Real.pi)*(‖f x‖*Real.exp ((B+1)*|x|)) := by
    filter_upwards [] with x w hw
    have hw' : ‖w‖ ≤ ‖z‖+1 := by
      have ht := norm_le_norm_sub_add w z
      have hh : ‖w-z‖ < 1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hw
      linarith
    have him : |w.im| ≤ ‖z‖+1 := (Complex.abs_im_le_norm w).trans hw'
    have he : ‖Complex.exp (c x*w)‖ ≤ Real.exp (B*|x|) := by
      apply (norm_knsFourierLaplace_phase_le x w).trans
      dsimp only [B]
      gcongr
    have hc : ‖c x‖ = 2*Real.pi*|x| := by
      dsimp only [c]
      simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    have hpol := abs_mul_exp_le_exp B x
    dsimp only [F']
    rw [norm_mul,norm_mul,hc]
    calc
      _ ≤ Real.exp (B*|x|)*(2*Real.pi*|x|)*‖f x‖ := by gcongr
      _ = (2*Real.pi)*(‖f x‖*(|x| * Real.exp (B*|x|))) := by ring
      _ ≤ _ := by gcongr
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun x => (2*Real.pi)*(‖f x‖*Real.exp ((B+1)*|x|)))
    (Metric.ball_mem_nhds z zero_lt_one) (Eventually.of_forall hFm)
    (integrable_knsFourierLaplace_integrand ha hf hgauss z) (hF'm z) hbound
    ((integrable_norm_mul_exp_abs_of_gaussian ha hf hgauss (B+1)).const_mul (2*Real.pi))
    (Eventually.of_forall fun x w _ => hdiff x w)
  exact h.2

/-- The actual Fourier-Laplace integral is entire under a positive Gaussian
square weight, even when the input data are merely measurable. -/
theorem differentiable_knsFourierLaplace {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hgauss : Integrable (fun x => Real.exp (a*x^2)*‖f x‖^2)) :
    Differentiable ℂ (bandFourierExtension f) :=
  fun z => (hasDerivAt_knsFourierLaplace ha hf hgauss z).differentiableAt

/-- The proved entire integral is analytic at every complex point, with
the ordinary Fourier transform as its exact real-axis restriction. -/
theorem analytic_knsFourierLaplace_ofReal {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hgauss : Integrable (fun x => Real.exp (a*x^2)*‖f x‖^2)) :
    (∀ z : ℂ, AnalyticAt ℂ (bandFourierExtension f) z) ∧
      (∀ t : ℝ, bandFourierExtension f (t : ℂ) = (𝓕 f) t) :=
  ⟨(differentiable_knsFourierLaplace ha hf hgauss).analyticAt,bandFourierExtension_ofReal f⟩

/-- The actual Fourier integral is an entire extension with finite quadratic
type and a positive bound constant. The type coefficient depends only on
the given Gaussian exponent; the bound constant may depend on the data. -/
theorem knsGaussian_fourier_entire {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hgauss : Integrable (fun x => Real.exp (a*x^2)*‖f x‖^2)) :
    Differentiable ℂ (bandFourierExtension f) ∧
      (∀ t : ℝ, bandFourierExtension f (t : ℂ) = (𝓕 f) t) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
        ‖bandFourierExtension f z‖ ≤ C*Real.exp ((8*Real.pi^2/a)*z.im^2) := by
  refine ⟨differentiable_knsFourierLaplace ha hf hgauss,bandFourierExtension_ofReal f,
    (∫ x, Real.exp (a*x^2)*‖f x‖^2)+Real.sqrt (2*Real.pi/a),?_,
    norm_knsFourierLaplace_le_quadratic ha hf hgauss⟩
  have hE : 0 ≤ ∫ x, Real.exp (a*x^2)*‖f x‖^2 :=
    integral_nonneg (fun x => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  have hs : 0 < Real.sqrt (2*Real.pi/a) := Real.sqrt_pos.mpr (by positivity)
  linarith

end

end MeyerGeneralProblem
