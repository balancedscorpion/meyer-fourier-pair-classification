module

public import MeyerGeneralProblem.Distribution.GaussianHeatSemigroup
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-!
# Fourier representation of the Gaussian heat flow

The positive-time heat flow is an integrable Gaussian convolution. Its
ordinary Fourier transform is the original transform times a strictly
positive Gaussian, so it has exactly the original Fourier gap.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ComplexConjugate Convolution FourierTransform NNReal Topology

private theorem heatGaussianVariance_coe {t : ℝ} (ht : 0 < t) :
    (((t / 2).toNNReal : ℝ≥0) : ℝ) = t / 2 := by
  rw [Real.coe_toNNReal', max_eq_left (by positivity)]

private theorem heatGaussianVariance_ne_zero {t : ℝ} (ht : 0 < t) :
    (t / 2).toNNReal ≠ 0 := by
  intro h
  have he := heatGaussianVariance_coe ht
  rw [h, NNReal.coe_zero] at he
  linarith

private theorem fourier_gaussianPDFReal_heat {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (gaussianPDFReal 0 (t / 2).toNNReal x : ℂ)) ξ =
      (Real.exp (-(Real.pi ^ 2 * t) * ξ ^ 2) : ℂ) := by
  let v := (t / 2).toNNReal
  calc
    _ = charFun (gaussianReal 0 v) (-2 * Real.pi * ξ) := by
      rw [Real.fourier_real_eq_integral_exp_smul, charFun_apply_real,
        integral_gaussianReal_eq_integral_smul (heatGaussianVariance_ne_zero ht)]
      apply integral_congr_ae
      filter_upwards with x
      have h : -2 * Real.pi * x * ξ = (-2 * Real.pi * ξ) * x := by ring
      rw [h]
      simp [smul_eq_mul, mul_comm]
    _ = _ := by
      rw [charFun_gaussianReal, Complex.ofReal_exp]
      congr 1
      push_cast
      rw [show (v : ℝ) = t / 2 from heatGaussianVariance_coe ht]
      push_cast
      ring

private theorem ofReal_realGaussianSmoothing_eq_convolution {t : ℝ} (ht : 0 < t)
    (f : ℝ → ℝ) :
    (fun y : ℝ => (realGaussianSmoothing t f y : ℂ)) =
      (fun x : ℝ => (f x : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (fun x : ℝ => (gaussianPDFReal 0 (t / 2).toNNReal x : ℂ)) := by
  funext y
  rw [convolution_def, realGaussianSmoothing, ← integral_const_mul,
    ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with x
  have hSq : (y - x) ^ 2 = (x - y) ^ 2 := by ring
  simp only [ContinuousLinearMap.mul_apply', gaussianPDFReal, sub_zero,
    heatGaussianVariance_coe ht, hSq, ← Complex.ofReal_mul]
  congr 1
  rw [show 2 * Real.pi * (t / 2) = Real.pi * t by ring, show 2 * (t / 2) = t by ring]
  ring

/-- Positive-time Gaussian smoothing preserves Lebesgue integrability. -/
theorem integrable_realGaussianSmoothing {f : ℝ → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) : Integrable (realGaussianSmoothing t f) := by
  have h : Integrable (fun y : ℝ => (realGaussianSmoothing t f y : ℂ)) := by
    rw [ofReal_realGaussianSmoothing_eq_convolution ht f]
    exact hf.ofReal.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ)
      (integrable_gaussianPDFReal 0 (t / 2).toNNReal).ofReal
  simpa only [Complex.reCLM_apply, Complex.ofReal_re] using Complex.reCLM.integrable_comp h

/-- The normalized Gaussian heat flow does not increase the L¹ norm. -/
theorem integral_norm_realGaussianSmoothing_le {f : ℝ → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) :
    (∫ y : ℝ, ‖realGaussianSmoothing t f y‖) ≤ ∫ x : ℝ, ‖f x‖ := by
  let g := gaussianPDFReal 0 (t / 2).toNNReal
  have hg := integrable_gaussianPDFReal 0 (t / 2).toNNReal
  have hMass : (∫ x : ℝ, g x) = 1 :=
    integral_gaussianPDFReal_eq_one 0 (heatGaussianVariance_ne_zero ht)
  have hConv : realGaussianSmoothing t (fun x => ‖f x‖) =
      (fun x : ℝ => ‖f x‖) ⋆[ContinuousLinearMap.mul ℝ ℝ] g := by
    funext y
    have he := congrArg Complex.re (congrFun
      (ofReal_realGaussianSmoothing_eq_convolution ht (fun x => ‖f x‖)) y)
    rw [Complex.ofReal_re, convolution_def] at he
    simp only [ContinuousLinearMap.mul_apply', ← Complex.ofReal_mul, integral_complex_ofReal,
      Complex.ofReal_re] at he
    rw [convolution_def, he]
    rfl
  have hPos (y : ℝ) : ‖realGaussianSmoothing t f y‖ ≤
      realGaussianSmoothing t (fun x => ‖f x‖) y := by
    rw [realGaussianSmoothing, realGaussianSmoothing,
      norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ (Real.sqrt (Real.pi * t))⁻¹)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    apply integral_congr_ae
    filter_upwards with x
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ ∫ y : ℝ, realGaussianSmoothing t (fun x => ‖f x‖) y :=
      integral_mono (integrable_realGaussianSmoothing hf ht).norm
        (integrable_realGaussianSmoothing hf.norm ht) hPos
    _ = _ := by
      rw [hConv, integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hf.norm hg, hMass,
        ContinuousLinearMap.mul_apply', mul_one]

/-- In the negative 2π convention, heat time t gives the multiplier
exp (-π² t ξ²). -/
theorem fourier_realGaussianSmoothing {f : ℝ → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    𝓕 (fun y : ℝ => (realGaussianSmoothing t f y : ℂ)) ξ =
      𝓕 (fun x : ℝ => (f x : ℂ)) ξ * (Real.exp (-(Real.pi ^ 2 * t) * ξ ^ 2) : ℂ) := by
  rw [ofReal_realGaussianSmoothing_eq_convolution ht f, ← fourier_gaussianPDFReal_heat ht]
  exact Real.fourier_mul_convolution_eq (R := ℂ) hf.ofReal
    (integrable_gaussianPDFReal 0 (t / 2).toNNReal).ofReal ξ

/-- Gaussian smoothing neither creates nor removes zeros of the ordinary
Fourier transform, including throughout any centered gap. -/
theorem fourier_realGaussianSmoothing_eq_zero_iff {f : ℝ → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    𝓕 (fun y : ℝ => (realGaussianSmoothing t f y : ℂ)) ξ = 0 ↔
      𝓕 (fun x : ℝ => (f x : ℂ)) ξ = 0 := by
  rw [fourier_realGaussianSmoothing hf ht, mul_eq_zero]
  have hNonzero : (Real.exp (-(Real.pi ^ 2 * t) * ξ ^ 2) : ℂ) ≠ 0 := by
    exact_mod_cast Real.exp_ne_zero _
  exact or_iff_left (fun h => (hNonzero h).elim)

/-- The ordinary Fourier transform of an integrable real density is
bounded by its L¹ norm. -/
theorem norm_fourier_ofReal_le_integral_norm (f : ℝ → ℝ) (ξ : ℝ) :
    ‖𝓕 (fun x : ℝ => (f x : ℂ)) ξ‖ ≤ ∫ x : ℝ, ‖f x‖ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply integral_congr_ae
  filter_upwards with x
  simp [smul_eq_mul, Complex.norm_exp]

/-- The Fourier transform of the heated density is dominated by its
original L¹ norm times the Gaussian multiplier. -/
theorem norm_fourier_realGaussianSmoothing_le {f : ℝ → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    ‖𝓕 (fun y : ℝ => (realGaussianSmoothing t f y : ℂ)) ξ‖ ≤
      (∫ x : ℝ, ‖f x‖) * Real.exp (-(Real.pi ^ 2 * t) * ξ ^ 2) := by
  rw [fourier_realGaussianSmoothing hf ht, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (norm_fourier_ofReal_le_integral_norm f ξ) (Real.exp_pos _).le

private theorem continuous_fourier_realGaussianSmoothing {f : ℝ → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) :
    Continuous (𝓕 (fun y : ℝ => (realGaussianSmoothing t f y : ℂ))) := by
  have hF : Integrable (fun y : ℝ => (realGaussianSmoothing t f y : ℂ)) :=
    (integrable_realGaussianSmoothing hf ht).ofReal
  have hInner : Continuous fun p : ℝ × ℝ => inner ℝ p.1 p.2 :=
    (innerSL ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).continuous₂
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar hInner hF

/-- Gaussian decay makes the ordinary Fourier transform of the heated
density integrable, even when the original transform is only bounded. -/
theorem integrable_fourier_realGaussianSmoothing {f : ℝ → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) :
    Integrable (𝓕 (fun y : ℝ => (realGaussianSmoothing t f y : ℂ))) := by
  have hG := (integrable_exp_neg_mul_sq (by positivity : 0 < Real.pi ^ 2 * t)).const_mul
    (∫ x : ℝ, ‖f x‖)
  exact hG.mono' (continuous_fourier_realGaussianSmoothing hf ht).aestronglyMeasurable
    (ae_of_all _ (norm_fourier_realGaussianSmoothing_le hf ht))

/-- Positive-frequency Fourier–Laplace integral of the heat flow. The cutoff
s is allowed to sit at the edge of a centered Fourier gap. -/
def heatFourierLaplace (t : ℝ) (f : ℝ → ℝ) (s : ℝ) (z : ℂ) : ℂ :=
  ∫ ξ in Ioi s, (𝓕 (fun y : ℝ => (realGaussianSmoothing t f y : ℂ))) ξ *
    Complex.exp ((↑(2 * Real.pi * ξ) * Complex.I) * z)

private theorem norm_heatFourierLaplace_integrand_le {f : ℝ → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) (z : ℂ) (ξ : ℝ) {B : ℝ} (hB : |z.im| ≤ B) :
    ‖(𝓕 (fun y : ℝ => (realGaussianSmoothing t f y : ℂ))) ξ *
      Complex.exp ((↑(2 * Real.pi * ξ) * Complex.I) * z)‖ ≤
      ((∫ x : ℝ, ‖f x‖) * Real.exp ((2 * Real.pi * B) ^ 2 / (2 * (Real.pi ^ 2 * t)))) *
        Real.exp (-(Real.pi ^ 2 * t / 2) * ξ ^ 2) := by
  let a := Real.pi ^ 2 * t
  let b := 2 * Real.pi * B
  have ha : 0 < a := by dsimp [a]; positivity
  have hre : (((↑(2 * Real.pi * ξ) : ℂ) * Complex.I) * z).re ≤ b * |ξ| := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, zero_sub, mul_one, add_zero]
    calc
      -(2 * Real.pi * ξ * z.im) ≤ |2 * Real.pi * ξ * z.im| := neg_le_abs _
      _ = (2 * Real.pi) * |ξ| * |z.im| := by
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      _ ≤ b * |ξ| := by
        dsimp [b]
        calc
          _ ≤ 2 * Real.pi * |ξ| * B :=
            mul_le_mul_of_nonneg_left hB (by positivity)
          _ = _ := by ring
  have hsq : b * |ξ| - a / 2 * ξ ^ 2 ≤ b ^ 2 / (2 * a) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * a)).2
    calc
      _ = b ^ 2 - (a * |ξ| - b) ^ 2 := by
        simp only [sub_sq, mul_pow, sq_abs]
        ring
      _ ≤ b ^ 2 := sub_le_self _ (sq_nonneg _)
  rw [norm_mul, Complex.norm_exp]
  refine (mul_le_mul_of_nonneg_right (norm_fourier_realGaussianSmoothing_le hf ht ξ)
    (Real.exp_pos _).le).trans ?_
  simp only [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (integral_nonneg fun _ => norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hre' : ((↑(2 * Real.pi * ξ) : ℂ) * (Complex.I * z)).re ≤ b * |ξ| := by
    simpa only [mul_assoc] using hre
  dsimp only [a, b] at hre' hsq
  simp only [mul_assoc] at hre' hsq
  linarith only [hre', hsq]

/-- The positive-frequency Fourier–Laplace integral is entire at each positive
heat time. Gaussian decay dominates the integral and its derivative locally
throughout the complex plane. -/
theorem differentiable_heatFourierLaplace {f : ℝ → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) (s : ℝ) : Differentiable ℂ (heatFourierLaplace t f s) := by
  intro z
  let B := |z.im| + 1
  let a := Real.pi ^ 2 * t
  let C := (∫ x : ℝ, ‖f x‖) * Real.exp ((2 * Real.pi * B) ^ 2 / (2 * a))
  let D (ξ : ℝ) : ℂ := ↑(2 * Real.pi * ξ) * Complex.I
  let F : ℝ → ℂ := 𝓕 (fun y : ℝ => (realGaussianSmoothing t f y : ℂ))
  let K (w : ℂ) (ξ : ℝ) : ℂ := F ξ * Complex.exp (D ξ * w)
  let L (w : ℂ) (ξ : ℝ) : ℂ := K w ξ * D ξ
  have ha : 0 < a := by dsimp [a]; positivity
  have hSide {w : ℂ} (hw : w ∈ Metric.ball z 1) : |w.im| ≤ B := by
    have hDist := Metric.mem_ball.mp hw
    rw [dist_eq_norm] at hDist
    have hIm : |w.im - z.im| ≤ ‖w - z‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (w - z)
    dsimp [B]
    calc
      _ = |(w.im - z.im) + z.im| := by ring_nf
      _ ≤ |w.im - z.im| + |z.im| := abs_add_le _ _
      _ ≤ _ := by linarith only [hIm, hDist]
  have hK (w : ℂ) : Continuous (K w) := by
    unfold K D
    exact (continuous_fourier_realGaussianSmoothing hf ht).mul (by fun_prop)
  have hL (w : ℂ) : Continuous (L w) := (hK w).mul (by unfold D; fun_prop)
  have hBound {w : ℂ} (hw : w ∈ Metric.ball z 1) (ξ : ℝ) :
      ‖K w ξ‖ ≤ C * Real.exp (-(a / 2) * ξ ^ 2) :=
    norm_heatFourierLaplace_integrand_le hf ht w ξ (hSide hw)
  have hKInt : Integrable (K z) (volume.restrict (Ioi s)) :=
    ((integrable_exp_neg_mul_sq (half_pos ha)).const_mul C).integrableOn.mono'
      (hK z).aestronglyMeasurable
      (ae_of_all _ (hBound (Metric.mem_ball_self zero_lt_one)))
  have hNormD (ξ : ℝ) : ‖D ξ‖ = (2 * Real.pi) * |ξ| := by
    simp [D, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hDom : Integrable (fun ξ : ℝ => (C * (2 * Real.pi)) *
      (|ξ| * Real.exp (-(a / 2) * ξ ^ 2))) (volume.restrict (Ioi s)) := by
    have h := (integrable_mul_exp_neg_mul_sq (half_pos ha)).norm
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] at h
    exact (h.const_mul (C * (2 * Real.pi))).integrableOn
  have hDeriv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi s)) (F := K) (F' := L)
    (Metric.ball_mem_nhds z zero_lt_one)
    (Filter.Eventually.of_forall fun w => (hK w).aestronglyMeasurable)
    hKInt (hL z).aestronglyMeasurable
    (ae_of_all _ fun ξ w hw => by
      change ‖K w ξ * D ξ‖ ≤ _
      rw [norm_mul, hNormD]
      calc
        _ ≤ (C * Real.exp (-(a / 2) * ξ ^ 2)) * ((2 * Real.pi) * |ξ|) :=
          mul_le_mul_of_nonneg_right (hBound hw ξ) (by positivity)
        _ = _ := by ring)
    hDom (ae_of_all _ fun ξ w _ => by
      simpa only [K, L, id_eq, mul_one, mul_comm (D ξ) (Complex.exp (D ξ * w)), mul_assoc] using
        (((hasDerivAt_id w).const_mul (D ξ)).cexp.const_mul (F ξ)))).2
  exact hDeriv.differentiableAt

/-- The ordinary Fourier transform of a real density has conjugate
symmetry across frequency zero. -/
theorem fourier_ofReal_neg_eq_conj (f : ℝ → ℝ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (f x : ℂ)) (-ξ) =
      conj (𝓕 (fun x : ℝ => (f x : ℂ)) ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
  congr 2
  push_cast
  ring

/-- On the real line the positive-frequency integral plus its conjugate
recovers the original heated density. The centered gap allows the integral
to begin at its positive edge. -/
theorem ofReal_realGaussianSmoothing_eq_heatFourierLaplace_add_conj
    {f : ℝ → ℝ} (hf : Integrable f) {t : ℝ} (ht : 0 < t)
    {s : ℝ} (hs : 0 ≤ s)
    (hGap : EqOn (𝓕 (fun y : ℝ => (f y : ℂ))) 0 (Ioo (-s) s)) (x : ℝ) :
    (realGaussianSmoothing t f x : ℂ) =
      heatFourierLaplace t f s x + conj (heatFourierLaplace t f s x) := by
  let g := realGaussianSmoothing t f
  let F : ℝ → ℂ := 𝓕 (fun y : ℝ => (g y : ℂ))
  let K : ℝ → ℂ := fun ξ => F ξ * Complex.exp ((↑(2 * Real.pi * ξ) * Complex.I) * x)
  have hgCont : Continuous g := by
    have hMap : Continuous (fun y : ℝ => (t, y)) := by fun_prop
    exact (continuousOn_realGaussianSmoothing_of_integrable hf).comp_continuous hMap
      (fun _ => ⟨ht, mem_univ _⟩)
  have hFInt : Integrable F := integrable_fourier_realGaussianSmoothing hf ht
  have hInv : (𝓕⁻ F) x = (g x : ℂ) := congrFun
    ((Complex.continuous_ofReal.comp hgCont).fourierInv_fourier_eq
      (integrable_realGaussianSmoothing hf ht).ofReal hFInt) x
  have hNorm (ξ : ℝ) :
      ‖Complex.exp ((↑(2 * Real.pi * ξ) * Complex.I) * x)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im]
  have hKInt : Integrable K := hFInt.norm.mono'
    ((continuous_fourier_realGaussianSmoothing hf ht).mul
      (show Continuous (fun ξ : ℝ => Complex.exp ((↑(2 * Real.pi * ξ) * Complex.I) * x)) by
        fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun ξ => by simp only [K, norm_mul, hNorm, mul_one, le_rfl])
  have hKInv : (𝓕⁻ F) x = ∫ ξ : ℝ, K ξ := by
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with ξ
    simp only [K, Real.inner_apply, smul_eq_mul]
    rw [mul_comm _ (F ξ)]
    congr 2
    push_cast
    ring
  have hLeft : (∫ ξ in Iic s, K ξ) = ∫ ξ in Iic (-s), K ξ := by
    rw [← Iic_union_Ioc_eq_Iic (neg_le_self hs)]
    apply integral_union_eq_left_of_ae
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with ξ hξ
    dsimp [K, F, g]
    rw [(fourier_realGaussianSmoothing_eq_zero_iff hf ht ξ).mpr (hGap hξ), zero_mul]
  have hReflection : (∫ ξ in Iic (-s), K ξ) = conj (∫ ξ in Ioi s, K ξ) := by
    rw [← integral_comp_neg_Ioi, ← integral_conj]
    refine setIntegral_congr_fun measurableSet_Ioi fun ξ _ => ?_
    simp only [K, map_mul, ← Complex.exp_conj]
    rw [show F (-ξ) = conj (F ξ) from fourier_ofReal_neg_eq_conj g ξ]
    congr 2
    simp only [Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [← hInv, hKInv, ← integral_add_compl measurableSet_Ioi hKInt, compl_Ioi, hLeft,
    hReflection]
  rfl

/-- The positive-frequency integral above any finite cutoff is exactly a
Cauchy integral in the upper half-plane. The exponential in the numerator
accounts for the cutoff. This identity needs only an integrable density. -/
theorem fourierLaplace_eq_cauchyIntegral {g : ℝ → ℂ} (hg : Integrable g)
    (s : ℝ) {z : ℂ} (hz : 0 < z.im) :
    (∫ ξ in Ioi s, (𝓕 g) ξ * Complex.exp ((↑(2 * Real.pi * ξ) * Complex.I) * z)) =
      ∫ x : ℝ, (-Complex.exp (((↑(2 * Real.pi) * Complex.I) * (z - x)) * s) /
        ((↑(2 * Real.pi) * Complex.I) * (z - x))) * g x := by
  let a (x : ℝ) : ℂ := (↑(2 * Real.pi) * Complex.I) * (z - x)
  let b := -(2 * Real.pi * z.im)
  let ν := volume.restrict (Ioi s)
  let K (ξ x : ℝ) := Complex.exp (a x * ξ) * g x
  have hb : b < 0 := neg_neg_of_pos (mul_pos (by positivity) hz)
  have ha (x : ℝ) : (a x).re = b := by
    simp [a, b, Complex.mul_re, Complex.mul_im, Complex.sub_im]
  have hCap : Integrable (fun ξ : ℝ => Real.exp (b * ξ)) ν :=
    integrableOn_exp_mul_Ioi hb s
  have hExp : Continuous (fun p : ℝ × ℝ => Complex.exp (a p.2 * p.1)) := by
    unfold a
    fun_prop
  have hK : Integrable (Function.uncurry K) (ν.prod volume) := by
    apply (hCap.mul_prod hg.norm).mono'
      (hExp.aestronglyMeasurable.mul hg.aestronglyMeasurable.comp_snd)
    filter_upwards with p
    change ‖Complex.exp (a p.2 * p.1) * g p.2‖ ≤ Real.exp (b * p.1) * ‖g p.2‖
    rw [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, ha]
  calc
    _ = ∫ ξ in Ioi s, ∫ x : ℝ, K ξ x := by
      refine setIntegral_congr_fun measurableSet_Ioi fun ξ _ => ?_
      rw [Real.fourier_real_eq_integral_exp_smul, ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with x
      simp only [smul_eq_mul, K, mul_right_comm _ (g x), ← Complex.exp_add]
      congr 2
      dsimp [a]
      push_cast
      ring
    _ = ∫ x : ℝ, ∫ ξ in Ioi s, K ξ x := integral_integral_swap hK
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [show (∫ ξ in Ioi s, K ξ x) =
          (∫ ξ in Ioi s, Complex.exp (a x * ξ)) * g x from integral_mul_const _ _,
        integral_exp_mul_complex_Ioi (by rw [ha]; exact hb)]

/-- In the upper half-plane the heated positive-frequency integral has
the same Cauchy representation, using the actual heated density. -/
theorem heatFourierLaplace_eq_cauchyIntegral {f : ℝ → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) (s : ℝ) {z : ℂ} (hz : 0 < z.im) :
    heatFourierLaplace t f s z =
      ∫ x : ℝ, (-Complex.exp (((↑(2 * Real.pi) * Complex.I) * (z - x)) * s) /
        ((↑(2 * Real.pi) * Complex.I) * (z - x))) * (realGaussianSmoothing t f x : ℂ) :=
  fourierLaplace_eq_cauchyIntegral (integrable_realGaussianSmoothing hf ht).ofReal s hz

/-- At every positive height the positive-frequency integral satisfies
a bound uniform over all positive heat times. -/
theorem norm_heatFourierLaplace_le {f : ℝ → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) (s : ℝ) {z : ℂ} (hz : 0 < z.im) :
    ‖heatFourierLaplace t f s z‖ ≤
      (∫ x : ℝ, ‖f x‖) * Real.exp (-(2 * Real.pi * z.im) * s) /
        (2 * Real.pi * z.im) := by
  let b := 2 * Real.pi * z.im
  let M := ∫ x : ℝ, ‖f x‖
  have hb : 0 < b := mul_pos (by positivity) hz
  have hM : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
  let K (ξ : ℝ) := (𝓕 (fun y : ℝ => (realGaussianSmoothing t f y : ℂ))) ξ *
    Complex.exp ((↑(2 * Real.pi * ξ) * Complex.I) * z)
  have hK (ξ : ℝ) : ‖K ξ‖ ≤ M * Real.exp (-b * ξ) := by
    have hNorm : ‖Complex.exp ((↑(2 * Real.pi * ξ) * Complex.I) * z)‖ =
        Real.exp (-b * ξ) := by
      rw [Complex.norm_exp]
      congr 1
      simp [b, Complex.mul_re, Complex.mul_im]
      ring
    change ‖(𝓕 (fun y : ℝ => (realGaussianSmoothing t f y : ℂ))) ξ *
      Complex.exp ((↑(2 * Real.pi * ξ) * Complex.I) * z)‖ ≤ _
    rw [norm_mul, hNorm]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    refine (norm_fourier_realGaussianSmoothing_le hf ht ξ).trans ?_
    apply mul_le_of_le_one_right hM
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (by positivity)) (sq_nonneg ξ))
  calc
    _ ≤ ∫ ξ in Ioi s, ‖K ξ‖ := norm_integral_le_integral_norm K
    _ ≤ ∫ ξ in Ioi s, M * Real.exp (-b * ξ) := by
      refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
        ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hb) s).const_mul M)
        (ae_of_all _ hK)
    _ = _ := by
      simp only [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hb), div_neg,
        neg_div, neg_neg, mul_div_assoc]
      rfl

end
end MeyerGeneralProblem
