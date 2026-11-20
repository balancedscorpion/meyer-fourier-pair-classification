module

public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Probability.Distributions.Cauchy

@[expose] public section

/-!
# The real Poisson kernel and its Fourier multiplier

The Fourier integral of the two-sided exponential is evaluated on
the two half-lines. Fourier inversion gives the multiplier of the
Cauchy density, and multiplication of the multipliers gives the real
Poisson convolution semigroup.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Convolution FourierTransform NNReal

private def poissonExponential (y : ℝ≥0) (t : ℝ) : ℂ :=
  (Real.exp (-(2 * Real.pi * (y : ℝ)) * |t|) : ℂ)

private def complexCauchyPDF (y : ℝ≥0) (x : ℝ) : ℂ :=
  (cauchyPDFReal 0 y x : ℂ)

private theorem continuous_poissonExponential (y : ℝ≥0) :
    Continuous (poissonExponential y) := by
  unfold poissonExponential
  fun_prop

private theorem integrable_poissonExponential {y : ℝ≥0} (hy : 0 < y) :
    Integrable (poissonExponential y) := by
  let a := 2 * Real.pi * (y : ℝ)
  have ha : 0 < a := mul_pos Real.two_pi_pos (show 0 < (y : ℝ) from hy)
  rw [← integrableOn_univ, ← @Ioi_union_Iic ℝ _ 0, integrableOn_union]
  constructor
  · exact (integrableOn_exp_mul_complex_Ioi
      (a := -(a : ℂ)) (by simpa using neg_lt_zero.mpr ha) 0).congr_fun
      (fun t ht => by
        have ht' : 0 < t := ht
        simp [poissonExponential, a, abs_of_pos ht', ← Complex.ofReal_exp,
          ← Complex.ofReal_mul, ← Complex.ofReal_neg]) measurableSet_Ioi
  · exact (integrableOn_exp_mul_complex_Iic
      (a := (a : ℂ)) (by simpa using ha) 0).congr_fun
      (fun t ht => by
        have ht' : t ≤ 0 := ht
        simp only [poissonExponential, a, abs_of_nonpos ht', ← Complex.ofReal_exp,
          ← Complex.ofReal_mul, neg_mul_neg]) measurableSet_Iic

private theorem fourier_poissonExponential {y : ℝ≥0} (hy : 0 < y) (ξ : ℝ) :
    𝓕 (poissonExponential y) ξ = complexCauchyPDF y ξ := by
  let a := 2 * Real.pi * (y : ℝ)
  let b := 2 * Real.pi * ξ
  let p : ℂ := -(a : ℂ) - (b : ℂ) * Complex.I
  let q : ℂ := (a : ℂ) - (b : ℂ) * Complex.I
  have hy' : 0 < (y : ℝ) := hy
  have ha : 0 < a := mul_pos Real.two_pi_pos hy'
  have hp : p.re = -a := by simp [p, Complex.sub_re, Complex.mul_re]
  have hq : q.re = a := by simp [q, Complex.sub_re, Complex.mul_re]
  have hpI : p.im = -b := by simp [p, Complex.sub_im, Complex.mul_im]
  have hqI : q.im = -b := by simp [q, Complex.sub_im, Complex.mul_im]
  have hpN : p.re < 0 := hp ▸ neg_lt_zero.mpr ha
  have hqP : 0 < q.re := hq ▸ ha
  let F (t : ℝ) : ℂ :=
    Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) * poissonExponential y t
  have hP : EqOn F (fun t : ℝ => Complex.exp (p * t)) (Ioi 0) := by
    intro t ht
    have ht' : 0 < t := ht
    change Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) *
      poissonExponential y t = Complex.exp (p * t)
    rw [poissonExponential, abs_of_pos ht', Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    dsimp [p, a, b]
    push_cast
    ring
  have hQ : EqOn F (fun t : ℝ => Complex.exp (q * t)) (Iic 0) := by
    intro t ht
    have ht' : t ≤ 0 := ht
    change Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) *
      poissonExponential y t = Complex.exp (q * t)
    rw [poissonExponential, abs_of_nonpos ht', Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    dsimp [q, a, b]
    push_cast
    ring
  have hF : Integrable F := by
    rw [← integrableOn_univ, ← @Ioi_union_Iic ℝ _ 0, integrableOn_union]
    exact ⟨(integrableOn_congr_fun hP measurableSet_Ioi).mpr
      (integrableOn_exp_mul_complex_Ioi hpN 0),
      (integrableOn_congr_fun hQ measurableSet_Iic).mpr (integrableOn_exp_mul_complex_Iic hqP 0)⟩
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  change (∫ t, F t) = _
  rw [← integral_add_compl measurableSet_Ioi hF, compl_Ioi,
    setIntegral_congr_fun measurableSet_Ioi hP, setIntegral_congr_fun measurableSet_Iic hQ,
    integral_exp_mul_complex_Ioi hpN 0, integral_exp_mul_complex_Iic hqP 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div, one_div]
  have hDenom : (ξ ^ 2 + (y : ℝ) ^ 2) ≠ 0 :=
    (add_pos_of_nonneg_of_pos (sq_nonneg ξ) (sq_pos_of_pos hy')).ne'
  apply Complex.ext
  · simp only [complexCauchyPDF, cauchyPDFReal_def, sub_zero, Complex.add_re, Complex.neg_re,
      Complex.ofReal_re, Complex.inv_re, Complex.normSq_apply, hp, hq, hpI, hqI, neg_mul_neg,
      neg_div, neg_neg]
    have h : a * a + b * b = (2 * Real.pi) ^ 2 * (ξ ^ 2 + (y : ℝ) ^ 2) := by
      dsimp [a, b]
      ring
    rw [h]
    dsimp [a]
    field_simp [Real.pi_ne_zero, hDenom]
    ring
  · simp only [complexCauchyPDF, Complex.ofReal_im, Complex.add_im, Complex.neg_im,
      Complex.inv_im, Complex.normSq_apply, hp, hq, hpI, hqI, neg_mul_neg, neg_neg, neg_add_cancel]

private theorem integrable_complexCauchyPDF (y : ℝ≥0) :
    Integrable (complexCauchyPDF y) :=
  (integrable_cauchyPDFReal 0 (γ := y)).ofReal

/-- The ordinary Fourier multiplier of the real Poisson kernel at
height `y`, with the negative-kernel Fourier convention. -/
theorem fourier_cauchyPDFReal_ofReal {y : ℝ≥0} (hy : 0 < y) (ξ : ℝ) :
    𝓕 (fun t : ℝ => (cauchyPDFReal 0 y t : ℂ)) ξ =
      (Real.exp (-(2 * Real.pi * (y : ℝ)) * |ξ|) : ℂ) := by
  have hInv : 𝓕⁻ (poissonExponential y) = complexCauchyPDF y := by
    funext x
    rw [Real.fourierInv_eq_fourier_neg, fourier_poissonExponential hy]
    simp [complexCauchyPDF, cauchyPDFReal_def]
  have hF : 𝓕 (poissonExponential y) = complexCauchyPDF y :=
    funext (fourier_poissonExponential hy)
  change 𝓕 (complexCauchyPDF y) ξ = poissonExponential y ξ
  rw [← hInv]
  exact congrFun ((continuous_poissonExponential y).fourier_fourierInv_eq
    (integrable_poissonExponential hy) (hF.symm ▸ integrable_complexCauchyPDF y)) ξ

private theorem continuous_complexCauchyPDF {y : ℝ≥0} (hy : 0 < y) :
    Continuous (complexCauchyPDF y) := by
  have hy' : 0 < (y : ℝ) := hy
  apply Complex.continuous_ofReal.comp
  change Continuous (fun t : ℝ => cauchyPDFReal 0 y t)
  simp only [cauchyPDFReal_def, sub_zero]
  exact continuous_const.mul ((show Continuous (fun t : ℝ => t ^ 2 + (y : ℝ) ^ 2) by
    fun_prop).inv₀ fun t => (add_pos_of_nonneg_of_pos (sq_nonneg t) (sq_pos_of_pos hy')).ne')

private theorem cauchyPDFReal_zero_le {y : ℝ≥0} (hy : 0 < y) (t : ℝ) :
    cauchyPDFReal 0 y t ≤ Real.pi⁻¹ * (y : ℝ) * ((y : ℝ) ^ 2)⁻¹ := by
  have hy' : 0 < (y : ℝ) := hy
  have hY : 0 < (y : ℝ) ^ 2 := sq_pos_of_pos hy'
  rw [cauchyPDFReal_def, sub_zero]
  exact mul_le_mul_of_nonneg_left
    ((inv_le_inv₀ (add_pos_of_nonneg_of_pos (sq_nonneg t) hY) hY).mpr
      (le_add_of_nonneg_left (sq_nonneg t)))
    (mul_nonneg (inv_nonneg.mpr Real.pi_pos.le) hy'.le)

private theorem convolution_complexCauchyPDF {s y : ℝ≥0} (hs : 0 < s) (hy : 0 < y) :
    complexCauchyPDF s ⋆[ContinuousLinearMap.mul ℂ ℂ] complexCauchyPDF y =
      complexCauchyPDF (s + y) := by
  let L := ContinuousLinearMap.mul ℂ ℂ
  have hsInt := integrable_complexCauchyPDF s
  have hyInt := integrable_complexCauchyPDF y
  have hsy : 0 < s + y := add_pos hs hy
  have hBdd : BddAbove (range (fun t : ℝ => ‖complexCauchyPDF y t‖)) := by
    refine ⟨Real.pi⁻¹ * (y : ℝ) * ((y : ℝ) ^ 2)⁻¹, ?_⟩
    rintro _ ⟨t, rfl⟩
    change ‖(cauchyPDFReal 0 y t : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_of_nonneg (cauchyPDF_pos 0 hy.ne' t).le]
    exact cauchyPDFReal_zero_le hy t
  have hCont : Continuous (complexCauchyPDF s ⋆[L] complexCauchyPDF y) :=
    hBdd.continuous_convolution_right_of_integrable L hsInt (continuous_complexCauchyPDF hy)
  have hSpec {z : ℝ≥0} (hz : 0 < z) (ξ : ℝ) :
      𝓕 (complexCauchyPDF z) ξ = poissonExponential z ξ :=
    fourier_cauchyPDFReal_ofReal hz ξ
  have hEq : 𝓕 (complexCauchyPDF s ⋆[L] complexCauchyPDF y) =
      𝓕 (complexCauchyPDF (s + y)) := by
    funext ξ
    change 𝓕 (complexCauchyPDF s ⋆[ContinuousLinearMap.mul ℂ ℂ] complexCauchyPDF y) ξ = _
    rw [Real.fourier_mul_convolution_eq hsInt hyInt, hSpec hs, hSpec hy, hSpec hsy]
    simp only [poissonExponential, ← Complex.ofReal_mul, ← Real.exp_add, NNReal.coe_add]
    congr 2
    ring
  have hFI : Integrable (𝓕 (complexCauchyPDF (s + y))) := by
    rw [funext (hSpec hsy)]
    exact integrable_poissonExponential hsy
  have hInv := hCont.fourierInv_fourier_eq (hsInt.integrable_convolution L hyInt) (hEq.symm ▸ hFI)
  rw [hEq, (continuous_complexCauchyPDF hsy).fourierInv_fourier_eq
    (integrable_complexCauchyPDF (s + y)) hFI] at hInv
  exact hInv.symm

/-- Convolution of two real Poisson kernels adds their heights. -/
theorem integral_cauchyPDFReal_mul_cauchyPDFReal {s y : ℝ≥0} (hs : 0 < s) (hy : 0 < y)
    (x : ℝ) :
    (∫ t : ℝ, cauchyPDFReal 0 s t * cauchyPDFReal t y x) =
      cauchyPDFReal 0 (s + y) x := by
  have h := congrArg Complex.re (congrFun (convolution_complexCauchyPDF hs hy) x)
  simpa only [convolution_def, ContinuousLinearMap.mul_apply', complexCauchyPDF,
    ← Complex.ofReal_mul, integral_complex_ofReal, Complex.ofReal_re,
    cauchyPDFReal_def, sub_zero] using h

/-- The same convolution identity for nonnegative Lebesgue integrals. -/
theorem lintegral_cauchyPDF_mul_cauchyPDF {s y : ℝ≥0} (hs : 0 < s) (hy : 0 < y)
    (x : ℝ) :
    (∫⁻ t : ℝ, cauchyPDF 0 s t * cauchyPDF t y x) = cauchyPDF 0 (s + y) x := by
  let f (t : ℝ) := cauchyPDFReal 0 s t * cauchyPDFReal t y x
  have hPos (t : ℝ) : 0 ≤ f t :=
    mul_nonneg (cauchyPDF_pos 0 hs.ne' t).le (cauchyPDF_pos t hy.ne' x).le
  have hBound (t : ℝ) : cauchyPDFReal t y x ≤ Real.pi⁻¹ * (y : ℝ) * ((y : ℝ) ^ 2)⁻¹ := by
    simpa only [cauchyPDFReal_def, sub_zero] using cauchyPDFReal_zero_le hy (x - t)
  have hMeas : Measurable f := by
    unfold f cauchyPDFReal
    fun_prop
  have hInt : Integrable f := by
    refine ((integrable_cauchyPDFReal 0 (γ := s)).mul_const
      (Real.pi⁻¹ * (y : ℝ) * ((y : ℝ) ^ 2)⁻¹)).mono' hMeas.aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_of_nonneg (hPos t)]
    exact mul_le_mul_of_nonneg_left (hBound t) (cauchyPDF_pos 0 hs.ne' t).le
  have hPdf (t : ℝ) : cauchyPDF 0 s t * cauchyPDF t y x = ENNReal.ofReal (f t) := by
    rw [cauchyPDF_def, cauchyPDF_def, ENNReal.ofReal_mul (cauchyPDF_pos 0 hs.ne' t).le]
  simp_rw [hPdf]
  rw [← ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ hPos)]
  change ENNReal.ofReal (∫ t : ℝ, cauchyPDFReal 0 s t * cauchyPDFReal t y x) = _
  rw [integral_cauchyPDFReal_mul_cauchyPDFReal hs hy, cauchyPDF_def]

end
end MeyerGeneralProblem
