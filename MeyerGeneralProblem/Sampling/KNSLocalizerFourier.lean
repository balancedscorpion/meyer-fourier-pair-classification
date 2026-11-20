module

public import MeyerGeneralProblem.Sampling.KNSMomentLocalizer
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# Exact Fourier normalization of the KNS moment localizer

The convention is exp(-2*pi*i*x*eta), so the normalized box has Fourier
transform sinc(pi*u*eta/n), with its true value one at zero. All identities
below concern the actual integrals and convolutions, not assigned symbols.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory Set Convolution
open scoped FourierTransform

/-- The actual Fourier integral of a real kernel after complexification. -/
def knsRealFourier (f : ℝ → ℝ) (η : ℝ) : ℂ := 𝓕 (fun x => (f x : ℂ)) η

private theorem integral_exp_scaled_sinc (r a : ℝ) :
    (∫ x in -r..r, Complex.exp (((a*x : ℝ) : ℂ)*Complex.I)) =
      2*(r : ℂ)*(Real.sinc (a*r) : ℂ) := by
  by_cases ha : a=0
  · simp [ha, two_mul]
  have h := intervalIntegral.integral_comp_mul_left
    (fun x : ℝ => Complex.exp ((x : ℂ)*Complex.I)) (a := -r) (b := r) ha
  rw [mul_neg, integral_exp_mul_I_eq_sinc] at h
  rw [h]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul]
  field_simp [Complex.ofReal_ne_zero.mpr ha]

/-- Exact Fourier transform of the symmetric real box, including zero frequency. -/
theorem knsRealFourier_box {r : ℝ} (hr : 0 ≤ r) (η : ℝ) :
    knsRealFourier (knsBox r) η = 2*(r : ℂ)*(Real.sinc (2*Real.pi*r*η) : ℂ) := by
  unfold knsRealFourier
  rw [Real.fourier_eq']
  have hind : (fun x : ℝ => Complex.exp ((↑(-2*Real.pi*inner ℝ x η))*Complex.I) •
      (knsBox r x : ℂ)) = (Icc (-r) r).indicator
        (fun x : ℝ => Complex.exp ((((-2*Real.pi*η)*x : ℝ) : ℂ)*Complex.I)) := by
    funext x
    by_cases hx : x ∈ Icc (-r) r
    · simp [knsBox, hx, smul_eq_mul]
      congr 2
      ring
    · simp [knsBox, hx]
  rw [hind, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -r ≤ r), integral_exp_scaled_sinc]
  congr 1
  rw [show -2*Real.pi*η*r = -(2*Real.pi*r*η) by ring, Real.sinc_neg]

/-- Complexification preserves the actual real convolution integral. -/
theorem knsComplexify_convolution (f g : ℝ → ℝ) :
    (fun x => ((f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x : ℂ)) =
      (fun x => (f x : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun x => (g x : ℂ)) := by
  funext x
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  simpa only [Complex.ofReal_mul] using
    (integral_complex_ofReal (f := fun y => f y * g (x-y))).symm

/-- Actual convolution is transformed into multiplication after complexification. -/
theorem knsRealFourier_convolution {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (η : ℝ) :
    knsRealFourier (f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) η =
      knsRealFourier f η * knsRealFourier g η := by
  unfold knsRealFourier
  rw [knsComplexify_convolution]
  exact Real.fourier_mul_convolution_eq hf.ofReal hg.ofReal η

/-- The normalized short box has the exact sinc argument pi*u*eta/n. -/
theorem knsRealFourier_beta {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u) (η : ℝ) :
    knsRealFourier (knsBeta n u) η = (Real.sinc (Real.pi*u*η/n) : ℂ) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hmul : knsRealFourier (knsBeta n u) η =
      ((n : ℝ)/u : ℂ)*knsRealFourier (knsBox (u/(2*n))) η := by
    simp only [knsRealFourier, Real.fourier_eq', knsBeta, Complex.ofReal_mul,
      Complex.ofReal_div, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hmul, knsRealFourier_box (by positivity)]
  have ha : 2*Real.pi*(u/(2*n))*η = Real.pi*u*η/n := by ring
  rw [ha]
  push_cast
  field_simp [hnC, Complex.ofReal_ne_zero.mpr hu.ne']

/-- The n=1 regression uses exactly one sinc(pi*u*eta) factor. -/
theorem knsRealFourier_localizer_one {u : ℝ} (hu : 0 < u) (η : ℝ) :
    knsRealFourier (knsMomentLocalizer 1 u) η =
      knsRealFourier (knsBox u) η * (Real.sinc (Real.pi*u*η) : ℂ) := by
  unfold knsMomentLocalizer
  rw [knsBSpline_one, knsRealFourier_convolution (integrable_knsBeta 1 u) (integrable_knsBox u),
    knsRealFourier_beta (by omega) hu]
  simp only [Nat.cast_one, div_one]
  ring

/-- Actual repeated convolution produces the corresponding positive
integer power of its Fourier integral. -/
theorem knsRealFourier_boxConvolution {g : ℝ → ℝ} (hg : Integrable g) (j : ℕ) (η : ℝ) :
    knsRealFourier (knsBoxConvolution g j) η = (knsRealFourier g η)^(j+1) := by
  induction j with
  | zero => simp only [knsBoxConvolution, zero_add, pow_one]
  | succ j ih =>
    rw [knsBoxConvolution, knsRealFourier_convolution hg (integrable_knsBoxConvolution hg j), ih]
    rw [pow_succ]
    ring

/-- The actual B-spline's Fourier transform is exactly sinc(pi*u*eta/n)^n. -/
theorem knsRealFourier_bspline {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u) (η : ℝ) :
    knsRealFourier (knsBSpline n u) η = (Real.sinc (Real.pi*u*η/n) : ℂ)^n := by
  rw [knsBSpline, knsRealFourier_boxConvolution (integrable_knsBeta n u),
    knsRealFourier_beta hn hu, Nat.sub_add_cancel hn]

/-- The full KNS Fourier formula, with the actual long-box transform and
the exact n-fold sinc factor. -/
theorem knsRealFourier_localizer {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u) (η : ℝ) :
    knsRealFourier (knsMomentLocalizer n u) η =
      knsRealFourier (knsBox u) η * (Real.sinc (Real.pi*u*η/n) : ℂ)^n := by
  rw [knsMomentLocalizer, knsRealFourier_convolution (integrable_knsBSpline n u)
    (integrable_knsBox u), knsRealFourier_bspline hn hu, mul_comm]

/-- At zero frequency the normalized short box has value exactly one. -/
theorem knsRealFourier_beta_zero {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u) :
    knsRealFourier (knsBeta n u) 0 = 1 := by
  simp [knsRealFourier_beta hn hu]

/-- A sinc factor absorbs one frequency magnitude with the exact KNS
scale n/(pi*u); the zero-frequency case uses sinc(0)=1. -/
theorem kns_weighted_sinc_le {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u) (ξ η : ℝ) :
    (|ξ|+|η|)*|Real.sinc (Real.pi*u*η/n)| ≤ |ξ|+n/(Real.pi*u) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let a : ℝ := Real.pi*u/n
  have ha : 0 < a := by dsimp [a]; positivity
  have harg : Real.pi*u*η/n = a*η := by dsimp [a]; ring
  rw [harg]
  have hη : |η| * |Real.sinc (a*η)| ≤ a⁻¹ := by
    by_cases hzero : η=0
    · simp only [hzero, abs_zero, zero_mul]
      positivity
    · have hηpos : 0 < |η| := abs_pos.mpr hzero
      rw [Real.sinc_of_ne_zero (mul_ne_zero ha.ne' hzero), abs_div,
        abs_mul, abs_of_pos ha]
      have he : |η| * (|Real.sin (a*η)|/(a*|η|)) = |Real.sin (a*η)|/a := by field_simp
      rw [he, ← one_div]
      exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) ha.le
  have hξ : |ξ| * |Real.sinc (a*η)| ≤ |ξ| :=
    mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sinc_le_one _)
  have hinv : a⁻¹ = n/(Real.pi*u) := by dsimp [a]; field_simp
  rw [add_mul]
  exact (add_le_add hξ hη).trans_eq (by rw [hinv])

/-- Translating the actual real kernel by x-v gives precisely the
negative Fourier phase exp(-2*pi*i*v*eta). -/
theorem knsRealFourier_translate (f : ℝ → ℝ) (v η : ℝ) :
    knsRealFourier (fun x => f (x-v)) η =
      Complex.exp ((-2*(Real.pi : ℂ)*Complex.I*(v : ℂ)*(η : ℂ))) * knsRealFourier f η := by
  unfold knsRealFourier
  simp only [Real.fourier_eq', smul_eq_mul]
  rw [← integral_add_right_eq_self
    (fun x : ℝ => Complex.exp ((↑(-2*Real.pi*inner ℝ x η))*Complex.I) * (f (x-v) : ℂ)) v]
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [add_sub_cancel_right, Real.inner_apply]
  have he : (↑(-2*Real.pi*((x+v)*η)) : ℂ)*Complex.I =
      -2*(Real.pi : ℂ)*Complex.I*(v : ℂ)*(η : ℂ) +
        (↑(-2*Real.pi*(x*η)) : ℂ)*Complex.I := by push_cast; ring
  rw [he, Complex.exp_add]
  ring

end

end MeyerGeneralProblem
