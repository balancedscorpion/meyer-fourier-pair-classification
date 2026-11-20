module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Tactic

@[expose] public section

/-!
# Sharp periodic complex Poincare--Wirtinger estimates

Actual interval Fourier coefficients and integration by parts retain the
normalization needed by the restricted square-root arithmetic endpoint.
-/

namespace MeyerGeneralProblem

noncomputable section

open MeasureTheory AddCircle Set
open scoped Interval ContDiff

/-- Differentiating an actual interval Fourier coefficient has its exact
Fourier normalization when the function's two endpoint values agree. -/
theorem fourierCoeffOn_deriv_of_endpoints {a b : ℝ} (hab : a < b)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hend : f a = f b) (n : ℤ) :
    fourierCoeffOn hab (deriv f) n =
      (2 * (Real.pi : ℂ) * Complex.I * n / (b-a)) * fourierCoeffOn hab f n := by
  let : Fact (0 < b-a) := ⟨by linarith⟩
  let e : ℝ → ℂ := fun x => fourier (-n) (x : AddCircle (b-a))
  let c : ℂ := 2 * (Real.pi : ℂ) * Complex.I * n / (b-a)
  have he (x : ℝ) : HasDerivAt e (-c*e x) x := by
    convert hasDerivAt_fourier_neg (b-a) n x using 1
    dsimp only [c, e]
    push_cast
    ring
  have hecont : Continuous e := continuous_iff_continuousAt.mpr (fun x => (he x).continuousAt)
  have hfcont : Continuous (deriv f) := by
    simpa only [iteratedDeriv_one] using hf.continuous_iteratedDeriv' 1
  have hfd (x : ℝ) : HasDerivAt f (deriv f x) x :=
    (hf.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hboundary : e b = e a := by
    dsimp only [e]
    apply congrArg (fun z : AddCircle (b-a) => fourier (-n) z)
    calc
      (b : AddCircle (b-a)) = ((a+(b-a) : ℝ) : AddCircle (b-a)) :=
        congrArg (fun z : ℝ => (z : AddCircle (b-a))) (by ring)
      _ = (a : AddCircle (b-a)) := AddCircle.coe_add_period (b-a) a
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := e) (u' := fun x => -c*e x) (v := f) (v' := deriv f)
    (fun x _ => he x) (fun x _ => hfd x)
    ((continuous_const.mul hecont).intervalIntegrable a b) (hfcont.intervalIntegrable a b)
  rw [hboundary, ← hend, sub_self] at hibp
  simp_rw [mul_assoc] at hibp
  rw [intervalIntegral.integral_const_mul] at hibp
  have hmoment : (∫ x in a..b, e x*deriv f x) = c*(∫ x in a..b, e x*f x) := by
    simpa only [neg_mul, integral_neg, zero_sub, neg_neg] using hibp
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp only [smul_eq_mul, Complex.real_smul]
  change ((1/(b-a):ℝ):ℂ)*(∫ x in a..b, e x*deriv f x) =
    c*(((1/(b-a):ℝ):ℂ)*(∫ x in a..b, e x*f x))
  rw [hmoment]
  ring

/-- Continuous functions have genuine finite interval L2 energy. -/
theorem continuous_memLp_Ioc {f : ℝ → ℂ} (hf : Continuous f) (a b : ℝ) :
    MemLp f 2 (volume.restrict (Ioc a b)) := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact hC x ⟨hx.1.le,hx.2⟩

/-- A vanishing interval mean is the actual zero Fourier coefficient. -/
theorem fourierCoeffOn_zero_of_integral_zero {a b : ℝ} (hab : a < b)
    (f : ℝ → ℂ) (hf : (∫ x in a..b, f x) = 0) :
    fourierCoeffOn hab f 0 = 0 := by
  rw [fourierCoeffOn_eq_integral]
  simp [hf]

/-- The sharp periodic complex Poincare--Wirtinger inequality follows
from actual derivative coefficients and Parseval, not a spectral premise. -/
theorem complex_periodic_poincare_wirtinger {a b : ℝ} (hab : a < b)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hend : f a = f b)
    (hmean : (∫ x in a..b, f x) = 0) :
    (2*Real.pi)^2 * (∫ x in a..b, ‖f x‖^2) ≤
      (b-a)^2 * (∫ x in a..b, ‖deriv f x‖^2) := by
  have hT : 0 < b-a := sub_pos.mpr hab
  have hfcont : Continuous (deriv f) := by
    simpa only [iteratedDeriv_one] using hf.continuous_iteratedDeriv' 1
  have hLf := continuous_memLp_Ioc hf.continuous a b
  have hLd := continuous_memLp_Ioc hfcont a b
  have hcoeff (n : ℤ) : (2*Real.pi/(b-a))^2 * ‖fourierCoeffOn hab f n‖^2 ≤
      ‖fourierCoeffOn hab (deriv f) n‖^2 := by
    by_cases hn : n=0
    · subst n
      rw [fourierCoeffOn_zero_of_integral_zero hab f hmean, norm_zero]
      simp
    · have hn1 : (1:ℝ) ≤ |(n:ℝ)| := by exact_mod_cast (Int.one_le_abs hn)
      rw [fourierCoeffOn_deriv_of_endpoints hab f hf hend n, norm_mul, mul_pow]
      have hc : ‖2 * (Real.pi : ℂ) * Complex.I * n / (b-a)‖ =
          (2*Real.pi/(b-a))*|(n:ℝ)| := by
        simp only [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast,
          ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos, abs_of_pos hT]
        norm_num
        ring
      rw [hc, mul_pow]
      have hsq : 1 ≤ |(n:ℝ)|^2 := by nlinarith [abs_nonneg (n:ℝ)]
      nlinarith [sq_nonneg (2*Real.pi/(b-a)), sq_nonneg ‖fourierCoeffOn hab f n‖,
        mul_nonneg (sq_nonneg (2*Real.pi/(b-a))) (sq_nonneg ‖fourierCoeffOn hab f n‖)]
  have hs := hasSum_le hcoeff
    ((hasSum_sq_fourierCoeffOn hab hLf).mul_left ((2*Real.pi/(b-a))^2))
    (hasSum_sq_fourierCoeffOn hab hLd)
  simp only [smul_eq_mul] at hs
  have hs' := mul_le_mul_of_nonneg_left hs (pow_nonneg hT.le 3)
  have halg (u v : ℝ) : (b-a)^3*((2*Real.pi/(b-a))^2*((b-a)⁻¹*u)) =
      (2*Real.pi)^2*u ∧ (b-a)^3*((b-a)⁻¹*v) = (b-a)^2*v := by
    constructor <;> field_simp
  rw [(halg (∫ x in a..b, ‖f x‖^2) (∫ x in a..b, ‖deriv f x‖^2)).1,
    (halg (∫ x in a..b, ‖f x‖^2) (∫ x in a..b, ‖deriv f x‖^2)).2] at hs'
  exact hs'

end

end MeyerGeneralProblem
