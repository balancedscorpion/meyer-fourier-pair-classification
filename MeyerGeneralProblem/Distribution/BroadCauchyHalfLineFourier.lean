module

public import MeyerGeneralProblem.Distribution.BroadCauchyKernel
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-!
# The half-line Fourier formula for the original Cauchy kernel

The exact transform is obtained by Laplace integration of the
exponential monomial on its decaying half-line.
-/

namespace MeyerGeneralProblem

noncomputable section

open Set Filter MeasureTheory
open scoped Topology FourierTransform

private def laplaceMonomial (s : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ n * Complex.exp (-s * (x : ℂ))

private theorem norm_laplaceMonomial (s : ℂ) (n : ℕ) (x : ℝ) :
    ‖laplaceMonomial s n x‖ = |x| ^ n * Real.exp (-s.re * x) := by
  simp only [laplaceMonomial, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

private theorem integrableOn_laplaceMonomial (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    IntegrableOn (laplaceMonomial s n) (Ioi 0) := by
  have hReal : IntegrableOn (fun x : ℝ => x ^ n * Real.exp (-s.re * x)) (Ioi 0) := by
    simpa only [Real.rpow_one, Real.rpow_natCast] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (n : ℝ)) (p := 1) (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg n)) zero_lt_one hs)
  refine hReal.mono' (by unfold laplaceMonomial; fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_laplaceMonomial, abs_of_pos (mem_Ioi.mp hx)]

private theorem tendsto_laplaceMonomial_atTop (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    Tendsto (laplaceMonomial s n) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have he : (fun x : ℝ => ‖laplaceMonomial s n x‖) =ᶠ[atTop]
      (fun x : ℝ => x ^ (n : ℝ) * Real.exp (-s.re * x)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [norm_laplaceMonomial, abs_of_nonneg hx, Real.rpow_natCast]
  exact (tendsto_congr' he).mpr (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero n s.re hs)

theorem hasDerivAt_laplaceExp (s : ℂ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (-s * (x : ℂ))) (-s * Complex.exp (-s * (x : ℂ))) x := by
  have h : HasDerivAt (fun z : ℂ => -s * z) (-s * 1) (x : ℂ) := (hasDerivAt_id' (x : ℂ)).const_mul _
  have he := h.cexp.comp_ofReal
  simpa only [mul_one, mul_comm] using he

private theorem hasDerivAt_laplaceMonomial_succ (s : ℂ) (n : ℕ) (x : ℝ) :
    HasDerivAt (laplaceMonomial s (n + 1))
      (((n + 1 : ℕ) : ℂ) * laplaceMonomial s n x - s * laplaceMonomial s (n + 1) x) x := by
  have hp : HasDerivAt (fun t : ℝ => (t : ℂ) ^ (n + 1)) (((n + 1 : ℕ) : ℂ) * (x : ℂ) ^ n) x := by
    simpa only [Nat.succ_sub_one] using (hasDerivAt_pow (n + 1) (x : ℂ)).comp_ofReal
  convert hp.mul (hasDerivAt_laplaceExp s x) using 1
  all_goals first | rfl | (dsimp only [laplaceMonomial]; ring)

/-- The complex Laplace integral of an integer monomial is given by
its factorial and the full complex decay parameter. -/
theorem integral_laplaceMonomial (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    ∫ x : ℝ in Ioi 0, (x : ℂ) ^ n * Complex.exp (-s * (x : ℂ)) =
      (n.factorial : ℂ) / s ^ (n + 1) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  change ∫ x : ℝ in Ioi 0, laplaceMonomial s n x = _
  induction n with
  | zero =>
    have he : (fun x : ℝ => Complex.exp (-s * (x : ℂ))) = laplaceMonomial s 0 := by
      funext x
      simp [laplaceMonomial]
    have hI := integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun x (_ : x ∈ Ici (0 : ℝ)) => hasDerivAt_laplaceExp s x)
      (show IntegrableOn (fun x : ℝ => -s * Complex.exp (-s * (x : ℂ))) (Ioi 0) by
        rw [show (fun x : ℝ => -s * Complex.exp (-s * (x : ℂ))) = (fun x => -s * laplaceMonomial s 0 x) by
          simp only [← he]]
        exact (integrableOn_laplaceMonomial s hs 0).const_mul _)
      (by rw [he]; exact tendsto_laplaceMonomial_atTop s hs 0)
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, zero_sub, integral_const_mul] at hI
    rw [he] at hI
    simp only [Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    apply (eq_div_iff hs0).mpr
    linear_combination -hI
  | succ n ih =>
    have hI := integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun x (_ : x ∈ Ici (0 : ℝ)) => hasDerivAt_laplaceMonomial_succ s n x)
      ((integrableOn_laplaceMonomial s hs n).const_mul (((n + 1 : ℕ) : ℂ)) |>.sub
        ((integrableOn_laplaceMonomial s hs (n + 1)).const_mul s))
      (tendsto_laplaceMonomial_atTop s hs (n + 1))
    rw [integral_sub ((integrableOn_laplaceMonomial s hs n).const_mul (((n + 1 : ℕ) : ℂ)))
      ((integrableOn_laplaceMonomial s hs (n + 1)).const_mul s),
      integral_const_mul, integral_const_mul] at hI
    have hzero : laplaceMonomial s (n + 1) 0 = 0 := by
      simp [laplaceMonomial]
    rw [hzero, sub_zero] at hI
    have he : s * (∫ x in Ioi (0 : ℝ), laplaceMonomial s (n + 1) x) =
        (((n + 1 : ℕ) : ℂ)) * ∫ x in Ioi (0 : ℝ), laplaceMonomial s n x := by
      linear_combination -hI
    apply (eq_div_iff (pow_ne_zero _ hs0)).mpr
    calc
      _ = (s * ∫ x in Ioi (0 : ℝ), laplaceMonomial s (n + 1) x) * s ^ (n + 1) := by
        rw [pow_succ s (n + 1)]
        ring
      _ = (((n + 1 : ℕ) : ℂ)) * (n.factorial : ℂ) := by
        rw [he, ih, mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hs0)]
      _ = _ := by rw [Nat.factorial_succ, Nat.cast_mul]

/-- Normalization of the half-line Fourier monomial for pole order n + 1. -/
def broadCauchyFourierFactor (n : ℕ) : ℂ :=
  ((2 * Real.pi : ℝ) * Complex.I) ^ (n + 1) / (n.factorial : ℂ)

/-- The original inverse Fourier formula on the upper half-plane. -/
def upperCauchyFrequency (n : ℕ) (z : ℂ) : ℝ → ℂ :=
  (Ioi (0 : ℝ)).indicator fun t =>
    broadCauchyFourierFactor n * (t : ℂ) ^ n *
      Complex.exp (((2 * Real.pi : ℝ) * Complex.I) * (t : ℂ) * z)

private theorem integrable_upperCauchyFrequency (n : ℕ) (z : ℂ) (hz : 0 < z.im) :
    Integrable (upperCauchyFrequency n z) := by
  let s : ℂ := -(((2 * Real.pi : ℝ) : ℂ) * Complex.I * z)
  have hs : 0 < s.re := by
    dsimp only [s]
    simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, mul_one,
      zero_sub, neg_neg]
    positivity
  rw [upperCauchyFrequency, integrable_indicator_iff measurableSet_Ioi]
  have he : (fun t : ℝ => broadCauchyFourierFactor n * (t : ℂ) ^ n *
      Complex.exp (((2 * Real.pi : ℝ) * Complex.I) * (t : ℂ) * z)) =
      (fun t => broadCauchyFourierFactor n * laplaceMonomial s n t) := by
    funext t
    dsimp only [laplaceMonomial, s]
    rw [mul_assoc]
    congr 2
    ring
  rw [he]
  exact (integrableOn_laplaceMonomial s hs n).const_mul _

private theorem continuous_upperCauchyFrequency (n : ℕ) (hn : 0 < n) (z : ℂ) :
    Continuous (upperCauchyFrequency n z) := by
  unfold upperCauchyFrequency
  change Continuous ((Ioi (0 : ℝ)).piecewise _ (0 : ℝ → ℂ))
  apply Continuous.piecewise
  · intro t ht
    rw [frontier_Ioi, mem_singleton_iff] at ht
    subst t
    simp [zero_pow hn.ne']
  · fun_prop
  · exact continuous_const

/-- The literal higher-order Cauchy kernel is integrable for m ≥ 2. -/
theorem integrable_broadCauchyKernel (m : ℕ) (hm : 2 ≤ m) (z : ℂ) (hz : z.im ≠ 0) :
    Integrable (broadCauchyKernel m z) := by
  let b := max 1 (|z.im|)⁻¹
  let C := b ^ m + (1 + ‖z‖) ^ 2 * b ^ m
  refine (integrable_inv_one_add_sq.const_mul C).mono'
    ((contDiff_broadCauchyKernel_test m z hz 0).continuous.aestronglyMeasurable) ?_
  filter_upwards with x
  have h0 := norm_weighted_iteratedDeriv_broadCauchyKernel_test_le m 0 0 (by omega) z hz x
  have h2 := norm_weighted_iteratedDeriv_broadCauchyKernel_test_le m 2 0 (by omega) z hz x
  simp only [Nat.ascFactorial_zero, Nat.cast_one, one_mul, pow_zero, add_zero, iteratedDeriv_zero] at h0 h2
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  rw [mul_add, mul_one, ← sq_abs x, mul_comm ‖broadCauchyKernel m z x‖]
  exact add_le_add h0 (by simpa [mul_comm] using h2)

private theorem fourier_upperCauchyFrequency (n : ℕ) (z : ℂ) (hz : 0 < z.im) :
    𝓕 (upperCauchyFrequency n z) = broadCauchyKernel (n + 1) z := by
  funext x
  let c : ℂ := ((2 * Real.pi : ℝ) : ℂ) * Complex.I
  let s : ℂ := c * ((x : ℂ) - z)
  have hs : 0 < s.re := by
    dsimp only [s, c]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im, mul_zero, zero_mul, sub_zero,
      mul_one, zero_sub, mul_neg, neg_neg]
    positivity
  have hc : c ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) Complex.I_ne_zero
  have hp : (x : ℂ) - z ≠ 0 := by
    intro he
    simp [s, he] at hs
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = ∫ t : ℝ in Ioi 0, broadCauchyFourierFactor n * laplaceMonomial s n t := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t ∈ Ioi (0 : ℝ)
      · rw [upperCauchyFrequency, indicator_of_mem ht, indicator_of_mem ht, smul_eq_mul]
        dsimp only [laplaceMonomial, s, c]
        calc
          _ = broadCauchyFourierFactor n * (t : ℂ) ^ n *
              (Complex.exp (↑(-2 * Real.pi * t * x) * Complex.I) *
                Complex.exp (((2 * Real.pi : ℝ) * Complex.I) * (t : ℂ) * z)) := by ring
          _ = _ := by
            rw [← Complex.exp_add, mul_assoc]
            congr 2
            push_cast
            ring
      · rw [upperCauchyFrequency, indicator_of_notMem ht, indicator_of_notMem ht, smul_zero]
    _ = broadCauchyFourierFactor n * ((n.factorial : ℂ) / s ^ (n + 1)) := by
      rw [integral_const_mul]
      exact congrArg ((broadCauchyFourierFactor n) * ·) (integral_laplaceMonomial s hs n)
    _ = _ := by
      change (c ^ (n + 1) / (n.factorial : ℂ)) *
        ((n.factorial : ℂ) / (c * ((x : ℂ) - z)) ^ (n + 1)) = _
      rw [broadCauchyKernel, inv_pow, mul_pow]
      have hfact : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
      field_simp [pow_ne_zero _ hc, pow_ne_zero (n + 1) hp]
      simp only [c, mul_pow]

/-- Pointwise inverse Fourier transform for a pole in the upper half-plane.
The value at frequency zero is included for every pole order at least two. -/
theorem fourierInv_broadCauchyKernel_upper (n : ℕ) (hn : 0 < n) (z : ℂ) (hz : 0 < z.im) :
    𝓕⁻ (broadCauchyKernel (n + 1) z) = upperCauchyFrequency n z := by
  rw [← fourier_upperCauchyFrequency n z hz]
  apply (continuous_upperCauchyFrequency n hn z).fourierInv_fourier_eq
    (integrable_upperCauchyFrequency n z hz)
  rw [fourier_upperCauchyFrequency n z hz]
  exact integrable_broadCauchyKernel (n + 1) (by omega) z hz.ne'

/-- The original inverse Fourier formula on the lower half-plane. -/
def lowerCauchyFrequency (n : ℕ) (z : ℂ) : ℝ → ℂ :=
  (Iio (0 : ℝ)).indicator fun t =>
    -(broadCauchyFourierFactor n * (t : ℂ) ^ n *
      Complex.exp (((2 * Real.pi : ℝ) * Complex.I) * (t : ℂ) * z))

theorem lowerCauchyFrequency_eq_reflection (n : ℕ) (z : ℂ) :
    lowerCauchyFrequency n z =
      (-1 : ℂ) ^ (n + 1) • (upperCauchyFrequency n (-z) ∘ LinearIsometryEquiv.neg ℝ) := by
  funext t
  change lowerCauchyFrequency n z t = (-1 : ℂ) ^ (n + 1) * upperCauchyFrequency n (-z) (-t)
  by_cases ht : t < 0
  · rw [lowerCauchyFrequency, upperCauchyFrequency, indicator_of_mem (show t ∈ Iio (0 : ℝ) from ht),
      indicator_of_mem (show -t ∈ Ioi (0 : ℝ) from neg_pos.mpr ht), Complex.ofReal_neg]
    have he : ((2 * Real.pi : ℝ) : ℂ) * Complex.I * -(t : ℂ) * -z =
        ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (t : ℂ) * z := by ring
    rw [he, neg_pow, pow_succ (-1 : ℂ) n]
    have hs : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by rw [← mul_pow]; norm_num
    symm
    calc
      _ = -(((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) *
          (broadCauchyFourierFactor n * (t : ℂ) ^ n *
            Complex.exp (((2 * Real.pi : ℝ) * Complex.I) * (t : ℂ) * z))) := by ring
      _ = _ := by rw [hs, one_mul]
  · rw [lowerCauchyFrequency, upperCauchyFrequency, indicator_of_notMem (show t ∉ Iio (0 : ℝ) from ht),
      indicator_of_notMem (show -t ∉ Ioi (0 : ℝ) from fun h => ht (neg_pos.mp h)), mul_zero]

private theorem broadCauchyKernel_eq_reflection (m : ℕ) (z : ℂ) :
    broadCauchyKernel m z =
      (-1 : ℂ) ^ m • (broadCauchyKernel m (-z) ∘ LinearIsometryEquiv.neg ℝ) := by
  funext x
  change ((x : ℂ) - z)⁻¹ ^ m = (-1 : ℂ) ^ m * (((-x : ℝ) : ℂ) - -z)⁻¹ ^ m
  rw [Complex.ofReal_neg, show -(x : ℂ) - -z = -((x : ℂ) - z) by ring,
    inv_neg, ← mul_pow]
  simp

private theorem integrable_lowerCauchyFrequency (n : ℕ) (z : ℂ) (hz : z.im < 0) :
    Integrable (lowerCauchyFrequency n z) := by
  rw [lowerCauchyFrequency_eq_reflection]
  have hpos : 0 < (-z).im := by simpa only [Complex.neg_im] using neg_pos.mpr hz
  exact ((LinearIsometryEquiv.neg ℝ (E := ℝ)).measurePreserving.integrable_comp_of_integrable
    (integrable_upperCauchyFrequency n (-z) hpos)).const_mul _

private theorem fourier_const_mul_complex (c : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    𝓕 (c • f) x = c * 𝓕 f x := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private theorem fourier_lowerCauchyFrequency (n : ℕ) (z : ℂ) (hz : z.im < 0) :
    𝓕 (lowerCauchyFrequency n z) = broadCauchyKernel (n + 1) z := by
  have hpos : 0 < (-z).im := by simpa only [Complex.neg_im] using neg_pos.mpr hz
  rw [lowerCauchyFrequency_eq_reflection]
  funext x
  rw [fourier_const_mul_complex, Real.fourier_comp_linearIsometry,
    fourier_upperCauchyFrequency n (-z) hpos]
  exact (congrFun (broadCauchyKernel_eq_reflection (n + 1) z) x).symm

/-- Pointwise inverse Fourier transform for a pole in the lower half-plane. -/
theorem fourierInv_broadCauchyKernel_lower (n : ℕ) (hn : 0 < n) (z : ℂ) (hz : z.im < 0) :
    𝓕⁻ (broadCauchyKernel (n + 1) z) = lowerCauchyFrequency n z := by
  have hpos : 0 < (-z).im := by simpa only [Complex.neg_im] using neg_pos.mpr hz
  have hcont : Continuous (lowerCauchyFrequency n z) := by
    rw [lowerCauchyFrequency_eq_reflection]
    exact continuous_const.smul ((continuous_upperCauchyFrequency n hn (-z)).comp
      (LinearIsometryEquiv.neg ℝ).continuous)
  rw [← fourier_lowerCauchyFrequency n z hz]
  apply hcont.fourierInv_fourier_eq (integrable_lowerCauchyFrequency n z hz)
  rw [fourier_lowerCauchyFrequency n z hz]
  exact integrable_broadCauchyKernel (n + 1) (by omega) z hz.ne

/-- Both half-plane formulas use the same original pole and the same
Fourier convention. -/
def broadCauchyFrequency (n : ℕ) (z : ℂ) : ℝ → ℂ :=
  if 0 < z.im then upperCauchyFrequency n z else lowerCauchyFrequency n z

theorem integrable_broadCauchyFrequency (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    Integrable (broadCauchyFrequency n z) := by
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · simpa only [broadCauchyFrequency, ite_eq_right hneg.not_gt] using integrable_lowerCauchyFrequency n z hneg
  · simpa only [broadCauchyFrequency, ite_eq_left hpos] using integrable_upperCauchyFrequency n z hpos

theorem fourier_broadCauchyFrequency (n : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    𝓕 (broadCauchyFrequency n z) = broadCauchyKernel (n + 1) z := by
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · simpa only [broadCauchyFrequency, ite_eq_right hneg.not_gt] using fourier_lowerCauchyFrequency n z hneg
  · simpa only [broadCauchyFrequency, ite_eq_left hpos] using fourier_upperCauchyFrequency n z hpos

theorem fourierInv_broadCauchyKernel (n : ℕ) (hn : 0 < n) (z : ℂ) (hz : z.im ≠ 0) :
    𝓕⁻ (broadCauchyKernel (n + 1) z) = broadCauchyFrequency n z := by
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · simpa only [broadCauchyFrequency, ite_eq_right hneg.not_gt] using fourierInv_broadCauchyKernel_lower n hn z hneg
  · simpa only [broadCauchyFrequency, ite_eq_left hpos] using fourierInv_broadCauchyKernel_upper n hn z hpos

end

end MeyerGeneralProblem
