module

public import MeyerGeneralProblem.Distribution.BroadCauchyKernel
public import MeyerGeneralProblem.Distribution.DiscreteSupportPoisson
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-!
# The support Cauchy kernel normalized at height one

Subtracting the Cauchy kernel at `i` gives quadratic decay on the
real line. Its real part is half the difference of the two Poisson
kernels. This is the subtraction appropriate for the original
support-count detector.
-/

namespace MeyerGeneralProblem

noncomputable section

open Adaptive Asymptotics Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology

/-- The factor `1 / (2π i)` in the support Cauchy integral. -/
def supportCauchyConstant : ℂ :=
  Complex.ofReal ((2 * Real.pi)⁻¹) * (-Complex.I)

/-- The Cauchy test kernel with value zero at `i`. -/
def supportCauchyKernel (z : ℂ) (x : ℝ) : ℂ :=
  supportCauchyConstant * (broadCauchyKernel 1 z x - broadCauchyKernel 1 Complex.I x)

/-- The exact pole-variable derivative of the normalized Cauchy kernel. -/
def supportCauchyDerivative (z : ℂ) (x : ℝ) : ℂ :=
  supportCauchyConstant * broadCauchyKernel 2 z x

/-- Its derivative in the pole variable is the actual squared Cauchy kernel. -/
theorem hasDerivAt_supportCauchyKernel (z : ℂ) (hz : z.im ≠ 0) (x : ℝ) :
    HasDerivAt (fun w => supportCauchyKernel w x)
      (supportCauchyDerivative z x) z := by
  simpa only [supportCauchyKernel, supportCauchyDerivative, Nat.cast_one, one_mul] using
    ((hasDerivAt_broadCauchyKernel_pole 1 z hz x).sub_const
      (broadCauchyKernel 1 Complex.I x)).const_mul supportCauchyConstant

/-- The Poisson real part has the exact unit-height subtraction,
including at real arguments. -/
theorem re_supportCauchyKernel_of_im_nonneg (z : ℂ) (hz : 0 ≤ z.im) (x : ℝ) :
    (supportCauchyKernel z x).re =
      (cauchyPDFReal z.re z.im.toNNReal x - cauchyPDFReal 0 1 x) / 2 := by
  simp only [supportCauchyKernel, supportCauchyConstant, broadCauchyKernel, pow_one,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, neg_zero, zero_mul, mul_zero,
    zero_sub, Complex.sub_re, Complex.sub_im, Complex.inv_im, Complex.normSq_apply,
    neg_neg, cauchyPDFReal_def, Real.coe_toNNReal _ hz, NNReal.coe_one, sub_zero,
    pow_two, mul_one]
  ring

/-- The normalized real-part formula at positive height. -/
theorem re_supportCauchyKernel (z : ℂ) (hz : 0 < z.im) (x : ℝ) :
    (supportCauchyKernel z x).re =
      (cauchyPDFReal z.re z.im.toNNReal x - cauchyPDFReal 0 1 x) / 2 :=
  re_supportCauchyKernel_of_im_nonneg z hz.le x

/-- A first-power real-line weight bound for the off-real resolvent. -/
def inverseKernelBound (z : ℂ) : ℝ :=
  1 + (1 + ‖z‖) / |z.im|

/-- A real-line weight bound for the inverse kernel under a positive denominator gap. -/
theorem norm_broadCauchyKernel_one_mul_weight_le_of_gap (z : ℂ) (x : ℝ) {r R : ℝ}
    (hr : 0 < r) (hD : r ≤ ‖(x : ℂ) - z‖) (hR : ‖z‖ ≤ R) :
    ‖broadCauchyKernel 1 z x‖ * (1 + |x|) ≤ 1 + (1 + R) / r := by
  let d := ‖(x : ℂ) - z‖
  have hd : 0 < d := hr.trans_le hD
  have hSize : |x| ≤ d + R := by
    have h := norm_sub_norm_le (x : ℂ) z
    rw [Complex.norm_real, Real.norm_eq_abs] at h
    linarith only [h, hR]
  have hNonneg : 0 ≤ 1 + R := add_nonneg zero_le_one ((norm_nonneg z).trans hR)
  have hRatio : 1 + R ≤ (1 + R) / r * d := by
    calc
      1 + R = ((1 + R) / r) * r := (div_mul_cancel₀ _ hr.ne').symm
      _ ≤ ((1 + R) / r) * d := mul_le_mul_of_nonneg_left hD (div_nonneg hNonneg hr.le)
  rw [broadCauchyKernel, pow_one, norm_inv]
  change d⁻¹ * (1 + |x|) ≤ _
  rw [inv_mul_eq_div]
  apply (div_le_iff₀ hd).mpr
  rw [add_mul, one_mul]
  linarith only [hRatio, hSize]

private theorem norm_broadCauchyKernel_one_mul_weight_le (z : ℂ)
    (hz : z.im ≠ 0) (x : ℝ) :
    ‖broadCauchyKernel 1 z x‖ * (1 + |x|) ≤ inverseKernelBound z := by
  have hD : |z.im| ≤ ‖(x : ℂ) - z‖ := by
    simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] using
      Complex.abs_im_le_norm ((x : ℂ) - z)
  exact norm_broadCauchyKernel_one_mul_weight_le_of_gap z x (abs_pos.mpr hz) hD le_rfl

/-- The subtraction at `i` factors into the two inverse kernels. -/
theorem supportCauchyKernel_eq_subtraction_product (w : ℂ) (x : ℝ)
    (hw : (x : ℂ) - w ≠ 0) :
    supportCauchyKernel w x = supportCauchyConstant * (w - Complex.I) *
      (broadCauchyKernel 1 w x * broadCauchyKernel 1 Complex.I x) := by
  have hI : (x : ℂ) - Complex.I ≠ 0 := by
    intro h
    simpa using congrArg Complex.im h
  simp only [supportCauchyKernel, broadCauchyKernel, pow_one]
  field_simp [hw, hI]
  ring

/-- The subtraction at `i` gives two powers of real-line decay. -/
theorem norm_supportCauchyKernel_mul_weight_sq_le (z : ℂ) (hz : z.im ≠ 0) (x : ℝ) :
    ‖supportCauchyKernel z x‖ * (1 + |x|) ^ 2 ≤
      ‖supportCauchyConstant‖ * ‖z - Complex.I‖ * inverseKernelBound z * inverseKernelBound Complex.I := by
  have hden (w : ℂ) (hw : w.im ≠ 0) : (x : ℂ) - w ≠ 0 := by
    intro h
    exact hw (by simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im,
      neg_eq_zero] using congrArg Complex.im h)
  have hI : Complex.I.im ≠ 0 := by simp
  rw [supportCauchyKernel_eq_subtraction_product z x (hden z hz), norm_mul, norm_mul, norm_mul]
  calc
    _ = ‖supportCauchyConstant‖ * ‖z - Complex.I‖ *
        (‖broadCauchyKernel 1 z x‖ * (1 + |x|)) * (‖broadCauchyKernel 1 Complex.I x‖ * (1 + |x|)) := by
      ring
    _ ≤ _ := by
      gcongr
      · unfold inverseKernelBound
        positivity
      · exact norm_broadCauchyKernel_one_mul_weight_le z hz x
      · exact norm_broadCauchyKernel_one_mul_weight_le Complex.I hI x

/-- The normalized kernel is measurable on the actual test line. -/
theorem measurable_supportCauchyKernel (z : ℂ) : Measurable (supportCauchyKernel z) := by
  unfold supportCauchyKernel broadCauchyKernel
  fun_prop

/-- A quadratic inverse weight is bounded by the unit-height Poisson kernel. -/
theorem le_mul_poisson_one_of_weight_bound (x : ℝ) {v C : ℝ}
    (hC : 0 ≤ C) (hBound : v * (1 + |x|) ^ 2 ≤ C) :
    v ≤ (C * Real.pi) * cauchyPDFReal 0 1 x := by
  have hSquare : x ^ 2 + 1 ≤ (1 + |x|) ^ 2 := by
    rw [add_sq, sq_abs]
    nlinarith only [abs_nonneg x]
  calc
    _ ≤ C / (1 + |x|) ^ 2 := (le_div_iff₀ (by positivity)).mpr hBound
    _ ≤ C / (x ^ 2 + 1) := div_le_div_of_nonneg_left hC (by positivity) hSquare
    _ = (C * Real.pi) * cauchyPDFReal 0 1 x := by
      simp only [cauchyPDFReal_def, NNReal.coe_one, one_pow, sub_zero, mul_one, div_eq_mul_inv]
      calc
        C * (x ^ 2 + 1)⁻¹ = C * (Real.pi * Real.pi⁻¹) * (x ^ 2 + 1)⁻¹ := by
          rw [mul_inv_cancel₀ Real.pi_ne_zero, mul_one]
        _ = _ := by ring

private theorem norm_supportCauchyKernel_le_poisson_one (z : ℂ) (hz : z.im ≠ 0) (x : ℝ) :
    ‖supportCauchyKernel z x‖ ≤
      (‖supportCauchyConstant‖ * ‖z - Complex.I‖ * inverseKernelBound z *
        inverseKernelBound Complex.I * Real.pi) * cauchyPDFReal 0 1 x := by
  exact le_mul_poisson_one_of_weight_bound x
    (by unfold inverseKernelBound; positivity)
    (norm_supportCauchyKernel_mul_weight_sq_le z hz x)

/-- The normalized Cauchy kernel is absolutely integrable against the
actual locally finite support count at every off-real pole variable. -/
theorem integrable_supportCauchyKernel_discreteSupportCount
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : DistributionSupportedOn S.carrier T)
    {K : ℕ} (hCount : ∀ r, (S.carrier ∩ Ico r (r + 1)).ncard ≤ K)
    (z : ℂ) (hz : z.im ≠ 0) :
    Integrable (supportCauchyKernel z) (discreteSupportCount T) := by
  have hP := integrable_poisson_discreteSupportCount S T hT hCount 0 (γ := 1) one_pos
  exact (hP.const_mul _).mono' (measurable_supportCauchyKernel z).aestronglyMeasurable
    (ae_of_all _ (norm_supportCauchyKernel_le_poisson_one z hz))

/-- The absolutely convergent support Cauchy integral has exactly the
difference of the two real Poisson values, divided by two. -/
theorem re_integral_supportCauchyKernel_discreteSupportCount
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : DistributionSupportedOn S.carrier T)
    {K : ℕ} (hCount : ∀ r, (S.carrier ∩ Ico r (r + 1)).ncard ≤ K)
    (z : ℂ) (hz : 0 < z.im) :
    (∫ x, supportCauchyKernel z x ∂discreteSupportCount T).re =
      ((∫ x, cauchyPDFReal z.re z.im.toNNReal x ∂discreteSupportCount T) -
        (∫ x, cauchyPDFReal 0 1 x ∂discreteSupportCount T)) / 2 := by
  change Complex.reCLM (∫ x, supportCauchyKernel z x ∂discreteSupportCount T) = _
  rw [← Complex.reCLM.integral_comp_comm
    (integrable_supportCauchyKernel_discreteSupportCount S T hT hCount z hz.ne')]
  change (∫ x, (supportCauchyKernel z x).re ∂discreteSupportCount T) = _
  simp_rw [re_supportCauchyKernel z hz]
  rw [integral_div, integral_sub
    (integrable_poisson_discreteSupportCount S T hT hCount z.re (Real.toNNReal_pos.mpr hz))
    (integrable_poisson_discreteSupportCount S T hT hCount 0 (γ := 1) one_pos)]

/-- The normalized support Cauchy integral is complex differentiable
away from the real axis. Its derivative integrates the squared kernel. -/
theorem hasDerivAt_integral_supportCauchyKernel_discreteSupportCount
    (S : LocallyFiniteCarrier) (T : TemperedDistribution ℝ ℂ)
    (hT : DistributionSupportedOn S.carrier T)
    {K : ℕ} (hCount : ∀ r, (S.carrier ∩ Ico r (r + 1)).ncard ≤ K)
    (z : ℂ) (hz : z.im ≠ 0) :
    HasDerivAt (fun w => ∫ x, supportCauchyKernel w x ∂discreteSupportCount T)
      (∫ x, supportCauchyConstant * broadCauchyKernel 2 z x ∂discreteSupportCount T) z := by
  let δ := |z.im| / 2
  let R := ‖z‖ + 1
  let U := {w : ℂ | δ < |w.im|} ∩ {w : ℂ | ‖w‖ < R}
  let D := 1 + (1 + R) / δ
  have hδ : 0 < δ := half_pos (abs_pos.mpr hz)
  have hU : U ∈ 𝓝 z := by
    have hOpen : IsOpen U := (isOpen_lt continuous_const Complex.continuous_im.abs).inter
      (isOpen_lt continuous_norm continuous_const)
    exact hOpen.mem_nhds ⟨half_lt_self (abs_pos.mpr hz), show ‖z‖ < R from lt_add_one ‖z‖⟩
  have hNear (w : ℂ) (hw : w ∈ U) : w.im ≠ 0 ∧ inverseKernelBound w ≤ D := by
    have hIm : δ < |w.im| := hw.1
    have hNorm : ‖w‖ < R := hw.2
    refine ⟨abs_pos.mp (hδ.trans hIm), ?_⟩
    unfold inverseKernelBound D
    gcongr
  let F' (w : ℂ) (x : ℝ) := supportCauchyConstant * broadCauchyKernel 2 w x
  let C := ‖supportCauchyConstant‖ * D ^ 2
  have hBound (w : ℂ) (hw : w ∈ U) (x : ℝ) :
      ‖F' w x‖ ≤ (C * Real.pi) * cauchyPDFReal 0 1 x := by
    have hWeight := (norm_broadCauchyKernel_one_mul_weight_le w (hNear w hw).1 x).trans
      (hNear w hw).2
    apply le_mul_poisson_one_of_weight_bound x (by positivity)
    calc
      _ = ‖supportCauchyConstant‖ * (‖broadCauchyKernel 1 w x‖ * (1 + |x|)) ^ 2 := by
        simp only [F', norm_mul, broadCauchyKernel, pow_one, norm_pow]
        ring
      _ ≤ C := by
        unfold C
        gcongr
  have hF'Meas : Measurable (F' z) := by unfold F' broadCauchyKernel; fun_prop
  have hP := integrable_poisson_discreteSupportCount S T hT hCount 0 (γ := 1) one_pos
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := supportCauchyKernel) (F' := F') hU
    (Eventually.of_forall fun w => (measurable_supportCauchyKernel w).aestronglyMeasurable)
    (integrable_supportCauchyKernel_discreteSupportCount S T hT hCount z hz)
    hF'Meas.aestronglyMeasurable (ae_of_all _ fun x w hw => hBound w hw x)
    (hP.const_mul (C * Real.pi))
    (ae_of_all _ fun x w hw => hasDerivAt_supportCauchyKernel w (hNear w hw).1 x)).2

private theorem measurable_integral_real_of_measurable_measure {Θ : Type*}
    [MeasurableSpace Θ] {η : Θ → Measure ℝ} (hη : Measurable η)
    {g : ℝ → ℝ} (hg : Measurable g) (hInt : ∀ θ, Integrable g (η θ)) :
    Measurable (fun θ => ∫ x, g x ∂η θ) := by
  have hPos := (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hg)).comp hη
  have hNeg := (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hg.neg)).comp hη
  convert hPos.ennreal_toReal.sub hNeg.ennreal_toReal using 1
  funext θ
  exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hInt θ)

private theorem measurable_integral_complex_of_measurable_measure {Θ : Type*}
    [MeasurableSpace Θ] {η : Θ → Measure ℝ} (hη : Measurable η)
    {g : ℝ → ℂ} (hg : Measurable g) (hInt : ∀ θ, Integrable g (η θ)) :
    Measurable (fun θ => ∫ x, g x ∂η θ) := by
  have hRe : Measurable (fun θ => (∫ x, g x ∂η θ).re) := by
    convert measurable_integral_real_of_measurable_measure hη
      (Complex.continuous_re.measurable.comp hg)
      (fun θ => Complex.reCLM.integrable_comp (hInt θ)) using 1
    funext θ
    exact (Complex.reCLM.integral_comp_comm (hInt θ)).symm
  have hIm : Measurable (fun θ => (∫ x, g x ∂η θ).im) := by
    convert measurable_integral_real_of_measurable_measure hη
      (Complex.continuous_im.measurable.comp hg)
      (fun θ => Complex.imCLM.integrable_comp (hInt θ)) using 1
    funext θ
    exact (Complex.imCLM.integral_comp_comm (hInt θ)).symm
  have hEq (θ : Θ) :
      (Complex.ofReal (∫ x, g x ∂η θ).re) +
        (Complex.ofReal (∫ x, g x ∂η θ).im) * Complex.I = ∫ x, g x ∂η θ :=
    Complex.re_add_im _
  have hMeas : Measurable (fun θ =>
      Complex.ofReal (∫ x, g x ∂η θ).re + Complex.ofReal (∫ x, g x ∂η θ).im * Complex.I) :=
    (Complex.continuous_ofReal.measurable.comp hRe).add
      ((Complex.continuous_ofReal.measurable.comp hIm).mul_const Complex.I)
  simpa only [hEq] using hMeas


private theorem norm_supportCauchyDerivative_mul_weight_sq_le (z : ℂ) (hz : z.im ≠ 0) (x : ℝ) :
    ‖supportCauchyDerivative z x‖ * (1 + |x|) ^ 2 ≤ ‖supportCauchyConstant‖ * inverseKernelBound z ^ 2 := by
  calc
    _ = ‖supportCauchyConstant‖ * (‖broadCauchyKernel 1 z x‖ * (1 + |x|)) ^ 2 := by
      simp only [supportCauchyDerivative, norm_mul, broadCauchyKernel, pow_one, norm_pow]
      ring
    _ ≤ _ := by
      gcongr
      exact norm_broadCauchyKernel_one_mul_weight_le z hz x

private theorem norm_supportCauchyDerivative_le_poisson_one (z : ℂ) (hz : z.im ≠ 0) (x : ℝ) :
    ‖supportCauchyDerivative z x‖ ≤
      (‖supportCauchyConstant‖ * inverseKernelBound z ^ 2 * Real.pi) * cauchyPDFReal 0 1 x :=
  le_mul_poisson_one_of_weight_bound x (by positivity)
    (norm_supportCauchyDerivative_mul_weight_sq_le z hz x)

private theorem supportCauchyKernel_remainder (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) (x : ℝ) :
    supportCauchyKernel w x - supportCauchyKernel z x - (w - z) • supportCauchyDerivative z x =
      (w - z) ^ 2 * (broadCauchyKernel 1 w x * supportCauchyDerivative z x) := by
  have hden (u : ℂ) (hu : u.im ≠ 0) : (x : ℂ) - u ≠ 0 := by
    intro h
    exact hu (by simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im,
      neg_eq_zero] using congrArg Complex.im h)
  simp only [supportCauchyKernel, supportCauchyDerivative, broadCauchyKernel, pow_one, smul_eq_mul]
  field_simp [hden z hz, hden w hw]
  ring

private theorem norm_supportCauchyKernel_remainder_le (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (x : ℝ) :
    ‖supportCauchyKernel w x - supportCauchyKernel z x - (w - z) • supportCauchyDerivative z x‖ ≤
      (|w.im|⁻¹ * (‖supportCauchyConstant‖ * inverseKernelBound z ^ 2 * Real.pi) *
        ‖w - z‖ ^ 2) * cauchyPDFReal 0 1 x := by
  have hInv : ‖broadCauchyKernel 1 w x‖ ≤ |w.im|⁻¹ := by
    rw [broadCauchyKernel, pow_one, norm_inv]
    apply inv_anti₀ (abs_pos.mpr hw)
    simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] using
      Complex.abs_im_le_norm ((x : ℂ) - w)
  rw [supportCauchyKernel_remainder z w hz hw, norm_mul, norm_pow, norm_mul]
  calc
    _ ≤ ‖w - z‖ ^ 2 * (|w.im|⁻¹ *
        ((‖supportCauchyConstant‖ * inverseKernelBound z ^ 2 * Real.pi) * cauchyPDFReal 0 1 x)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact mul_le_mul hInv (norm_supportCauchyDerivative_le_poisson_one z hz x)
          (norm_nonneg _) (inv_nonneg.mpr (abs_nonneg _))
    _ = _ := by ring

private theorem measurable_supportCauchyDerivative (z : ℂ) : Measurable (supportCauchyDerivative z) := by
  unfold supportCauchyDerivative broadCauchyKernel
  fun_prop

section CauchyL2

variable {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
variable (S : Θ → LocallyFiniteCarrier) (T : Θ → TemperedDistribution ℝ ℂ)
variable (hT : ∀ θ, DistributionSupportedOn (S θ).carrier (T θ))
variable (hCont : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) → Continuous (fun θ => T θ f))
variable {K : ℕ} (hCount : ∀ θ r, ((S θ).carrier ∩ Ico r (r + 1)).ncard ≤ K)

omit [TopologicalSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ] in
include hT hCount in
private theorem exists_poisson_one_uniform_bound : ∃ M : ℝ, 0 ≤ M ∧
    ∀ θ, (∫ x, cauchyPDFReal 0 1 x ∂discreteSupportCount (T θ)) ≤ M := by
  obtain ⟨C, hC, hBound⟩ := exists_lintegral_poisson_bound_of_discreteSupportCount K (γ := 1) one_pos
  refine ⟨C.toReal, ENNReal.toReal_nonneg, fun θ => ?_⟩
  rw [integral_poisson_discreteSupportCount_eq _ _ one_pos]
  exact ENNReal.toReal_mono hC.ne (hBound (S θ) (T θ) (hT θ) (hCount θ) 0)

include hT hCont hCount

private theorem memLp_integral_discreteSupportCount_of_bound
    (ν : Measure Θ) [IsFiniteMeasure ν]
    {g : ℝ → ℂ} (hg : Measurable g) {B : ℝ} (hB : 0 ≤ B)
    (hDom : ∀ x, ‖g x‖ ≤ B * cauchyPDFReal 0 1 x) :
    MemLp (fun θ => ∫ x, g x ∂discreteSupportCount (T θ)) 2 ν := by
  have hP (θ : Θ) :=
    integrable_poisson_discreteSupportCount (S θ) (T θ) (hT θ) (hCount θ) 0 (γ := 1) one_pos
  have hInt (θ : Θ) : Integrable g (discreteSupportCount (T θ)) :=
    ((hP θ).const_mul B).mono' hg.aestronglyMeasurable (ae_of_all _ hDom)
  have hMeas := measurable_integral_complex_of_measurable_measure
    (measurable_discreteSupportCount S T hT hCont) hg hInt
  obtain ⟨M, _, hM⟩ := exists_poisson_one_uniform_bound S T hT hCount
  apply MemLp.of_bound hMeas.aestronglyMeasurable (B * M)
  filter_upwards with θ
  exact (norm_integral_le_of_norm_le ((hP θ).const_mul B) (ae_of_all _ hDom)).trans
    (by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left (hM θ) hB)

private theorem memLp_integral_supportCauchyKernel (ν : Measure Θ) [IsFiniteMeasure ν]
    (z : ℂ) (hz : z.im ≠ 0) :
    MemLp (fun θ => ∫ x, supportCauchyKernel z x ∂discreteSupportCount (T θ)) 2 ν :=
  memLp_integral_discreteSupportCount_of_bound S T hT hCont hCount ν (measurable_supportCauchyKernel z)
    (by unfold inverseKernelBound; positivity) (norm_supportCauchyKernel_le_poisson_one z hz)

private theorem memLp_integral_supportCauchyDerivative (ν : Measure Θ) [IsFiniteMeasure ν]
    (z : ℂ) (hz : z.im ≠ 0) :
    MemLp (fun θ => ∫ x, supportCauchyDerivative z x ∂discreteSupportCount (T θ)) 2 ν :=
  memLp_integral_discreteSupportCount_of_bound S T hT hCont hCount ν (measurable_supportCauchyDerivative z)
    (by positivity) (norm_supportCauchyDerivative_le_poisson_one z hz)

/-- The normalized Cauchy integral as an `L²` field over a family of
weakly continuous distributions with a common support count. -/
def supportCauchyL2 (ν : Measure Θ) [IsFiniteMeasure ν] (z : ℂ) : Lp ℂ 2 ν :=
  if hz : z.im ≠ 0 then (memLp_integral_supportCauchyKernel S T hT hCont hCount ν z hz).toLp _ else 0

/-- At each fixed off-real parameter the `L²` field is represented by
the actual normalized Cauchy integral. -/
theorem coeFn_supportCauchyL2 (ν : Measure Θ) [IsFiniteMeasure ν] (z : ℂ) (hz : z.im ≠ 0) :
    supportCauchyL2 S T hT hCont hCount ν z =ᵐ[ν]
      fun θ => ∫ x, supportCauchyKernel z x ∂discreteSupportCount (T θ) := by
  simp only [supportCauchyL2, dite_eq_left hz]
  exact MemLp.coeFn_toLp _

/-- The normalization height is the zero value of the subtracted Cauchy field. -/
theorem supportCauchyL2_at_I (ν : Measure Θ) [IsFiniteMeasure ν] :
    supportCauchyL2 S T hT hCont hCount ν Complex.I = 0 := by
  apply Lp.ext
  filter_upwards [coeFn_supportCauchyL2 S T hT hCont hCount ν Complex.I (by simp),
    Lp.coeFn_zero ℂ 2 ν] with θ hθ h0
  rw [hθ, h0]
  simp [supportCauchyKernel]

/-- The exact Cauchy integral is complex differentiable in the probability
`L²` norm at each off-real parameter. The derivative integrates the squared
kernel and the error has a uniform quadratic bound. -/
theorem differentiableAt_supportCauchyL2 (ν : Measure Θ) [IsProbabilityMeasure ν] (z : ℂ)
    (hz : z.im ≠ 0) : DifferentiableAt ℂ (supportCauchyL2 S T hT hCont hCount ν) z := by
  let Q := supportCauchyL2 S T hT hCont hCount ν
  let D (θ : Θ) := ∫ x, supportCauchyDerivative z x ∂discreteSupportCount (T θ)
  let Dz := (memLp_integral_supportCauchyDerivative S T hT hCont hCount ν z hz).toLp D
  have hDz : Dz =ᵐ[ν] D := MemLp.coeFn_toLp _
  refine (show HasDerivAt Q Dz z from hasDerivAt_iff_isLittleO_nhds_zero.mpr ?_).differentiableAt
  let δ := |z.im| / 2
  have hδ : 0 < δ := half_pos (abs_pos.mpr hz)
  let C := δ⁻¹ * (‖supportCauchyConstant‖ * inverseKernelBound z ^ 2 * Real.pi)
  have hC : 0 ≤ C := by positivity
  obtain ⟨M, hM0, hM⟩ := exists_poisson_one_uniform_bound S T hT hCount
  let R (a : ℂ) := Q (z + a) - Q z - a • Dz
  have hBig : R =O[𝓝 0] (fun a : ℂ => a ^ 2) := by
    refine isBigO_iff.mpr ⟨C * M, ?_⟩
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hδ] with a ha
    have ha' : ‖a‖ < δ := by simpa only [Metric.mem_ball, dist_zero_right] using ha
    have hδw : δ ≤ |(z + a).im| := by
      have hRev := abs_sub_abs_le_abs_sub z.im ((z + a).im)
      rw [Complex.add_im, sub_add_cancel_left, abs_neg] at hRev
      have hi := Complex.abs_im_le_norm a
      dsimp only [δ, Complex.add_im] at ha' ⊢
      linarith only [hRev, hi, ha']
    have hw := abs_pos.mp (hδ.trans_le hδw)
    have hBound (θ : Θ) :
        ‖(∫ x, supportCauchyKernel (z + a) x ∂discreteSupportCount (T θ)) -
          (∫ x, supportCauchyKernel z x ∂discreteSupportCount (T θ)) - a • D θ‖ ≤
          (C * ‖a‖ ^ 2) * M := by
      let η := discreteSupportCount (T θ)
      have hP := integrable_poisson_discreteSupportCount (S θ) (T θ) (hT θ) (hCount θ) 0 (γ := 1) one_pos
      have hDInt : Integrable (supportCauchyDerivative z) η :=
        (hP.const_mul _).mono' (measurable_supportCauchyDerivative z).aestronglyMeasurable
          (ae_of_all _ (norm_supportCauchyDerivative_le_poisson_one z hz))
      have hPoint (x : ℝ) :
          ‖supportCauchyKernel (z + a) x - supportCauchyKernel z x - a • supportCauchyDerivative z x‖ ≤
            (C * ‖a‖ ^ 2) * cauchyPDFReal 0 1 x := by
        have h := norm_supportCauchyKernel_remainder_le z (z + a) hz hw x
        rw [add_sub_cancel_left] at h
        refine h.trans ?_
        unfold C
        have hInv := inv_anti₀ hδ hδw
        have hP0 := (cauchyPDF_pos 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0) x).le
        gcongr
      change ‖(∫ x, supportCauchyKernel (z + a) x ∂η) - (∫ x, supportCauchyKernel z x ∂η) -
        a • (∫ x, supportCauchyDerivative z x ∂η)‖ ≤ _
      have h1 := integrable_supportCauchyKernel_discreteSupportCount (S θ) (T θ) (hT θ) (hCount θ) (z+a) hw
      have h2 := integrable_supportCauchyKernel_discreteSupportCount (S θ) (T θ) (hT θ) (hCount θ) z hz
      rw [← integral_smul, ← integral_sub h1 h2]
      change ‖(∫ x, (supportCauchyKernel (z + a) - supportCauchyKernel z) x ∂η) -
        (∫ x, (a • supportCauchyDerivative z) x ∂η)‖ ≤ _
      rw [← integral_sub (h1.sub h2) (hDInt.smul a)]
      exact (norm_integral_le_of_norm_le (hP.const_mul (C * ‖a‖ ^ 2)) (ae_of_all _ hPoint)).trans
        (by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left (hM θ) (by positivity))
    have hAe : ∀ᵐ θ ∂ν, ‖R a θ‖ ≤ (C * ‖a‖ ^ 2) * M := by
      filter_upwards [Lp.coeFn_sub (Q (z+a) - Q z) (a • Dz), Lp.coeFn_sub (Q (z+a)) (Q z),
        Lp.coeFn_smul a Dz, hDz, coeFn_supportCauchyL2 S T hT hCont hCount ν (z+a) hw,
        coeFn_supportCauchyL2 S T hT hCont hCount ν z hz] with θ hR hSub hSm hDθ hWθ hZθ
      change ‖(Q (z+a) - Q z - a • Dz) θ‖ ≤ _
      simp only [Pi.sub_apply, Pi.smul_apply] at hR hSub hSm
      rw [hR, hSub, hSm, hDθ, show Q (z+a) θ = _ from hWθ, show Q z θ = _ from hZθ]
      exact hBound θ
    have hNorm := Lp.norm_le_of_ae_bound (by positivity : 0 ≤ (C * ‖a‖ ^ 2) * M) hAe
    have hOne : measureUnivNNReal ν = 1 := by
      apply NNReal.eq
      simp [measureUnivNNReal]
    rw [hOne, NNReal.coe_one, Real.one_rpow, one_mul] at hNorm
    change ‖R a‖ ≤ (C * M) * ‖a ^ 2‖
    rw [norm_pow]
    exact hNorm.trans_eq (by ring)
  exact hBig.trans_isLittleO (isLittleO_pow_id (by norm_num))

end CauchyL2

end
end MeyerGeneralProblem
