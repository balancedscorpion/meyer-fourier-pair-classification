module

public import MeyerGeneralProblem.Distribution.GaussianHeatFourier
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Complex.SqrtDeriv
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Integrability.PosLog
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Function.JacobianOneDim

@[expose] public section

/-!
# Cauchy transforms of integrable real densities

Nonnegative densities yield holomorphic functions with nonnegative real
part in the upper half-plane. This allows mean-value estimates after
transport to the disk, including for signed densities by taking the
difference of their positive and negative parts.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

/-- The Cauchy transform with its real part equal to the unnormalized
Poisson integral on the upper half-plane. -/
def cauchyRealDensity (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, (Complex.I / (z - x)) * (f x : ℂ)

private theorem im_le_norm_sub_real (z : ℂ) (x : ℝ) : z.im ≤ ‖z - x‖ := by
  refine (le_abs_self z.im).trans ?_
  simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using
    Complex.abs_im_le_norm (z - x)

private theorem sub_real_ne_zero_of_im_pos {z : ℂ} (hz : 0 < z.im) (x : ℝ) :
    z - x ≠ 0 := norm_pos_iff.mp (hz.trans_le (im_le_norm_sub_real z x))

private theorem integrable_cauchyRealDensity_integrand {f : ℝ → ℝ} (hf : Integrable f)
    {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun x : ℝ => (Complex.I / (z - x)) * (f x : ℂ)) := by
  have hCont : Continuous (fun x : ℝ => Complex.I / (z - x)) :=
    continuous_const.div (by fun_prop) (sub_real_ne_zero_of_im_pos hz)
  refine (hf.norm.const_mul z.im⁻¹).mono'
    (hCont.aestronglyMeasurable.mul (hf.ofReal (𝕜 := ℂ)).aestronglyMeasurable) ?_
  filter_upwards with x
  rw [norm_mul, norm_div, Complex.norm_I, Complex.norm_real, one_div]
  exact mul_le_mul_of_nonneg_right
    (inv_anti₀ hz (im_le_norm_sub_real z x)) (norm_nonneg _)

/-- Only the imaginary height is needed for the Cauchy kernel bound. -/
theorem norm_cauchyRealDensity_le {f : ℝ → ℝ} (hf : Integrable f)
    {z : ℂ} (hz : 0 < z.im) :
    ‖cauchyRealDensity f z‖ ≤ z.im⁻¹ * (∫ x : ℝ, ‖f x‖) := by
  have hInt := integrable_cauchyRealDensity_integrand hf hz
  rw [cauchyRealDensity, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono hInt.norm
    (hf.norm.const_mul z.im⁻¹) fun x => ?_)
  rw [norm_mul, norm_div, Complex.norm_I, Complex.norm_real, one_div]
  exact mul_le_mul_of_nonneg_right
    (inv_anti₀ hz (im_le_norm_sub_real z x)) (norm_nonneg _)

/-- The Cauchy transform of a nonnegative density takes values in the
closed right half-plane. -/
theorem re_cauchyRealDensity_nonneg {f : ℝ → ℝ} (hf : Integrable f)
    (hNonneg : 0 ≤ᵐ[volume] f) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (cauchyRealDensity f z).re := by
  change 0 ≤ Complex.reCLM (∫ x : ℝ, (Complex.I / (z - x)) * (f x : ℂ))
  rw [← Complex.reCLM.integral_comp_comm (integrable_cauchyRealDensity_integrand hf hz)]
  apply integral_nonneg_of_ae
  filter_upwards [hNonneg] with x hx
  simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.div_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_div, zero_add,
    Complex.sub_im]
  exact mul_nonneg (div_nonneg hz.le (Complex.normSq_nonneg _)) hx

/-- The Cauchy transform is holomorphic at every positive height. -/
theorem differentiableOn_cauchyRealDensity {f : ℝ → ℝ} (hf : Integrable f) :
    DifferentiableOn ℂ (cauchyRealDensity f) {z : ℂ | 0 < z.im} := by
  intro z hz
  have hz' : 0 < z.im := hz
  let a := z.im / 2
  have ha : 0 < a := half_pos hz'
  let K (w : ℂ) (x : ℝ) := (Complex.I / (w - x)) * (f x : ℂ)
  let L (w : ℂ) (x : ℝ) := -Complex.I / (w - x) ^ 2 * (f x : ℂ)
  have hW {w : ℂ} (hw : w ∈ Metric.ball z a) : a < w.im := by
    have hDist := Metric.mem_ball.mp hw
    rw [dist_eq_norm] at hDist
    have hIm : z.im - w.im ≤ ‖w - z‖ := by
      calc
        z.im - w.im = -(w - z).im := by simp [Complex.sub_im]
        _ ≤ |(w - z).im| := neg_le_abs _
        _ ≤ _ := Complex.abs_im_le_norm _
    dsimp [a] at *
    linarith only [hDist, hIm]
  have hLp : Continuous (fun x : ℝ => -Complex.I / (z - x) ^ 2) :=
    continuous_const.div (by fun_prop) (fun x => pow_ne_zero _ (sub_real_ne_zero_of_im_pos hz' x))
  have hNear : ∀ᶠ w in 𝓝 z, w ∈ Metric.ball z a := Metric.ball_mem_nhds z ha
  have hDeriv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ)) (F := K) (F' := L)
    (Metric.ball_mem_nhds z ha)
    (hNear.mono fun w hw =>
      (integrable_cauchyRealDensity_integrand hf (ha.trans (hW hw))).aestronglyMeasurable)
    (integrable_cauchyRealDensity_integrand hf hz')
    (hLp.aestronglyMeasurable.mul (hf.ofReal (𝕜 := ℂ)).aestronglyMeasurable)
    (ae_of_all _ fun x w hw => by
      change ‖-Complex.I / (w - x) ^ 2 * (f x : ℂ)‖ ≤ (a ^ 2)⁻¹ * ‖f x‖
      rw [norm_mul, norm_div, norm_neg, Complex.norm_I, norm_pow, Complex.norm_real, one_div]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ (sq_pos_of_pos ha)
        (pow_le_pow_left₀ ha.le ((hW hw).le.trans (im_le_norm_sub_real w x)) _))
        (norm_nonneg _))
    (hf.norm.const_mul ((a ^ 2)⁻¹))
    (ae_of_all _ fun x w hw => by
      have hSub := sub_real_ne_zero_of_im_pos (ha.trans (hW hw)) x
      have hDiv := (hasDerivAt_const w Complex.I).div
        ((hasDerivAt_id w).sub_const (x : ℂ)) hSub
      simpa only [K, L, Pi.div_apply, id_eq, zero_mul, mul_one, zero_sub] using
        hDiv.mul_const (f x : ℂ))).2
  exact hDeriv.differentiableAt.differentiableWithinAt

/-- Cauchy transforms respect differences of integrable real densities. -/
theorem cauchyRealDensity_sub {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    {z : ℂ} (hz : 0 < z.im) :
    cauchyRealDensity (fun x => f x - g x) z = cauchyRealDensity f z - cauchyRealDensity g z := by
  simp only [cauchyRealDensity, Complex.ofReal_sub, mul_sub]
  exact integral_sub (integrable_cauchyRealDensity_integrand hf hz)
    (integrable_cauchyRealDensity_integrand hg hz)

/-- The cutoff-zero Fourier–Laplace integral is the normalized Cauchy
transform of the actual heated density. -/
theorem heatFourierLaplace_zero_eq_cauchyRealDensity {f : ℝ → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : 0 < z.im) :
    heatFourierLaplace t f 0 z = (↑(2 * Real.pi) : ℂ)⁻¹ *
      cauchyRealDensity (realGaussianSmoothing t f) z := by
  rw [heatFourierLaplace_eq_cauchyIntegral hf ht 0 hz, cauchyRealDensity, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, ← mul_assoc]
  congr 1
  have hp : (↑(2 * Real.pi) : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  have hx := sub_real_ne_zero_of_im_pos hz x
  field_simp [Complex.I_ne_zero]
  ring_nf
  simp [Complex.I_sq]

/-- Cayley map from the unit disk to the upper half-plane, taking zero
to i. -/
def cayleyToUpperHalfPlane (w : ℂ) : ℂ :=
  Complex.I * (1 + w) / (1 - w)

private theorem one_sub_ne_zero_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
  intro h
  have he : w = 1 := (sub_eq_zero.mp h).symm
  simp [he] at hw

/-- The Cayley map's imaginary part in disk coordinates. -/
theorem im_cayleyToUpperHalfPlane (w : ℂ) :
    (cayleyToUpperHalfPlane w).im = (1 - ‖w‖ ^ 2) / Complex.normSq (1 - w) := by
  rw [← Complex.normSq_eq_norm_sq, cayleyToUpperHalfPlane, Complex.div_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, zero_mul, one_mul, zero_add, zero_sub, Complex.normSq_apply w]
  ring

/-- The Cayley map takes every point of the open unit disk to positive
imaginary height. -/
theorem im_cayleyToUpperHalfPlane_pos {w : ℂ} (hw : ‖w‖ < 1) :
    0 < (cayleyToUpperHalfPlane w).im := by
  rw [im_cayleyToUpperHalfPlane]
  exact div_pos (sub_pos.mpr (by nlinarith [norm_nonneg w]))
    (Complex.normSq_pos.mpr (one_sub_ne_zero_of_norm_lt_one hw))

/-- The Cayley map is holomorphic on the open unit disk. -/
theorem differentiableOn_cayleyToUpperHalfPlane :
    DifferentiableOn ℂ cayleyToUpperHalfPlane (Metric.ball 0 1) := by
  unfold cayleyToUpperHalfPlane
  apply DifferentiableOn.div (by fun_prop) (by fun_prop)
  intro w hw
  apply one_sub_ne_zero_of_norm_lt_one
  simpa only [Metric.mem_ball, dist_zero_right] using hw

/-- The Cayley map extends holomorphically across any finite boundary
point of the disk. -/
theorem analyticAt_cayleyToUpperHalfPlane {w : ℂ} (hw : w ≠ 1) :
    AnalyticAt ℂ cayleyToUpperHalfPlane w := by
  unfold cayleyToUpperHalfPlane
  exact (analyticAt_const.mul (analyticAt_const.add analyticAt_id)).div
    (analyticAt_const.sub analyticAt_id) (sub_ne_zero.mpr (Ne.symm hw))

private theorem sqrt_norm_le_sqrt_two_mul_re_sqrt_add_one {z : ℂ} (hz : 0 ≤ z.re) :
    Real.sqrt ‖z‖ ≤ Real.sqrt 2 * ((1 + z).sqrt).re := by
  have hNorm : ‖z‖ ≤ ‖1 + z‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, zero_add]
    nlinarith only [hz]
  rw [Complex.sqrt, Complex.cpow_inv_two_re, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  apply Real.sqrt_le_sqrt
  simp only [Complex.add_re, Complex.one_re]
  linarith only [hNorm, hz]

private theorem re_sqrt_add_one_le_sqrt_one_add_norm (z : ℂ) :
    ((1 + z).sqrt).re ≤ Real.sqrt (1 + ‖z‖) := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  apply Real.sqrt_le_sqrt
  have hRe : (1 + z).re ≤ ‖1 + z‖ :=
    (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hNorm : ‖(1 : ℂ) + z‖ ≤ 1 + ‖z‖ := by
    simpa only [norm_one] using norm_add_le (1 : ℂ) z
  linarith only [hRe, hNorm]

/-- A holomorphic function with nonnegative real part on the disk has a
uniform bound on its radial half-moment. Only the value at the disk
center enters the bound. -/
theorem circleAverage_sqrt_norm_le_of_re_nonneg {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hPos : ∀ w ∈ Metric.ball 0 1, 0 ≤ (F w).re)
    {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) :
    Real.circleAverage (fun w => Real.sqrt ‖F w‖) 0 r ≤
      Real.sqrt 2 * Real.sqrt (1 + ‖F 0‖) := by
  let G (w : ℂ) := (1 + F w).sqrt
  have hG : DifferentiableOn ℂ G (Metric.ball 0 1) := by
    intro w hw
    have hSlit : (1 + F w) ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      rw [Complex.add_re, Complex.one_re]
      linarith only [hPos w hw]
    have hW : DifferentiableWithinAt ℂ (fun u : ℂ => 1 + F u) (Metric.ball 0 1) w :=
      (differentiableAt_const (c := (1 : ℂ))).differentiableWithinAt.add (hF w hw)
    exact (Complex.differentiableAt_sqrt hSlit).comp_differentiableWithinAt w hW
  have hClosed : Metric.closedBall (0 : ℂ) |r| ⊆ Metric.ball 0 1 := by
    rw [abs_of_nonneg hr]
    exact Metric.closedBall_subset_ball hr₁
  have hSphere : Metric.sphere (0 : ℂ) |r| ⊆ Metric.ball 0 1 :=
    Metric.sphere_subset_closedBall.trans hClosed
  have hGI : CircleIntegrable G 0 r := (hG.continuousOn.mono hSphere).circleIntegrable'
  have hAvg : Real.circleAverage (fun w => (G w).re) 0 r = (G 0).re := by
    change Real.circleAverage (Complex.reCLM ∘ G) 0 r = _
    rw [Complex.reCLM.circleAverage_comp_comm hGI, (hG.diffContOnCl_ball hClosed).circleAverage]
    rfl
  have hLeft : ContinuousOn (fun w => Real.sqrt ‖F w‖) (Metric.ball 0 1) :=
    Real.continuous_sqrt.comp_continuousOn hF.continuousOn.norm
  have hRight : ContinuousOn (fun w => Real.sqrt 2 * (G w).re) (Metric.ball 0 1) :=
    continuousOn_const.mul (Complex.continuous_re.comp_continuousOn hG.continuousOn)
  calc
    _ ≤ Real.circleAverage (fun w => Real.sqrt 2 * (G w).re) 0 r :=
      Real.circleAverage_mono (hLeft.mono hSphere).circleIntegrable'
        (hRight.mono hSphere).circleIntegrable'
        (fun w hw => sqrt_norm_le_sqrt_two_mul_re_sqrt_add_one (hPos w (hSphere hw)))
    _ = Real.sqrt 2 * (G 0).re := by
      change Real.circleAverage (fun w => Real.sqrt 2 • (G w).re) 0 r = _
      rw [Real.circleAverage_fun_smul, hAvg, smul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (re_sqrt_add_one_le_sqrt_one_add_norm (F 0)) (Real.sqrt_nonneg _)

private theorem differentiableOn_cauchyRealDensity_comp_cayley {f : ℝ → ℝ} (hf : Integrable f) :
    DifferentiableOn ℂ (cauchyRealDensity f ∘ cayleyToUpperHalfPlane) (Metric.ball 0 1) :=
  (differentiableOn_cauchyRealDensity hf).comp differentiableOn_cayleyToUpperHalfPlane
    (fun w hw => im_cayleyToUpperHalfPlane_pos (by
      simpa only [Metric.mem_ball, dist_zero_right] using hw))

/-- A nonnegative integrable real density gives a Cauchy transform with
uniformly bounded radial half-moments on the disk. -/
theorem circleAverage_sqrt_norm_cauchyRealDensity_le_of_nonneg {f : ℝ → ℝ}
    (hf : Integrable f) (hPos : 0 ≤ᵐ[volume] f) {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) :
    Real.circleAverage (fun w => Real.sqrt ‖cauchyRealDensity f (cayleyToUpperHalfPlane w)‖) 0 r ≤
      Real.sqrt 2 * Real.sqrt (1 + ∫ x : ℝ, ‖f x‖) := by
  refine (circleAverage_sqrt_norm_le_of_re_nonneg
    (differentiableOn_cauchyRealDensity_comp_cayley hf) (fun w hw => ?_) hr hr₁).trans ?_
  · exact re_cauchyRealDensity_nonneg hf hPos (im_cayleyToUpperHalfPlane_pos
      (by simpa only [Metric.mem_ball, dist_zero_right] using hw))
  · apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    apply Real.sqrt_le_sqrt (add_le_add (le_refl _) _)
    simpa [Function.comp_apply, cayleyToUpperHalfPlane] using
      norm_cauchyRealDensity_le hf (z := Complex.I) (by simp)

theorem sqrt_add_le_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt (add_nonneg ha hb)]
  nlinarith only [Real.sq_sqrt ha, Real.sq_sqrt hb,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- The radial half-moment estimate holds also for signed densities,
by applying the positive-real-part estimate to their two parts. -/
theorem circleAverage_sqrt_norm_cauchyRealDensity_le {f : ℝ → ℝ}
    (hf : Integrable f) {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) :
    Real.circleAverage (fun w => Real.sqrt ‖cauchyRealDensity f (cayleyToUpperHalfPlane w)‖) 0 r ≤
      2 * Real.sqrt 2 * Real.sqrt (1 + ∫ x : ℝ, ‖f x‖) := by
  let p (x : ℝ) := max (f x) 0
  let n (x : ℝ) := max (-f x) 0
  have hp : Integrable p := hf.pos_part
  have hn : Integrable n := hf.neg_part
  have hp₀ : ∀ x, 0 ≤ p x := fun x => le_max_right (f x) 0
  have hn₀ : ∀ x, 0 ≤ n x := fun x => le_max_right (-f x) 0
  have hpMass : (∫ x : ℝ, ‖p x‖) ≤ ∫ x : ℝ, ‖f x‖ := by
    refine integral_mono hp.norm hf.norm fun x => ?_
    rw [Real.norm_of_nonneg (hp₀ x), Real.norm_eq_abs]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hnMass : (∫ x : ℝ, ‖n x‖) ≤ ∫ x : ℝ, ‖f x‖ := by
    refine integral_mono hn.norm hf.norm fun x => ?_
    rw [Real.norm_of_nonneg (hn₀ x), Real.norm_eq_abs]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  have hSub : (fun x => p x - n x) = f := by
    funext x
    dsimp [p, n]
    rcases le_total 0 (f x) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_sub, neg_neg]
  let A (g : ℝ → ℝ) (w : ℂ) := Real.sqrt ‖cauchyRealDensity g (cayleyToUpperHalfPlane w)‖
  have hSphere : Metric.sphere (0 : ℂ) |r| ⊆ Metric.ball 0 1 := by
    rw [abs_of_nonneg hr]
    exact Metric.sphere_subset_closedBall.trans (Metric.closedBall_subset_ball hr₁)
  have hCont {g : ℝ → ℝ} (hg : Integrable g) : ContinuousOn (A g) (Metric.sphere 0 |r|) :=
    (Real.continuous_sqrt.comp_continuousOn
      (differentiableOn_cauchyRealDensity_comp_cayley hg).continuousOn.norm).mono hSphere
  have hPoint (w : ℂ) (hw : w ∈ Metric.sphere 0 |r|) : A f w ≤ A p w + A n w := by
    have hHeight := im_cayleyToUpperHalfPlane_pos (by
      simpa only [Metric.mem_ball, dist_zero_right] using hSphere hw)
    dsimp [A]
    rw [← hSub, cauchyRealDensity_sub hp hn hHeight]
    exact (Real.sqrt_le_sqrt (norm_sub_le _ _)).trans
      (sqrt_add_le_add_sqrt (norm_nonneg _) (norm_nonneg _))
  calc
    _ ≤ Real.circleAverage (fun w => A p w + A n w) 0 r :=
      Real.circleAverage_mono (hCont hf).circleIntegrable'
        ((hCont hp).add (hCont hn)).circleIntegrable' hPoint
    _ = Real.circleAverage (A p) 0 r + Real.circleAverage (A n) 0 r :=
      Real.circleAverage_fun_add (hCont hp).circleIntegrable' (hCont hn).circleIntegrable'
    _ ≤ _ := by
      have h₁ := (circleAverage_sqrt_norm_cauchyRealDensity_le_of_nonneg hp (ae_of_all _ hp₀) hr hr₁).trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (add_le_add (le_refl _) hpMass)) (Real.sqrt_nonneg _))
      have h₂ := (circleAverage_sqrt_norm_cauchyRealDensity_le_of_nonneg hn (ae_of_all _ hn₀) hr hr₁).trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (add_le_add (le_refl _) hnMass)) (Real.sqrt_nonneg _))
      simpa only [two_mul, add_mul] using add_le_add h₁ h₂

private theorem cauchyRealDensity_add_real (f : ℝ → ℝ) (a : ℝ) (z : ℂ) :
    cauchyRealDensity f (z + a) = cauchyRealDensity (fun x => f (x + a)) z := by
  unfold cauchyRealDensity
  rw [← integral_add_right_eq_self
    (fun x : ℝ => Complex.I / (z + (a : ℂ) - x) * (f x : ℂ)) a]
  apply integral_congr_ae
  filter_upwards with x
  rw [Complex.ofReal_add, add_sub_add_right_eq_sub]

/-- The analytic positive-frequency part of the heated density has
uniform radial half-moments for a disk chart centered at any real
translate of i. -/
theorem circleAverage_sqrt_norm_heatFourierLaplace_add_real_le {f : ℝ → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) (a : ℝ) {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) :
    Real.circleAverage (fun w => Real.sqrt ‖heatFourierLaplace t f 0
      (cayleyToUpperHalfPlane w + a)‖) 0 r ≤
      2 * Real.sqrt 2 * Real.sqrt (1 + ∫ x : ℝ, ‖f x‖) := by
  let g := realGaussianSmoothing t f
  let ga (x : ℝ) := g (x + a)
  have hg : Integrable g := integrable_realGaussianSmoothing hf ht
  have hga : Integrable ga := hg.comp_add_right a
  have hSphere : Metric.sphere (0 : ℂ) |r| ⊆ Metric.ball 0 1 := by
    rw [abs_of_nonneg hr]
    exact Metric.sphere_subset_closedBall.trans (Metric.closedBall_subset_ball hr₁)
  have hC := (differentiableOn_cauchyRealDensity_comp_cayley hga).continuousOn
  have hH := (differentiable_heatFourierLaplace hf ht 0).continuous.comp_continuousOn
    (differentiableOn_cayleyToUpperHalfPlane.continuousOn.add
      (continuousOn_const (c := (a : ℂ))))
  have hScale : ‖((↑(2 * Real.pi) : ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.two_pi_pos.le]
    exact inv_le_one_of_one_le₀ (by nlinarith [Real.pi_gt_three])
  refine (Real.circleAverage_mono
    ((Real.continuous_sqrt.comp_continuousOn hH.norm).mono hSphere).circleIntegrable'
    ((Real.continuous_sqrt.comp_continuousOn hC.norm).mono hSphere).circleIntegrable'
    (fun w hw => ?_)).trans ?_
  · apply Real.sqrt_le_sqrt
    change ‖heatFourierLaplace t f 0 (cayleyToUpperHalfPlane w + a)‖ ≤
      ‖cauchyRealDensity ga (cayleyToUpperHalfPlane w)‖
    have hHeight : 0 < (cayleyToUpperHalfPlane w + a).im := by
      rw [Complex.add_im, Complex.ofReal_im, add_zero]
      exact im_cayleyToUpperHalfPlane_pos (by
        simpa only [Metric.mem_ball, dist_zero_right] using hSphere hw)
    rw [heatFourierLaplace_zero_eq_cauchyRealDensity hf ht hHeight, cauchyRealDensity_add_real,
      norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hScale
  · have hMass : (∫ x : ℝ, ‖ga x‖) = ∫ x : ℝ, ‖g x‖ :=
      integral_add_right_eq_self (fun x : ℝ => ‖g x‖) a
    refine (circleAverage_sqrt_norm_cauchyRealDensity_le hga hr hr₁).trans ?_
    rw [hMass]
    exact
      (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (add_le_add (le_refl _) (integral_norm_realGaussianSmoothing_le hf ht)))
        (by positivity))

/-- The heat-time-uniform radial estimate in the disk chart centered at i. -/
theorem circleAverage_sqrt_norm_heatFourierLaplace_le {f : ℝ → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) :
    Real.circleAverage (fun w => Real.sqrt ‖heatFourierLaplace t f 0 (cayleyToUpperHalfPlane w)‖) 0 r ≤
      2 * Real.sqrt 2 * Real.sqrt (1 + ∫ x : ℝ, ‖f x‖) := by
  simpa only [Complex.ofReal_zero, add_zero] using
    circleAverage_sqrt_norm_heatFourierLaplace_add_real_le hf ht 0 hr hr₁

/-- Away from the full-turn endpoints, the unit circle avoids the Cayley pole. -/
theorem circleMap_unit_ne_one {θ : ℝ} (hθ : θ ∈ Ioo 0 (2 * Real.pi)) :
    circleMap 0 1 θ ≠ 1 := by
  intro he
  have hDist : |θ - 0| < 2 * Real.pi := by
    rw [sub_zero, abs_of_pos hθ.1]
    exact hθ.2
  have hz : θ = 0 := eq_of_circleMap_eq one_ne_zero hDist (he.trans (by simp [circleMap]))
  exact hθ.1.ne' hz

/-- The heat-time-uniform radial estimate passes to the boundary of the
disk. The Cayley map has only one exceptional boundary point, which is
removed from the angular integration interval. -/
theorem integrableOn_sqrt_norm_heatFourierLaplace_circle_boundary
    {f : ℝ → ℝ} (hf : Integrable f) {t : ℝ} (ht : 0 < t) :
    let A (θ : ℝ) :=
      Real.sqrt ‖heatFourierLaplace t f 0 (cayleyToUpperHalfPlane (circleMap 0 1 θ))‖
    IntegrableOn A (Ioo 0 (2 * Real.pi)) ∧
      (∫ θ in Ioo 0 (2 * Real.pi), A θ) ≤
        (2 * Real.pi) * (2 * Real.sqrt 2 * Real.sqrt (1 + ∫ x : ℝ, ‖f x‖)) := by
  let M := 2 * Real.sqrt 2 * Real.sqrt (1 + ∫ x : ℝ, ‖f x‖)
  let μ := volume.restrict (Ioo 0 (2 * Real.pi))
  let A (r θ : ℝ) :=
    Real.sqrt ‖heatFourierLaplace t f 0 (cayleyToUpperHalfPlane (circleMap 0 r θ))‖
  let r (n : ℕ) : ℝ := 1 - ((n : ℝ) + 1)⁻¹
  have hR₀ (n : ℕ) : 0 ≤ r n := by
    dsimp [r]
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]))
  have hR₁ (n : ℕ) : r n < 1 := sub_lt_self _ (inv_pos.mpr (by positivity))
  have hR : Tendsto r atTop (𝓝 1) := by
    have hInv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (by
        simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
          (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
    simpa only [r, sub_zero] using tendsto_const_nhds.sub hInv
  have hH := (differentiable_heatFourierLaplace hf ht 0).continuous
  have hMain : Continuous (fun z : ℂ => Real.sqrt ‖heatFourierLaplace t f 0 z‖) :=
    Real.continuous_sqrt.comp hH.norm
  have hContC {z : ℂ} (hz : z ≠ 1) : ContinuousAt cayleyToUpperHalfPlane z := by
    unfold cayleyToUpperHalfPlane
    exact (show ContinuousAt (fun w : ℂ => Complex.I * (1 + w)) z by fun_prop).div
      (by fun_prop) (sub_ne_zero.mpr hz.symm)
  have hContCircle (n : ℕ) : Continuous fun θ : ℝ => A (r n) θ := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    have hW : circleMap 0 (r n) θ ≠ 1 := by
      have h := norm_circleMap_zero (r n) θ
      rw [abs_of_nonneg (hR₀ n)] at h
      intro he
      rw [he, norm_one] at h
      exact (hR₁ n).ne h.symm
    exact hMain.continuousAt.comp ((hContC hW).comp (by fun_prop))
  have hI (n : ℕ) : Integrable (A (r n)) μ := by
    have hClosed : ContinuousOn (A (r n)) (Icc 0 (2 * Real.pi)) :=
      (hContCircle n).continuousOn
    exact hClosed.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hIntBound (n : ℕ) : (∫ θ, A (r n) θ ∂μ) ≤ (2 * Real.pi) * M := by
    have he := circleAverage_sqrt_norm_heatFourierLaplace_le hf ht (hR₀ n) (hR₁ n)
    change (2 * Real.pi)⁻¹ * (∫ θ in 0..2 * Real.pi, A (r n) θ) ≤ M at he
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le, integral_Ioc_eq_integral_Ioo] at he
    exact (inv_mul_le_iff₀ Real.two_pi_pos).mp he
  have hA : ∀ᵐ θ ∂μ, Tendsto (fun n : ℕ => A (r n) θ) atTop (𝓝 (A 1 θ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hCircle : ContinuousAt (fun a : ℝ => circleMap 0 a θ) 1 := by
      simp only [circleMap_zero]
      fun_prop
    exact (hMain.continuousAt.tendsto.comp ((hContC (circleMap_unit_ne_one hθ)).tendsto.comp
      (hCircle.tendsto.comp hR)))
  have hENN (n : ℕ) : (∫⁻ θ, ‖A (r n) θ‖ₑ ∂μ) ≤ ENNReal.ofReal ((2 * Real.pi) * M) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hI n)]
    have hN : (∫ θ, ‖A (r n) θ‖ ∂μ) = ∫ θ, A (r n) θ ∂μ :=
      integral_congr_ae (ae_of_all _ fun _ => Real.norm_of_nonneg (Real.sqrt_nonneg _))
    rw [hN]
    exact ENNReal.ofReal_le_ofReal (hIntBound n)
  have hL : liminf (fun n : ℕ => ∫⁻ θ, ‖A (r n) θ‖ₑ ∂μ) atTop ≤
      ENNReal.ofReal ((2 * Real.pi) * M) := by
    refine liminf_le_of_le (by isBoundedDefault) ?_
    intro b hb
    obtain ⟨n, hn⟩ := hb.exists
    exact hn.trans (hENN n)
  have hFin : Integrable (A 1) μ :=
    integrable_of_tendsto hA (fun n => (hI n).aestronglyMeasurable)
      (hL.trans_lt ENNReal.ofReal_lt_top).ne
  refine ⟨hFin, ?_⟩
  have hFatou := (lintegral_enorm_le_liminf_of_tendsto hA
    (fun n => (hI n).aestronglyMeasurable.aemeasurable.enorm)).trans hL
  rw [← ofReal_integral_norm_eq_lintegral_enorm hFin] at hFatou
  have hM₀ : 0 ≤ M := by dsimp [M]; positivity
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg Real.two_pi_pos.le hM₀)).mp
  simpa only [A, Real.norm_of_nonneg (Real.sqrt_nonneg _)] using hFatou

/-- The increasing angular coordinate of the real boundary of the Cayley chart. -/
def cayleyBoundaryAngle (x : ℝ) : ℝ := Real.pi + 2 * Real.arctan x

/-- The Cayley boundary angle is continuous on the real line. -/
theorem continuous_cayleyBoundaryAngle : Continuous cayleyBoundaryAngle :=
  continuous_const.add (continuous_const.mul Real.continuous_arctan)

private theorem image_cayleyBoundaryAngle :
    cayleyBoundaryAngle '' univ = Ioo 0 (2 * Real.pi) := by
  ext θ
  constructor
  · rintro ⟨x, _, rfl⟩
    obtain ⟨hl, hu⟩ := Real.arctan_mem_Ioo x
    dsimp [cayleyBoundaryAngle]
    exact ⟨by linarith only [hl], by linarith only [hu]⟩
  · intro hθ
    have hMem : (θ - Real.pi) / 2 ∈ range Real.arctan := by
      rw [Real.range_arctan]
      exact ⟨by linarith only [hθ.1], by linarith only [hθ.2]⟩
    obtain ⟨x, hx⟩ := hMem
    exact ⟨x, mem_univ _, by dsimp [cayleyBoundaryAngle]; linarith only [hx]⟩

private theorem injOn_cayleyBoundaryAngle : InjOn cayleyBoundaryAngle univ := by
  intro x _ y _ he
  apply Real.arctan_injective
  dsimp [cayleyBoundaryAngle] at he
  linarith only [he]

private theorem hasDerivWithinAt_cayleyBoundaryAngle (x : ℝ) :
    HasDerivWithinAt cayleyBoundaryAngle (2 / (1 + x ^ 2)) univ x := by
  unfold cayleyBoundaryAngle
  simpa only [mul_one_div] using
    (((Real.hasDerivAt_arctan x).const_mul 2).const_add Real.pi).hasDerivWithinAt

/-- The real boundary of the inverse Cayley map in angular coordinates. -/
theorem circleMap_cayleyBoundaryAngle (x : ℝ) :
    circleMap 0 1 (cayleyBoundaryAngle x) = ((x : ℂ) - Complex.I) / ((x : ℂ) + Complex.I) := by
  have hPos : 0 < 1 + x ^ 2 := by positivity
  have hRoot : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr hPos
  have hSq : (Real.sqrt (1 + x ^ 2)) ^ 2 = 1 + x ^ 2 := Real.sq_sqrt hPos.le
  have hCos : Real.cos (cayleyBoundaryAngle x) = (x ^ 2 - 1) / (x ^ 2 + 1) := by
    rw [cayleyBoundaryAngle, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_two_mul,
      Real.cos_arctan, div_pow, one_pow, hSq]
    field_simp
    ring
  have hSin : Real.sin (cayleyBoundaryAngle x) = -(2 * x) / (x ^ 2 + 1) := by
    rw [cayleyBoundaryAngle, Real.sin_add, Real.cos_pi, Real.sin_pi, Real.sin_two_mul,
      Real.sin_arctan, Real.cos_arctan]
    have hProd : Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + x ^ 2) = 1 + x ^ 2 := by
      simpa only [pow_two] using hSq
    calc
      _ = -(2 * x) / (Real.sqrt (1 + x ^ 2) * Real.sqrt (1 + x ^ 2)) := by ring
      _ = _ := by rw [hProd, add_comm]
  rw [circleMap_zero, Complex.ofReal_one, one_mul, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, hCos,
      Complex.div_re, Complex.sub_re, Complex.add_im, Complex.sub_im, zero_add,
      Complex.normSq_apply]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero, hSin,
      Complex.div_im, Complex.add_re, Complex.sub_re, Complex.sub_im, sub_zero,
      Complex.normSq_apply]
    ring

/-- The finite angular boundary coordinate inverts the Cayley map. -/
theorem cayleyToUpperHalfPlane_circleMap_cayleyBoundaryAngle (x : ℝ) :
    cayleyToUpperHalfPlane (circleMap 0 1 (cayleyBoundaryAngle x)) = (x : ℂ) := by
  have hDen : (x : ℂ) + Complex.I ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    simp at hh
  rw [cayleyToUpperHalfPlane, circleMap_cayleyBoundaryAngle x]
  have hBottom : (1 : ℂ) - ((x : ℂ) - Complex.I) / ((x : ℂ) + Complex.I) =
      (2 * Complex.I) / ((x : ℂ) + Complex.I) := by
    field_simp [hDen]
    ring
  have hTop : (1 : ℂ) + ((x : ℂ) - Complex.I) / ((x : ℂ) + Complex.I) =
      (2 * (x : ℂ)) / ((x : ℂ) + Complex.I) := by
    field_simp [hDen]
    ring
  rw [hBottom, hTop]
  field_simp [hDen, Complex.I_ne_zero]

/-- The angular Jacobian of the Cayley boundary coordinate is the
doubled Cauchy weight. -/
theorem lintegral_cayleyBoundaryAngle (P : ℝ → ℝ≥0∞) :
    (∫⁻ θ in Ioo 0 (2 * Real.pi), P θ) =
      ∫⁻ x : ℝ, ENNReal.ofReal (2 / (1 + x ^ 2)) * P (cayleyBoundaryAngle x) := by
  have hD : ∀ x ∈ (univ : Set ℝ),
      HasDerivWithinAt cayleyBoundaryAngle (2 / (1 + x ^ 2)) univ x :=
    fun x _ => hasDerivWithinAt_cayleyBoundaryAngle x
  have he := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    hD injOn_cayleyBoundaryAngle P
  simp only [image_cayleyBoundaryAngle, Measure.restrict_univ] at he
  exact he.trans (lintegral_congr (fun x => by rw [abs_of_nonneg (by positivity)]))

/-- The Bochner integral form of the Cayley boundary change of variables. -/
theorem integral_cayleyBoundaryAngle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ℝ → E) :
    (∫ θ in Ioo 0 (2 * Real.pi), P θ) =
      ∫ x : ℝ, (2 / (1 + x ^ 2) : ℝ) • P (cayleyBoundaryAngle x) := by
  have hD : ∀ x ∈ (univ : Set ℝ),
      HasDerivWithinAt cayleyBoundaryAngle (2 / (1 + x ^ 2)) univ x :=
    fun x _ => hasDerivWithinAt_cayleyBoundaryAngle x
  have he := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    hD injOn_cayleyBoundaryAngle P
  rw [image_cayleyBoundaryAngle, Measure.restrict_univ] at he
  refine he.trans (integral_congr_ae (ae_of_all _ fun x => ?_))
  dsimp only
  rw [abs_of_nonneg (by positivity)]

/-- Angular integrability gives weighted real-line integrability with
the exact Cayley factor of two in the integral. -/
theorem integrable_weighted_cayleyBoundary (Q : ℂ → ℝ)
    (hI : IntegrableOn (fun θ : ℝ => Q (cayleyToUpperHalfPlane (circleMap 0 1 θ)))
      (Ioo 0 (2 * Real.pi))) :
    let W (x : ℝ) := Q x / (1 + x ^ 2)
    Integrable W ∧ (∫ θ in Ioo 0 (2 * Real.pi), Q (cayleyToUpperHalfPlane (circleMap 0 1 θ))) =
      2 * (∫ x : ℝ, W x) := by
  let W (x : ℝ) := Q x / (1 + x ^ 2)
  let A (θ : ℝ) := Q (cayleyToUpperHalfPlane (circleMap 0 1 θ))
  have hJ : ∀ x ∈ (univ : Set ℝ),
      HasDerivWithinAt cayleyBoundaryAngle (2 / (1 + x ^ 2)) univ x :=
    fun x _ => hasDerivWithinAt_cayleyBoundaryAngle x
  have hEq (x : ℝ) : |2 / (1 + x ^ 2)| • A (cayleyBoundaryAngle x) = 2 * W x := by
    rw [abs_of_pos (by positivity), smul_eq_mul]
    dsimp only [A, W]
    rw [cayleyToUpperHalfPlane_circleMap_cayleyBoundaryAngle]
    ring
  have hIff := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    hJ injOn_cayleyBoundaryAngle A
  rw [image_cayleyBoundaryAngle] at hIff
  have hWI : Integrable (fun x => 2 * W x) := by
    simpa only [hEq, IntegrableOn, Measure.restrict_univ] using hIff.mp hI
  have hWInt : Integrable W := by
    convert hWI.const_mul (2 : ℝ)⁻¹ using 1
    funext x
    ring
  have hChange := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    hJ injOn_cayleyBoundaryAngle A
  rw [image_cayleyBoundaryAngle] at hChange
  simp only [hEq, setIntegral_univ, integral_const_mul] at hChange
  exact ⟨hWInt, hChange⟩

private theorem integrable_weighted_of_cayley_boundary_bound (Q : ℂ → ℝ) {B : ℝ}
    (hI : IntegrableOn (fun θ : ℝ => Q (cayleyToUpperHalfPlane (circleMap 0 1 θ)))
      (Ioo 0 (2 * Real.pi)))
    (hBound : (∫ θ in Ioo 0 (2 * Real.pi), Q (cayleyToUpperHalfPlane (circleMap 0 1 θ))) ≤
      2 * B) :
    let W (x : ℝ) := Q x / (1 + x ^ 2)
    Integrable W ∧ (∫ x : ℝ, W x) ≤ B := by
  obtain ⟨hWInt, hChange⟩ := integrable_weighted_cayleyBoundary Q hI
  exact ⟨hWInt, by linarith only [hChange, hBound]⟩

/-- The positive-frequency part of the heated density has a weighted
boundary half-moment on the real line, uniformly in positive heat time. -/
theorem integrable_sqrt_norm_heatFourierLaplace_weighted
    {f : ℝ → ℝ} (hf : Integrable f) {t : ℝ} (ht : 0 < t) :
    let W (x : ℝ) := Real.sqrt ‖heatFourierLaplace t f 0 x‖ / (1 + x ^ 2)
    Integrable W ∧
      (∫ x : ℝ, W x) ≤
        Real.pi * (2 * Real.sqrt 2 * Real.sqrt (1 + ∫ x : ℝ, ‖f x‖)) := by
  obtain ⟨hAInt, hABound⟩ := integrableOn_sqrt_norm_heatFourierLaplace_circle_boundary hf ht
  exact integrable_weighted_of_cayley_boundary_bound
    (fun z => Real.sqrt ‖heatFourierLaplace t f 0 z‖) hAInt (by
      rw [← mul_assoc]
      exact hABound)

private theorem log_max_one_le_mul_sqrt_add {u d : ℝ} (hu : 0 ≤ u) (hd : 0 < d) :
    Real.log (max 1 u) ≤ d * Real.sqrt u + 4 / d := by
  by_cases h : u ≤ 1
  · rw [max_eq_left h, Real.log_one]
    positivity
  have hu₀ : 0 < u := zero_lt_one.trans (lt_of_not_ge h)
  rw [max_eq_right (le_of_lt (lt_of_not_ge h))]
  let v := Real.sqrt (Real.sqrt u)
  have hv₂ : v ^ 2 = Real.sqrt u := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hLog : Real.log u ≤ 4 * v := by
    have hvPos : 0 < v := by dsimp [v]; positivity
    have hvLog : Real.log v = Real.log u / 2 / 2 := by
      dsimp [v]
      rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hu]
    linarith only [Real.log_le_sub_one_of_pos hvPos, hvLog]
  have hSq : (4 * v - d * v ^ 2) * d ≤ 4 := by
    nlinarith only [sq_nonneg (d * v - 2)]
  have hDiv := (le_div_iff₀ hd).mpr hSq
  rw [hv₂] at hDiv
  linarith only [hLog, hDiv]

private theorem tendsto_integral_inv_one_add_sq_tail :
    Tendsto (fun n : ℕ => ∫ x in {x : ℝ | (n : ℝ) ≤ |x|}, (1 + x ^ 2)⁻¹) atTop (𝓝 0) := by
  let S (n : ℕ) := {x : ℝ | (n : ℝ) ≤ |x|}
  have hS (n : ℕ) : MeasurableSet (S n) :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hAnti : Antitone S := by
    intro n m hnm x hx
    change (n : ℝ) ≤ |x|
    exact (Nat.cast_le.mpr hnm).trans (show (m : ℝ) ≤ |x| from hx)
  have hEmpty : (⋂ n : ℕ, S n) = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    exact hn.not_ge (mem_iInter.mp hx n)
  have hLim := tendsto_setIntegral_of_antitone hS hAnti
    ⟨0, integrable_inv_one_add_sq.integrableOn⟩
  simpa only [hEmpty, Measure.restrict_empty, integral_zero_measure] using hLim

/-- The positive part of the logarithm on the real boundary is integrable
against the Cauchy weight and has a tail uniformly small at all positive
heat times. -/
theorem exists_uniform_weighted_log_pos_tail_heatFourierLaplace
    {f : ℝ → ℝ} (hf : Integrable f) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ (t : ℝ), 0 < t →
      let V (x : ℝ) := Real.log (max 1 ‖heatFourierLaplace t f 0 x‖) / (1 + x ^ 2)
      Integrable V ∧ (∫ x in {x : ℝ | (N : ℝ) ≤ |x|}, V x) < ε := by
  let M := Real.pi * (2 * Real.sqrt 2 * Real.sqrt (1 + ∫ x : ℝ, ‖f x‖))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let d := ε / (2 * (M + 1))
  have hd : 0 < d := by dsimp [d]; positivity
  have hdM : d * M ≤ ε / 2 := by
    dsimp [d]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 2 * (M + 1))]
    nlinarith only [hε]
  have hFar := (tendsto_order.1 tendsto_integral_inv_one_add_sq_tail).2 (d * ε / 8)
    (by positivity)
  obtain ⟨N, hN, hNTail⟩ :=
    ((eventually_gt_atTop (0 : ℕ)).and hFar).exists
  refine ⟨N, hN, ?_⟩
  intro t ht
  let S := {x : ℝ | (N : ℝ) ≤ |x|}
  let V (x : ℝ) := Real.log (max 1 ‖heatFourierLaplace t f 0 x‖) / (1 + x ^ 2)
  let U (x : ℝ) := Real.sqrt ‖heatFourierLaplace t f 0 x‖ / (1 + x ^ 2)
  let W (x : ℝ) := (1 + x ^ 2)⁻¹
  obtain ⟨hU, hUBound⟩ := integrable_sqrt_norm_heatFourierLaplace_weighted hf ht
  have hW : Integrable W := integrable_inv_one_add_sq
  have hVCont : Continuous V := by
    have hG : Continuous (fun x : ℝ => ‖heatFourierLaplace t f 0 x‖) :=
      ((differentiable_heatFourierLaplace hf ht 0).continuous.comp Complex.continuous_ofReal).norm
    have hLog : Continuous (fun x : ℝ => Real.log (max 1 ‖heatFourierLaplace t f 0 x‖)) :=
      (continuous_const.max hG).log (fun x => ne_of_gt (zero_lt_one.trans_le (le_max_left _ _)))
    exact hLog.div (by fun_prop) (fun x => by positivity)
  have hV₀ (x : ℝ) : 0 ≤ V x :=
    div_nonneg (Real.log_nonneg (le_max_left _ _)) (by positivity)
  have hPoint (x : ℝ) : V x ≤ d * U x + (4 / d) * W x := by
    have he := div_le_div_of_nonneg_right (log_max_one_le_mul_sqrt_add
      (norm_nonneg (heatFourierLaplace t f 0 x)) hd) (by positivity : 0 ≤ 1 + x ^ 2)
    dsimp only [V, U, W]
    simpa only [div_eq_mul_inv, add_mul, mul_assoc] using he
  have hComp : Integrable (fun x => d * U x + (4 / d) * W x) :=
    (hU.const_mul d).add (hW.const_mul (4 / d))
  have hV : Integrable V := hComp.mono' hVCont.aestronglyMeasurable (ae_of_all _ fun x =>
    (Real.norm_of_nonneg (hV₀ x)).trans_le (hPoint x))
  refine ⟨hV, ?_⟩
  have hUS : (∫ x in S, U x) ≤ M :=
    (setIntegral_le_integral hU (ae_of_all _ fun _ => by dsimp only [U]; positivity)).trans hUBound
  have hWS : (4 / d) * (∫ x in S, W x) < ε / 2 := by
    calc
      _ < (4 / d) * (d * ε / 8) :=
        mul_lt_mul_of_pos_left hNTail (by positivity : 0 < 4 / d)
      _ = _ := by
        field_simp [hd.ne']
        ring
  calc
    _ ≤ ∫ x in S, d * U x + (4 / d) * W x :=
      integral_mono_of_nonneg (ae_of_all _ hV₀) hComp.integrableOn (ae_of_all _ hPoint)
    _ = d * (∫ x in S, U x) + (4 / d) * (∫ x in S, W x) := by
      rw [integral_add (hU.const_mul d).integrableOn (hW.const_mul (4 / d)).integrableOn,
        integral_const_mul, integral_const_mul]
    _ < ε := by linarith only [mul_le_mul_of_nonneg_left hUS hd.le, hdM, hWS]

/-- A uniform radial bound for the negative logarithm controls its
weighted total on the real boundary of a translated Cayley chart. -/
theorem integrable_weighted_neg_log_of_uniform_radial
    {H : ℂ → ℂ} (hH : Differentiable ℂ H) (a : ℝ) {C : ℝ}
    (hBound : ∀ r : ℝ, 0 < r → r < 1 →
      Real.circleAverage (fun w => Real.posLog ‖H (cayleyToUpperHalfPlane w + a)‖⁻¹) 0 r ≤ C) :
    let W (x : ℝ) := Real.posLog ‖H ((x : ℂ) + a)‖⁻¹ / (1 + x ^ 2)
    Integrable W ∧ (∫ x : ℝ, W x) ≤ Real.pi * max C 0 := by
  let F (w : ℂ) := H (cayleyToUpperHalfPlane w + a)
  let V (r θ : ℝ) := Real.posLog ‖F (circleMap 0 r θ)‖⁻¹
  let ν := volume.restrict (Ioo 0 (2 * Real.pi))
  let r (n : ℕ) := 1 - ((n : ℝ) + 2)⁻¹
  let B := (2 * Real.pi) * max C 0
  have hB : 0 ≤ B := mul_nonneg Real.two_pi_pos.le (le_max_right _ _)
  have hR₀ (n : ℕ) : 0 < r n := by
    dsimp [r]
    apply sub_pos.mpr (inv_lt_one_of_one_lt₀ ?_)
    linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hR₁ (n : ℕ) : r n < 1 := sub_lt_self _ (inv_pos.mpr (by positivity))
  have hR : Tendsto r atTop (𝓝 1) := by
    have hInv : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (by
        simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
          (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 2))
    simpa only [r, sub_zero] using tendsto_const_nhds.sub hInv
  have hF : DifferentiableOn ℂ F (Metric.ball 0 1) :=
    hH.comp_differentiableOn
      (differentiableOn_cayleyToUpperHalfPlane.add (differentiableOn_const (a : ℂ)))
  have hPos (q θ : ℝ) : 0 ≤ V q θ := Real.posLog_nonneg
  have hMeas (q : ℝ) : Measurable (V q) := by
    have hC : Measurable cayleyToUpperHalfPlane := by
      unfold cayleyToUpperHalfPlane
      exact (measurable_const.mul (measurable_const.add measurable_id)).div
        (measurable_const.sub measurable_id)
    have hInner : Measurable (fun θ : ℝ => F (circleMap 0 q θ)) :=
      hH.continuous.measurable.comp
        ((hC.comp ((continuous_circleMap 0 q).measurable)).add measurable_const)
    exact measurable_const.max (Real.measurable_log.comp hInner.norm.inv)
  have hI (n : ℕ) : Integrable (V (r n)) ν := by
    have hSub : Metric.sphere (0 : ℂ) |r n| ⊆ Metric.ball 0 1 := by
      rw [abs_of_pos (hR₀ n)]
      exact Metric.sphere_subset_closedBall.trans (Metric.closedBall_subset_ball (hR₁ n))
    have hM : MeromorphicOn F (Metric.sphere 0 |r n|) :=
      ((hF.analyticOnNhd Metric.isOpen_ball).mono hSub).meromorphicOn
    have hInv : CircleIntegrable (fun w => Real.posLog ‖F w‖⁻¹) 0 (r n) := by
      simpa only [Pi.inv_apply, norm_inv] using hM.inv.circleIntegrable_posLog_norm
    exact hInv.1.mono_set Ioo_subset_Ioc_self
  have hEnn (n : ℕ) : (∫⁻ θ, ENNReal.ofReal (V (r n) θ) ∂ν) ≤ ENNReal.ofReal B := by
    have hReal := (hBound (r n) (hR₀ n) (hR₁ n)).trans (le_max_left C 0)
    change (2 * Real.pi)⁻¹ * (∫ θ in 0..2 * Real.pi, V (r n) θ) ≤ max C 0 at hReal
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le, integral_Ioc_eq_integral_Ioo] at hReal
    rw [← ofReal_integral_eq_lintegral_ofReal (hI n) (ae_of_all _ (hPos _))]
    exact ENNReal.ofReal_le_ofReal ((inv_mul_le_iff₀ Real.two_pi_pos).mp hReal)
  have hPoint : ∀ᵐ θ ∂ν, ENNReal.ofReal (V 1 θ) ≤
      liminf (fun n : ℕ => ENNReal.ofReal (V (r n) θ)) atTop := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    by_cases h₀ : F (circleMap 0 1 θ) = 0
    · simp only [V, h₀, norm_zero, inv_zero, Real.posLog_zero, ENNReal.ofReal_zero, zero_le]
    have hc : ContinuousAt cayleyToUpperHalfPlane (circleMap 0 1 θ) := by
      unfold cayleyToUpperHalfPlane
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      exact sub_ne_zero.mpr (circleMap_unit_ne_one hθ).symm
    have hCircle : ContinuousAt (fun b : ℝ => circleMap 0 b θ) 1 := by
      simp only [circleMap_zero]
      fun_prop
    have hFAt : ContinuousAt F (circleMap 0 1 θ) :=
      hH.continuous.continuousAt.comp (hc.add continuousAt_const)
    have hArg : Tendsto (fun n : ℕ => F (circleMap 0 (r n) θ)) atTop
        (𝓝 (F (circleMap 0 1 θ))) :=
      hFAt.tendsto.comp (hCircle.tendsto.comp hR)
    have hLog : ContinuousAt (fun z : ℂ => Real.posLog ‖z‖⁻¹) (F (circleMap 0 1 θ)) := by
      have hN := norm_ne_zero_iff.mpr h₀
      unfold Real.posLog
      have hInv : ContinuousAt (fun z : ℂ => ‖z‖⁻¹) (F (circleMap 0 1 θ)) :=
        continuous_norm.continuousAt.inv₀ hN
      have hReal : ContinuousAt (fun z : ℂ => Real.log (‖z‖⁻¹)) (F (circleMap 0 1 θ)) :=
        (Real.continuousAt_log (inv_ne_zero hN)).comp_of_eq hInv rfl
      exact continuousAt_const.max hReal
    exact ((ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (hLog.tendsto.comp hArg)).liminf_eq).ge
  have hLimBound : liminf (fun n : ℕ => ∫⁻ θ, ENNReal.ofReal (V (r n) θ) ∂ν) atTop ≤
      ENNReal.ofReal B := by
    refine liminf_le_of_le (by isBoundedDefault) ?_
    intro b hb
    obtain ⟨n, hn⟩ := hb.exists
    exact hn.trans (hEnn n)
  have hFatou : (∫⁻ θ, ENNReal.ofReal (V 1 θ) ∂ν) ≤ ENNReal.ofReal B :=
    (lintegral_mono_ae hPoint).trans
      ((lintegral_liminf_le (fun n => ENNReal.measurable_ofReal.comp (hMeas (r n)))).trans hLimBound)
  have hAng : Integrable (V 1) ν := by
    refine ⟨(hMeas 1).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm,
      lintegral_enorm_of_ae_nonneg (ae_of_all _ (hPos 1))]
    exact hFatou.trans_lt ENNReal.ofReal_lt_top
  have hAngBound : (∫ θ, V 1 θ ∂ν) ≤ B := by
    apply (ENNReal.ofReal_le_ofReal_iff hB).mp
    rw [ofReal_integral_eq_lintegral_ofReal hAng (ae_of_all _ (hPos 1))]
    exact hFatou
  exact integrable_weighted_of_cayley_boundary_bound
    (fun z => Real.posLog ‖H (z + a)‖⁻¹) hAng (by
      rw [← mul_assoc]
      exact hAngBound)

end
end MeyerGeneralProblem
