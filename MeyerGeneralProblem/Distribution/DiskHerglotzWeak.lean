module

public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Complex.Poisson
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

@[expose] public section

/-!
# Weak bounds for Herglotz integrals on the disk

A fractional linear transform of a holomorphic function with
nonnegative real part gives a weak bound by the mean-value theorem.
This bounds the harmonic conjugate of signed boundary data by
splitting the data into its positive and negative parts.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

/-- Angular Lebesgue measure on one traversal of the circle. -/
def diskAngleMeasure : Measure ℝ :=
  volume.restrict (Ioo 0 (2 * Real.pi))

private theorem add_const_ne_zero_of_re_nonneg {z : ℂ} {L : ℝ}
    (hL : 0 < L) (hz : 0 ≤ z.re) : (L : ℂ) + z ≠ 0 := by
  intro h
  have he := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at he
  linarith only [hL, hz, he]

private theorem re_div_add_const_nonneg {z : ℂ} {L : ℝ}
    (hL : 0 < L) (hz : 0 ≤ z.re) : 0 ≤ (z / ((L : ℂ) + z)).re := by
  rw [Complex.div_re, Complex.add_re, Complex.ofReal_re, Complex.add_im,
    Complex.ofReal_im, zero_add, ← add_div]
  apply div_nonneg _ (Complex.normSq_nonneg _)
  exact add_nonneg (mul_nonneg hz (add_nonneg hL.le hz)) (mul_self_nonneg _)

private theorem half_le_re_div_add_const_of_le_norm {z : ℂ} {L : ℝ}
    (hL : 0 < L) (hz : 0 ≤ z.re) (hN : L ≤ ‖z‖) :
    (1 / 2 : ℝ) ≤ (z / ((L : ℂ) + z)).re := by
  have hSq : L ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ hL.le hN _
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hSq
  rw [Complex.div_re, ← add_div]
  apply (le_div_iff₀ (Complex.normSq_pos.mpr (add_const_ne_zero_of_re_nonneg hL hz))).mpr
  simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re, Complex.add_im,
    Complex.ofReal_im, zero_add]
  nlinarith only [hSq]

private theorem re_div_add_const_le_norm_div {z : ℂ} {L : ℝ}
    (hL : 0 < L) (hz : 0 ≤ z.re) : (z / ((L : ℂ) + z)).re ≤ ‖z‖ / L := by
  have hB : L ≤ ‖(L : ℂ) + z‖ := by
    calc
      _ ≤ ((L : ℂ) + z).re := by
        rw [Complex.add_re, Complex.ofReal_re]
        linarith only [hz]
      _ ≤ _ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
  calc
    _ ≤ ‖z / ((L : ℂ) + z)‖ :=
      (le_abs_self _).trans (Complex.abs_re_le_norm _)
    _ = ‖z‖ / ‖(L : ℂ) + z‖ := norm_div _ _
    _ ≤ _ := div_le_div_of_nonneg_left (norm_nonneg _) hL hB

/-- Angular weak estimate for the norm of a holomorphic function with
nonnegative real part on the disk. Only its center value enters. -/
theorem diskAngleMeasure_le_norm_superlevel_of_re_nonneg {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hPos : ∀ w ∈ Metric.ball 0 1, 0 ≤ (F w).re)
    {r L : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) (hL : 0 < L) :
    diskAngleMeasure {θ | L ≤ ‖F (circleMap 0 r θ)‖} ≤
      ENNReal.ofReal (4 * Real.pi * (‖F 0‖ / L)) := by
  let G (w : ℂ) := F w / ((L : ℂ) + F w)
  let V (θ : ℝ) := 2 * (G (circleMap 0 r θ)).re
  let ν := diskAngleMeasure
  have hG : DifferentiableOn ℂ G (Metric.ball 0 1) :=
    hF.div ((differentiableOn_const (L : ℂ)).add hF)
      (fun w hw => add_const_ne_zero_of_re_nonneg hL (hPos w hw))
  have hClosed : Metric.closedBall (0 : ℂ) |r| ⊆ Metric.ball 0 1 := by
    rw [abs_of_nonneg hr]
    exact Metric.closedBall_subset_ball hr₁
  have hSphere : Metric.sphere (0 : ℂ) |r| ⊆ Metric.ball 0 1 :=
    Metric.sphere_subset_closedBall.trans hClosed
  have hCircle (θ : ℝ) : circleMap 0 r θ ∈ Metric.ball 0 1 :=
    hSphere (circleMap_mem_sphere' 0 r θ)
  have hV : Continuous V :=
    continuous_const.mul (Complex.continuous_re.comp (hG.continuousOn.comp_continuous
      (continuous_circleMap 0 r) hCircle))
  have hV₀ (θ : ℝ) : 0 ≤ V θ :=
    mul_nonneg (by norm_num) (re_div_add_const_nonneg hL (hPos _ (hCircle θ)))
  have hVInt : Integrable V ν := by
    have hI : ContinuousOn V (Icc 0 (2 * Real.pi)) := hV.continuousOn
    exact hI.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hGI : CircleIntegrable G 0 r := (hG.continuousOn.mono hSphere).circleIntegrable'
  have hAvg : Real.circleAverage (fun w => (G w).re) 0 r = (G 0).re := by
    change Real.circleAverage (Complex.reCLM ∘ G) 0 r = _
    rw [Complex.reCLM.circleAverage_comp_comm hGI, (hG.diffContOnCl_ball hClosed).circleAverage]
    rfl
  have hCenter : (G 0).re ≤ ‖F 0‖ / L :=
    re_div_add_const_le_norm_div hL (hPos 0 (Metric.mem_ball_self zero_lt_one))
  have hI : (∫ θ : ℝ, V θ ∂ν) = 4 * Real.pi * (G 0).re := by
    change (2 * Real.pi)⁻¹ * (∫ θ in 0..2 * Real.pi, (G (circleMap 0 r θ)).re) = _ at hAvg
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le, integral_Ioc_eq_integral_Ioo] at hAvg
    have hEq := congrArg (fun u : ℝ => (2 * Real.pi) * u) hAvg
    rw [← mul_assoc, mul_inv_cancel₀ Real.two_pi_pos.ne', one_mul] at hEq
    change (∫ θ in Ioo 0 (2 * Real.pi), 2 * (G (circleMap 0 r θ)).re) = _
    rw [integral_const_mul, hEq]
    ring
  calc
    _ ≤ ∫⁻ θ, ENNReal.ofReal (V θ) ∂ν := by
      apply meas_le_lintegral₀ (ENNReal.measurable_ofReal.comp hV.measurable).aemeasurable
      intro θ hθ
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      have h := half_le_re_div_add_const_of_le_norm hL (hPos _ (hCircle θ)) hθ
      change 1 ≤ 2 * (G (circleMap 0 r θ)).re
      linarith only [h]
    _ = ENNReal.ofReal (4 * Real.pi * (G 0).re) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hVInt (ae_of_all _ hV₀), hI]
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hCenter (by positivity))

/-- Angular weak estimate for the imaginary part of the difference of
two holomorphic functions with nonnegative real part. -/
theorem diskAngleMeasure_lt_abs_im_sub_superlevel_of_re_nonneg {F G : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hG : DifferentiableOn ℂ G (Metric.ball 0 1))
    (hF₀ : ∀ w ∈ Metric.ball 0 1, 0 ≤ (F w).re)
    (hG₀ : ∀ w ∈ Metric.ball 0 1, 0 ≤ (G w).re)
    {r L : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) (hL : 0 < L) :
    diskAngleMeasure {θ | L < |(F (circleMap 0 r θ) - G (circleMap 0 r θ)).im|} ≤
      ENNReal.ofReal (8 * Real.pi * ((‖F 0‖ + ‖G 0‖) / L)) := by
  let E₁ := {θ : ℝ | L / 2 ≤ ‖F (circleMap 0 r θ)‖}
  let E₂ := {θ : ℝ | L / 2 ≤ ‖G (circleMap 0 r θ)‖}
  have hSubset : {θ : ℝ | L < |(F (circleMap 0 r θ) - G (circleMap 0 r θ)).im|} ⊆ E₁ ∪ E₂ := by
    intro θ hθ
    change L < |(F (circleMap 0 r θ) - G (circleMap 0 r θ)).im| at hθ
    by_contra hN
    have hN₁ : θ ∉ E₁ := fun h => hN (Or.inl h)
    have hN₂ : θ ∉ E₂ := fun h => hN (Or.inr h)
    have h₁ : ‖F (circleMap 0 r θ)‖ < L / 2 := lt_of_not_ge hN₁
    have h₂ : ‖G (circleMap 0 r θ)‖ < L / 2 := lt_of_not_ge hN₂
    have hTri := (Complex.abs_im_le_norm (F (circleMap 0 r θ) -
      G (circleMap 0 r θ))).trans (norm_sub_le _ _)
    linarith only [hθ, h₁, h₂, hTri]
  calc
    _ ≤ diskAngleMeasure (E₁ ∪ E₂) := measure_mono hSubset
    _ ≤ diskAngleMeasure E₁ + diskAngleMeasure E₂ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (4 * Real.pi * (‖F 0‖ / (L / 2))) +
        ENNReal.ofReal (4 * Real.pi * (‖G 0‖ / (L / 2))) :=
      add_le_add (diskAngleMeasure_le_norm_superlevel_of_re_nonneg hF hF₀ hr hr₁ (half_pos hL))
        (diskAngleMeasure_le_norm_superlevel_of_re_nonneg hG hG₀ hr hr₁ (half_pos hL))
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- The disk Herglotz integral with a unit-circle parameterization and
signed real density in the parameter variable. -/
def diskHerglotzIntegral (ζ : ℝ → ℂ) (g : ℝ → ℝ) (w : ℂ) : ℂ :=
  ∫ x : ℝ, herglotzRieszKernel 0 w (ζ x) * (g x : ℂ)

private theorem herglotzRieszKernel_zero (z w : ℂ) :
    herglotzRieszKernel 0 w z = (z + w) / (z - w) := by
  simp [herglotzRieszKernel_def]

private theorem unit_sub_ne_zero {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ < 1) :
    z - w ≠ 0 := by
  intro h
  rw [sub_eq_zero.mp h] at hz
  exact hw.ne hz

private theorem integrable_diskHerglotz_integrand
    {ζ : ℝ → ℂ} (hζ : Measurable ζ) (hUnit : ∀ x, ‖ζ x‖ = 1)
    {g : ℝ → ℝ} (hg : Integrable g) {w : ℂ} (hw : ‖w‖ < 1) :
    Integrable (fun x : ℝ => ((ζ x + w) / (ζ x - w)) * (g x : ℂ)) := by
  have hC : Measurable (fun x : ℝ => (ζ x + w) / (ζ x - w)) :=
    (hζ.add measurable_const).div (hζ.sub measurable_const)
  refine (hg.norm.const_mul ((1 + ‖w‖) / (1 - ‖w‖))).mono'
    (hC.aestronglyMeasurable.mul (hg.ofReal (𝕜 := ℂ)).aestronglyMeasurable) ?_
  filter_upwards with x
  rw [norm_mul, Complex.norm_real, norm_div]
  have hDen : 1 - ‖w‖ ≤ ‖ζ x - w‖ := by
    simpa only [hUnit x] using norm_sub_norm_le (ζ x) w
  have hNum : ‖ζ x + w‖ ≤ 1 + ‖w‖ := by
    simpa only [hUnit x] using norm_add_le (ζ x) w
  exact mul_le_mul_of_nonneg_right
    (div_le_div₀ (by positivity) hNum (sub_pos.mpr hw) hDen) (norm_nonneg _)

/-- The Herglotz integral of an integrable density is holomorphic in
the open unit disk. -/
theorem differentiableOn_diskHerglotzIntegral
    {ζ : ℝ → ℂ} (hζ : Measurable ζ) (hUnit : ∀ x, ‖ζ x‖ = 1)
    {g : ℝ → ℝ} (hg : Integrable g) :
    DifferentiableOn ℂ (diskHerglotzIntegral ζ g) (Metric.ball 0 1) := by
  intro w hw
  have hw' : ‖w‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hw
  let a := (1 - ‖w‖) / 2
  have ha : 0 < a := half_pos (sub_pos.mpr hw')
  let K (z : ℂ) (x : ℝ) := ((ζ x + z) / (ζ x - z)) * (g x : ℂ)
  let D (z : ℂ) (x : ℝ) := ((2 * ζ x) / (ζ x - z) ^ 2) * (g x : ℂ)
  have hZ {z : ℂ} (hz : z ∈ Metric.ball w a) : ‖z‖ < 1 - a := by
    have hDist := Metric.mem_ball.mp hz
    rw [dist_eq_norm] at hDist
    dsimp only [a] at *
    linarith only [hDist, norm_sub_norm_le z w]
  have hDen {z : ℂ} (hz : z ∈ Metric.ball w a) (x : ℝ) : a ≤ ‖ζ x - z‖ := by
    have h := norm_sub_norm_le (ζ x) z
    rw [hUnit x] at h
    linarith only [hZ hz, h]
  have hZ₀ {z : ℂ} (hz : z ∈ Metric.ball w a) : ‖z‖ < 1 :=
    (hZ hz).trans_le (sub_le_self _ ha.le)
  have hMeas (z : ℂ) : AEStronglyMeasurable (K z) volume :=
    ((hζ.add measurable_const).div (hζ.sub measurable_const)).aestronglyMeasurable.mul
      (hg.ofReal (𝕜 := ℂ)).aestronglyMeasurable
  have hDMeas (z : ℂ) : AEStronglyMeasurable (D z) volume :=
    ((measurable_const.mul hζ).div ((hζ.sub measurable_const).pow_const _)).aestronglyMeasurable.mul
      (hg.ofReal (𝕜 := ℂ)).aestronglyMeasurable
  have hDeriv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ)) (F := K) (F' := D)
    (Metric.ball_mem_nhds w ha)
    (Eventually.of_forall hMeas)
    (integrable_diskHerglotz_integrand hζ hUnit hg hw') (hDMeas w)
    (ae_of_all _ fun x z hz => by
      change ‖((2 * ζ x) / (ζ x - z) ^ 2) * (g x : ℂ)‖ ≤ (2 / a ^ 2) * ‖g x‖
      rw [norm_mul, norm_div, norm_mul, hUnit x, mul_one, norm_pow, Complex.norm_real]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
      exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos ha)
        (pow_le_pow_left₀ ha.le (hDen hz x) _))
    (hg.norm.const_mul (2 / a ^ 2))
    (ae_of_all _ fun x z hz => by
      have hNum := (hasDerivAt_id z).const_add (ζ x)
      have hDenom := (hasDerivAt_id z).const_sub (ζ x)
      have he : HasDerivAt (K · x)
          ((1 * (ζ x - z) - (ζ x + z) * (-1)) / (ζ x - z) ^ 2 * (g x : ℂ)) z := by
        simpa only [K, Pi.div_apply, id_eq] using
          (hNum.div hDenom (unit_sub_ne_zero (hUnit x) (hZ₀ hz))).mul_const (g x : ℂ)
      have hEq : ((1 * (ζ x - z) - (ζ x + z) * (-1)) / (ζ x - z) ^ 2 * (g x : ℂ)) =
          D z x := by
        change _ = (2 * ζ x / (ζ x - z) ^ 2) * (g x : ℂ)
        congr 1
        congr 1
        ring
      exact hEq ▸ he)).2
  have he : diskHerglotzIntegral ζ g = (fun z : ℂ => ∫ x : ℝ, K z x) := by
    funext z
    simp only [diskHerglotzIntegral, herglotzRieszKernel_zero, K]
  rw [he]
  exact hDeriv.differentiableAt.differentiableWithinAt

/-- The real part of the Herglotz integral integrates the real part of
its kernel against the same real density. -/
theorem re_diskHerglotzIntegral
    {ζ : ℝ → ℂ} (hζ : Measurable ζ) (hUnit : ∀ x, ‖ζ x‖ = 1)
    {g : ℝ → ℝ} (hg : Integrable g) {w : ℂ} (hw : ‖w‖ < 1) :
    (diskHerglotzIntegral ζ g w).re = ∫ x : ℝ, (herglotzRieszKernel 0 w (ζ x)).re * g x := by
  unfold diskHerglotzIntegral
  simp only [herglotzRieszKernel_zero]
  change Complex.reCLM (∫ x : ℝ, ((ζ x + w) / (ζ x - w)) * (g x : ℂ)) = _
  rw [← Complex.reCLM.integral_comp_comm (integrable_diskHerglotz_integrand hζ hUnit hg hw)]
  apply integral_congr_ae
  filter_upwards with x
  rw [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- Nonnegative data give a Herglotz integral with nonnegative real part. -/
theorem re_diskHerglotzIntegral_nonneg
    {ζ : ℝ → ℂ} (hζ : Measurable ζ) (hUnit : ∀ x, ‖ζ x‖ = 1)
    {g : ℝ → ℝ} (hg : Integrable g) (hPos : 0 ≤ᵐ[volume] g)
    {w : ℂ} (hw : ‖w‖ < 1) : 0 ≤ (diskHerglotzIntegral ζ g w).re := by
  rw [re_diskHerglotzIntegral hζ hUnit hg hw]
  apply integral_nonneg_of_ae
  filter_upwards [hPos] with x hx
  apply mul_nonneg _ hx
  have he := congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := 0) (w := w)) (ζ x)
  simp only [poissonKernel_def, Function.comp_apply, herglotzRieszKernel_zero,
    sub_zero, hUnit x, one_pow] at he
  rw [herglotzRieszKernel_zero, ← he]
  exact div_nonneg (sub_nonneg.mpr (by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) hw.le 2)) (sq_nonneg _)

/-- The center value of the Herglotz integral is the total mass. -/
theorem diskHerglotzIntegral_zero
    {ζ : ℝ → ℂ} (hUnit : ∀ x, ‖ζ x‖ = 1) (g : ℝ → ℝ) :
    diskHerglotzIntegral ζ g 0 = ((∫ x : ℝ, g x : ℝ) : ℂ) := by
  rw [diskHerglotzIntegral, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with x
  have hne : ζ x ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hUnit x]
    exact one_ne_zero
  simp [herglotzRieszKernel_zero, hne]

/-- The disk Herglotz integral is additive under subtraction of integrable
real data at every interior point. -/
theorem diskHerglotzIntegral_sub
    {ζ : ℝ → ℂ} (hζ : Measurable ζ) (hUnit : ∀ x, ‖ζ x‖ = 1)
    {g k : ℝ → ℝ} (hg : Integrable g) (hk : Integrable k)
    {w : ℂ} (hw : ‖w‖ < 1) :
    diskHerglotzIntegral ζ (fun x => g x - k x) w =
      diskHerglotzIntegral ζ g w - diskHerglotzIntegral ζ k w := by
  simp only [diskHerglotzIntegral, herglotzRieszKernel_zero, Complex.ofReal_sub, mul_sub]
  exact integral_sub (integrable_diskHerglotz_integrand hζ hUnit hg hw)
    (integrable_diskHerglotz_integrand hζ hUnit hk hw)

/-- The radial imaginary part of a Herglotz integral of signed real
data obeys a weak estimate with the L¹ norm of the data. -/
theorem diskAngleMeasure_lt_abs_im_diskHerglotzIntegral
    {ζ : ℝ → ℂ} (hζ : Measurable ζ) (hUnit : ∀ x, ‖ζ x‖ = 1)
    {g : ℝ → ℝ} (hg : Integrable g) {r L : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) (hL : 0 < L) :
    diskAngleMeasure {θ | L < |(diskHerglotzIntegral ζ g (circleMap 0 r θ)).im|} ≤
      ENNReal.ofReal (8 * Real.pi * ((∫ x : ℝ, ‖g x‖) / L)) := by
  let p (x : ℝ) := max (g x) 0
  let n (x : ℝ) := max (-g x) 0
  have hp : Integrable p := hg.pos_part
  have hn : Integrable n := hg.neg_part
  have hp₀ (x : ℝ) : 0 ≤ p x := le_max_right _ _
  have hn₀ (x : ℝ) : 0 ≤ n x := le_max_right _ _
  have hSub : (fun x => p x - n x) = g := by
    funext x
    dsimp only [p, n]
    rcases le_total 0 (g x) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_sub, neg_neg]
  have hNorm : ‖diskHerglotzIntegral ζ p 0‖ + ‖diskHerglotzIntegral ζ n 0‖ = ∫ x : ℝ, ‖g x‖ := by
    rw [diskHerglotzIntegral_zero hUnit, diskHerglotzIntegral_zero hUnit,
      Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (integral_nonneg hp₀), Real.norm_of_nonneg (integral_nonneg hn₀),
      ← integral_add hp hn]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [p, n]
    rcases le_total 0 (g x) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), add_zero, Real.norm_of_nonneg h]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_add, Real.norm_of_nonpos h]
  have hReal {k : ℝ → ℝ} (hk : Integrable k) (hk₀ : ∀ x, 0 ≤ k x)
      (w : ℂ) (hw : w ∈ Metric.ball 0 1) : 0 ≤ (diskHerglotzIntegral ζ k w).re :=
    re_diskHerglotzIntegral_nonneg hζ hUnit hk (ae_of_all _ hk₀)
      (by simpa only [Metric.mem_ball, dist_zero_right] using hw)
  have hMain := diskAngleMeasure_lt_abs_im_sub_superlevel_of_re_nonneg
    (differentiableOn_diskHerglotzIntegral hζ hUnit hp)
    (differentiableOn_diskHerglotzIntegral hζ hUnit hn)
    (hReal hp hp₀) (hReal hn hn₀) hr hr₁ hL
  rw [hNorm] at hMain
  convert hMain using 2
  ext θ
  have hw : ‖circleMap 0 r θ‖ < 1 := by rw [norm_circleMap_zero, abs_of_nonneg hr]; exact hr₁
  change L < |(diskHerglotzIntegral ζ g (circleMap 0 r θ)).im| ↔
    L < |(diskHerglotzIntegral ζ p (circleMap 0 r θ) -
      diskHerglotzIntegral ζ n (circleMap 0 r θ)).im|
  rw [← diskHerglotzIntegral_sub hζ hUnit hp hn hw, hSub]

private theorem measure_lt_abs_superlevel_le_of_ae_tendsto
    {ν : Measure ℝ} {v : ℝ → ℝ} {u : ℕ → ℝ → ℝ} {L : ℝ} {M : ℝ≥0∞}
    (hv : Measurable v) (hu : ∀ n, Measurable (u n))
    (hLim : ∀ᵐ θ ∂ν, Tendsto (fun n : ℕ => u n θ) atTop (𝓝 (v θ)))
    (hBound : ∀ n, ν {θ | L < |u n θ|} ≤ M) :
    ν {θ | L < |v θ|} ≤ M := by
  let E := {θ : ℝ | L < |v θ|}
  let Eₙ (n : ℕ) := {θ : ℝ | L < |u n θ|}
  let A := E.indicator (fun _ => (1 : ℝ≥0∞))
  let B (n : ℕ) := (Eₙ n).indicator (fun _ => (1 : ℝ≥0∞))
  have hE : MeasurableSet E := measurableSet_lt measurable_const (continuous_abs.measurable.comp hv)
  have hEₙ (n : ℕ) : MeasurableSet (Eₙ n) :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hu n))
  have hBM (n : ℕ) : Measurable (B n) := measurable_const.indicator (hEₙ n)
  have hPoint : ∀ᵐ θ ∂ν, A θ ≤ liminf (fun n : ℕ => B n θ) atTop := by
    filter_upwards [hLim] with θ hθ
    by_cases hθE : θ ∈ E
    · change L < |v θ| at hθE
      have hAbs : Tendsto (fun n : ℕ => |u n θ|) atTop (𝓝 |v θ|) :=
        (continuous_abs.continuousAt.tendsto.comp hθ)
      have hEvent : ∀ᶠ n : ℕ in atTop, θ ∈ Eₙ n := (tendsto_order.1 hAbs).1 L hθE
      dsimp only [A]
      rw [indicator_of_mem (show θ ∈ E from hθE)]
      refine le_liminf_of_le (by isBoundedDefault) ?_
      filter_upwards [hEvent] with n hn
      rw [show B n θ = 1 from indicator_of_mem hn _]
    · dsimp only [A]
      rw [indicator_of_notMem hθE]
      exact zero_le
  have hBnd : liminf (fun n : ℕ => ∫⁻ θ, B n θ ∂ν) atTop ≤ M := by
    refine liminf_le_of_le (by isBoundedDefault) ?_
    intro b hb
    obtain ⟨n, hn⟩ := hb.exists
    have hEeq : (∫⁻ θ, B n θ ∂ν) = ν (Eₙ n) := lintegral_indicator_one (hEₙ n)
    exact hn.trans (hEeq.le.trans (hBound n))
  calc
    _ = ∫⁻ θ, A θ ∂ν := (lintegral_indicator_one hE).symm
    _ ≤ ∫⁻ θ, liminf (fun n : ℕ => B n θ) atTop ∂ν := lintegral_mono_ae hPoint
    _ ≤ liminf (fun n : ℕ => ∫⁻ θ, B n θ ∂ν) atTop :=
      lintegral_liminf_le hBM
    _ ≤ _ := hBnd

/-- Whenever the radial imaginary part of a signed Herglotz integral
has a measurable boundary value, the same weak estimate holds there. -/
theorem diskAngleMeasure_lt_abs_diskHerglotz_boundary
    {ζ : ℝ → ℂ} (hζ : Measurable ζ) (hUnit : ∀ x, ‖ζ x‖ = 1)
    {g : ℝ → ℝ} (hg : Integrable g) {v : ℝ → ℝ} (hv : Measurable v)
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n) (hr₁ : ∀ n, r n < 1)
    (hLim : ∀ᵐ θ ∂diskAngleMeasure, Tendsto
      (fun n : ℕ => (diskHerglotzIntegral ζ g (circleMap 0 (r n) θ)).im) atTop (𝓝 (v θ)))
    {L : ℝ} (hL : 0 < L) :
    diskAngleMeasure {θ | L < |v θ|} ≤ ENNReal.ofReal (8 * Real.pi * ((∫ x : ℝ, ‖g x‖) / L)) := by
  refine measure_lt_abs_superlevel_le_of_ae_tendsto hv ?_ hLim
    (fun n => diskAngleMeasure_lt_abs_im_diskHerglotzIntegral hζ hUnit hg (hr n) (hr₁ n) hL)
  intro n
  have hSub (θ : ℝ) : circleMap 0 (r n) θ ∈ Metric.ball 0 1 := by
    rw [Metric.mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_nonneg (hr n)]
    exact hr₁ n
  have hc := (differentiableOn_diskHerglotzIntegral hζ hUnit hg).continuousOn
  exact (Complex.continuous_im.comp (hc.comp_continuous
    (continuous_circleMap 0 (r n)) hSub)).measurable

end
end MeyerGeneralProblem
