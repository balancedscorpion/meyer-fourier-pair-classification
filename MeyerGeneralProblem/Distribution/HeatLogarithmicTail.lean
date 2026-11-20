module

public import MeyerGeneralProblem.Distribution.BoundaryLogRadialLimit
public import MeyerGeneralProblem.Distribution.LaplaceSupportEdge
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

/-!
# Negative logarithmic tails of the Gaussian heat flow

At the common Fourier edge the normalized transform has a uniform
radial half-moment at large chart heights. Jensen's formula, the
subexponential center bound and the boundary Jacobian then control the
weighted negative logarithmic tails.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Set
open scoped FourierTransform Topology

private theorem stieltjesDensity_mul_pos (g : ℝ → ℂ) {y : ℝ} (hy : 0 < y) (z : ℂ) :
    stieltjesDensity g ((y : ℂ) * z) = stieltjesDensity (fun x => g (y * x)) z := by
  let K (x : ℝ) := ((y : ℂ) * z - x)⁻¹ * g x
  have hK := Measure.integral_comp_mul_left K y
  rw [abs_of_pos (inv_pos.mpr hy), Complex.real_smul, Complex.ofReal_inv] at hK
  apply mul_left_cancel₀ (inv_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'))
  calc
    _ = ∫ x : ℝ, K (y * x) := hK.symm
    _ = _ := by
      unfold stieltjesDensity
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [K]
      rw [Complex.ofReal_mul, ← mul_sub, mul_inv_rev, mul_assoc, mul_comm _ (g (y * x))]
      ring

/-- The edge-normalized heated transform is entire. -/
theorem differentiable_edgeNormalizedHeatFourierLaplace
    {f : ℝ → ℝ} (hf : Integrable f) {t : ℝ} (ht : 0 < t) (b : ℝ) :
    Differentiable ℂ (edgeNormalizedHeatFourierLaplace t f b) := by
  unfold edgeNormalizedHeatFourierLaplace
  exact (show Differentiable ℂ (fun z : ℂ => Complex.exp (-(↑(2 * Real.pi * b) * Complex.I) * z))
    by fun_prop).mul (differentiable_heatFourierLaplace hf ht b)

/-- After edge normalization the radial half-moment is bounded
independently of positive heat time and all chart heights at least one. -/
theorem circleAverage_sqrt_norm_edgeNormalizedHeatFourierLaplace_mul_le
    {f : ℝ → ℝ} (hf : Integrable f) {t : ℝ} (ht : 0 < t) (b : ℝ)
    {y r : ℝ} (hy : 1 ≤ y) (hr : 0 ≤ r) (hr₁ : r < 1) :
    Real.circleAverage (fun w => Real.sqrt ‖edgeNormalizedHeatFourierLaplace t f b
      ((y : ℂ) * cayleyToUpperHalfPlane w)‖) 0 r ≤
      4 * Real.sqrt 2 * Real.sqrt (1 + ∫ x : ℝ, ‖f x‖) := by
  have hy₀ : 0 < y := zero_lt_one.trans_le hy
  let h := realGaussianSmoothing t f
  let g (x : ℝ) := Complex.exp ((↑(-(2 * Real.pi * b) * x) : ℂ) * Complex.I) * (h x : ℂ)
  let gy (x : ℝ) := g (y * x)
  have hh : Integrable h := integrable_realGaussianSmoothing hf ht
  have hNorm (x : ℝ) : ‖g x‖ = ‖h x‖ := by
    dsimp only [g]
    simp [Complex.norm_exp, Complex.mul_re]
  have hg : Integrable g := hh.norm.mono'
    ((show Continuous (fun x : ℝ => Complex.exp ((↑(-(2 * Real.pi * b) * x) : ℂ) * Complex.I)) by
      fun_prop).aestronglyMeasurable.mul (hh.ofReal (𝕜 := ℂ)).aestronglyMeasurable)
    (ae_of_all _ fun x => (hNorm x).le)
  have hgy : Integrable gy := hg.comp_mul_left' hy₀.ne'
  have hMass : (∫ x : ℝ, ‖gy x‖) ≤ ∫ x : ℝ, ‖f x‖ := by
    change (∫ x : ℝ, ‖g (y * x)‖) ≤ ∫ x : ℝ, ‖f x‖
    rw [Measure.integral_comp_mul_left (fun x : ℝ => ‖g x‖),
      abs_of_pos (inv_pos.mpr hy₀), smul_eq_mul]
    calc
      _ ≤ ∫ x : ℝ, ‖g x‖ :=
        mul_le_of_le_one_left (integral_nonneg fun _ => norm_nonneg _) (inv_le_one_of_one_le₀ hy)
      _ = ∫ x : ℝ, ‖h x‖ := integral_congr_ae (ae_of_all _ hNorm)
      _ ≤ _ := integral_norm_realGaussianSmoothing_le hf ht
  have hSphere : Metric.sphere (0 : ℂ) |r| ⊆ Metric.ball 0 1 := by
    rw [abs_of_nonneg hr]
    exact Metric.sphere_subset_closedBall.trans (Metric.closedBall_subset_ball hr₁)
  have hC := ((differentiableOn_stieltjesDensity hgy).comp differentiableOn_cayleyToUpperHalfPlane
    (fun w hw => (im_cayleyToUpperHalfPlane_pos (by
      simpa only [Metric.mem_ball, dist_zero_right] using hw)).ne')).continuousOn
  have hH := (differentiable_edgeNormalizedHeatFourierLaplace hf ht b).continuous.comp_continuousOn
    ((continuousOn_const (c := (y : ℂ))).mul differentiableOn_cayleyToUpperHalfPlane.continuousOn)
  have hScale : ‖((↑(2 * Real.pi) : ℂ)⁻¹ * Complex.I)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, mul_one, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg Real.two_pi_pos.le]
    exact inv_le_one_of_one_le₀ (by nlinarith [Real.pi_gt_three])
  refine (Real.circleAverage_mono
    ((Real.continuous_sqrt.comp_continuousOn hH.norm).mono hSphere).circleIntegrable'
    ((Real.continuous_sqrt.comp_continuousOn hC.norm).mono hSphere).circleIntegrable'
    (fun w hw => ?_)).trans ?_
  · apply Real.sqrt_le_sqrt
    change ‖edgeNormalizedHeatFourierLaplace t f b ((y : ℂ) * cayleyToUpperHalfPlane w)‖ ≤
      ‖stieltjesDensity gy (cayleyToUpperHalfPlane w)‖
    have hHeight := im_cayleyToUpperHalfPlane_pos (by
      simpa only [Metric.mem_ball, dist_zero_right] using hSphere hw)
    have hHeight' : 0 < ((y : ℂ) * cayleyToUpperHalfPlane w).im := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      exact mul_pos hy₀ hHeight
    rw [edgeNormalizedHeatFourierLaplace_eq_stieltjesDensity hf ht b hHeight',
      norm_mul, stieltjesDensity_mul_pos _ hy₀]
    exact mul_le_of_le_one_left (norm_nonneg _) hScale
  · exact (circleAverage_sqrt_norm_stieltjesDensity_le hgy hr hr₁).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (add_le_add (le_refl _) hMass)) (by positivity))

/-- The negative logarithmic mass in the centered Cauchy weight is
tight in the small-time limit. The radius depends on the prescribed
error, while the estimate holds for every sufficiently small heat time. -/
theorem exists_eventually_weighted_neg_log_tail_lt_heatFourierLaplace
    {f : ℝ → ℝ} (hf : Integrable f) (hfCont : Continuous f) (hf₀ : f ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R > 0, ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      let V (x : ℝ) := Real.posLog ‖heatFourierLaplace t f 0 x‖⁻¹ / (1 + x ^ 2)
      Integrable V ∧ (∫ x in {x : ℝ | R ≤ |x|}, V x) < ε := by
  have hEmpty : EqOn (𝓕 (fun x : ℝ => (f x : ℂ))) 0 (Ioo (-(0 : ℝ)) 0) := by simp
  obtain ⟨b, hb, hZero, hEdge, _⟩ :=
    exists_common_positiveFourier_lower_edge hf hfCont hf₀ le_rfl hEmpty
  let M := 4 * Real.sqrt 2 * Real.sqrt (1 + ∫ x : ℝ, ‖f x‖)
  let η := ε / (4 * Real.pi)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨y, hy, hy₀, hCenter⟩ :=
    exists_large_height_eventually_edgeNormalizedHeatFourierLaplace_norm_gt_exp
      hf hb hEdge hη (max 1 (8 * Real.pi * M / ε))
  have hy₁ : 1 ≤ y := (le_max_left _ _).trans hy.le
  have hErr : (2 / y) * (Real.pi * (2 * M + η * y)) < ε := by
    have hSmall : 8 * Real.pi * M < y * ε :=
      (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hy)
    have hPart : 4 * Real.pi * M / y < ε / 2 := (div_lt_iff₀ hy₀).mpr (by
      nlinarith only [hSmall])
    have hEta : 2 * Real.pi * η = ε / 2 := by
      dsimp [η]
      field_simp [Real.pi_ne_zero]
      ring
    calc
      _ = 4 * Real.pi * M / y + 2 * Real.pi * η := by
        field_simp [hy₀.ne']
        ring
      _ < _ := by linarith only [hPart, hEta]
  refine ⟨y, hy₀, ?_⟩
  obtain ⟨C, hInt⟩ := exists_eventually_integrable_weighted_neg_log_heatFourierLaplace_centered
    hf hfCont hf₀
  have hT : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [hT, hCenter, hInt] with t ht htCenter htInt
  refine ⟨htInt.1, ?_⟩
  let H := edgeNormalizedHeatFourierLaplace t f b
  let A (z : ℂ) := H ((y : ℂ) * z)
  let F (w : ℂ) := A (cayleyToUpperHalfPlane w)
  let L (x : ℝ) := Real.posLog ‖heatFourierLaplace t f 0 x‖⁻¹
  let V (x : ℝ) := L x / (1 + x ^ 2)
  let W (u : ℝ) := L (y * u) / (1 + u ^ 2)
  let T := {x : ℝ | y ≤ |x|}
  have hTMeas : MeasurableSet T := measurableSet_le measurable_const continuous_abs.measurable
  have hCut : heatFourierLaplace t f 0 = heatFourierLaplace t f b :=
    heatFourierLaplace_eq_of_zero_Ioo hf ht hb hZero
  have hAD : Differentiable ℂ A :=
    (differentiable_edgeNormalizedHeatFourierLaplace hf ht b).comp (by fun_prop)
  have hFD : DifferentiableOn ℂ F (Metric.ball 0 1) :=
    hAD.comp_differentiableOn differentiableOn_cayleyToUpperHalfPlane
  have hAt : Real.exp (-η * y) ≤ ‖F 0‖ := by
    simpa [F, A, H, cayleyToUpperHalfPlane] using htCenter.le
  have hBound (r : ℝ) (hr : 0 < r) (hr₁ : r < 1) :
      Real.circleAverage (fun w => Real.posLog ‖F w‖⁻¹) 0 r ≤ 2 * M + η * y := by
    have he := circleAverage_neg_log_norm_le_of_circleAverage_sqrt_norm_le hFD
      (Real.exp_pos _) hAt hr hr₁
      (circleAverage_sqrt_norm_edgeNormalizedHeatFourierLaplace_mul_le hf ht b hy₁ hr.le hr₁)
    rw [Real.log_exp] at he
    linarith only [he]
  have hD : 0 ≤ 2 * M + η * y := by positivity
  have hW0 := integrable_weighted_neg_log_of_uniform_radial hAD 0 (by
    intro r hr hr₁
    simpa only [Complex.ofReal_zero, add_zero] using hBound r hr hr₁)
  have hW : Integrable W ∧ (∫ u : ℝ, W u) ≤ Real.pi * (2 * M + η * y) := by
    simpa only [W, L, A, H, Complex.ofReal_zero, add_zero, ← Complex.ofReal_mul,
      norm_edgeNormalizedHeatFourierLaplace_real, ← hCut, max_eq_left hD] using hW0
  let P (u : ℝ) := y * T.indicator V (y * u)
  have hP₀ (u : ℝ) : 0 ≤ P u := by
    apply mul_nonneg hy₀.le
    by_cases hu : y * u ∈ T
    · rw [indicator_of_mem hu]
      exact div_nonneg Real.posLog_nonneg (by positivity)
    · rw [indicator_of_notMem hu]
  have hP (u : ℝ) : P u ≤ (2 / y) * W u := by
    by_cases hu : y * u ∈ T
    · have ha : y ≤ |y * u| := hu
      rw [abs_mul, abs_of_pos hy₀] at ha
      have hu₀ : 1 ≤ |u| :=
        le_of_mul_le_mul_left (by simpa only [mul_one] using ha) hy₀
      have hu₂ : 1 ≤ u ^ 2 := by
        simpa only [one_pow, sq_abs] using (sq_le_sq₀ zero_le_one (abs_nonneg _)).mpr hu₀
      have hp : y ^ 2 * (1 + u ^ 2) ≤ 2 * (1 + (y * u) ^ 2) := by
        nlinarith only [mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hu₂)]
      have hFrac : y / (1 + (y * u) ^ 2) ≤ (2 / y) / (1 + u ^ 2) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hy₀).mpr
        nlinarith only [hp]
      dsimp only [P]
      rw [indicator_of_mem hu]
      dsimp only [V, W]
      calc
        _ = L (y * u) * (y / (1 + (y * u) ^ 2)) := by ring
        _ ≤ L (y * u) * ((2 / y) / (1 + u ^ 2)) :=
          mul_le_mul_of_nonneg_left hFrac Real.posLog_nonneg
        _ = _ := by ring
    · dsimp only [P]
      rw [indicator_of_notMem hu, mul_zero]
      exact mul_nonneg (by positivity) (div_nonneg Real.posLog_nonneg (by positivity))
  have hChange : (∫ u : ℝ, P u) = ∫ x in T, V x := by
    dsimp only [P]
    rw [integral_const_mul, Measure.integral_comp_mul_left (T.indicator V) y,
      abs_of_pos (inv_pos.mpr hy₀), smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hy₀.ne', one_mul, integral_indicator hTMeas]
  change (∫ x in T, V x) < ε
  rw [← hChange]
  calc
    _ ≤ ∫ u : ℝ, (2 / y) * W u :=
      integral_mono_of_nonneg (ae_of_all _ hP₀) (hW.1.const_mul _) (ae_of_all _ hP)
    _ ≤ (2 / y) * (Real.pi * (2 * M + η * y)) := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hW.2 (by positivity)
    _ < _ := hErr

private theorem abs_log_eq_log_max_one_add_posLog_inv {v : ℝ} (hv : 0 ≤ v) :
    |Real.log v| = Real.log (max 1 v) + Real.posLog v⁻¹ := by
  rw [← Real.posLog_eq_log_max_one hv, Real.posLog_apply, Real.posLog_apply, Real.log_inv]
  by_cases h : 0 ≤ Real.log v
  · rw [abs_of_nonneg h, max_eq_right h, max_eq_left (neg_nonpos.mpr h), add_zero]
  · have h' := (lt_of_not_ge h).le
    rw [abs_of_nonpos h', max_eq_left h', max_eq_right (neg_nonneg.mpr h'), zero_add]

/-- The absolute logarithm of the heated positive-frequency transform
has a weighted real-line tail that is uniformly small as heat time
tends to zero. -/
theorem exists_eventually_weighted_abs_log_tail_lt_heatFourierLaplace
    {f : ℝ → ℝ} (hf : Integrable f) (hfCont : Continuous f) (hf₀ : f ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R > 0, ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      let V (x : ℝ) := |Real.log ‖heatFourierLaplace t f 0 x‖| / (1 + x ^ 2)
      Integrable V ∧ (∫ x in {x : ℝ | R ≤ |x|}, V x) < ε := by
  obtain ⟨N, hN, hPos⟩ := exists_uniform_weighted_log_pos_tail_heatFourierLaplace hf (half_pos hε)
  obtain ⟨R, hR, hNeg⟩ := exists_eventually_weighted_neg_log_tail_lt_heatFourierLaplace
    hf hfCont hf₀ (half_pos hε)
  let S := max (N : ℝ) R
  refine ⟨S, hR.trans_le (le_max_right _ _), ?_⟩
  have hT : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [hT, hNeg] with t ht hV
  obtain ⟨hVInt, hVTail⟩ := hV
  obtain ⟨hUInt, hUTail⟩ := hPos t ht
  let U (x : ℝ) := Real.log (max 1 ‖heatFourierLaplace t f 0 x‖) / (1 + x ^ 2)
  let V (x : ℝ) := Real.posLog ‖heatFourierLaplace t f 0 x‖⁻¹ / (1 + x ^ 2)
  let T := {x : ℝ | S ≤ |x|}
  have hU₀ : ∀ x, 0 ≤ U x := fun _ =>
    div_nonneg (Real.log_nonneg (le_max_left _ _)) (by positivity)
  have hV₀ : ∀ x, 0 ≤ V x := fun _ =>
    div_nonneg Real.posLog_nonneg (by positivity)
  have hEq (x : ℝ) : |Real.log ‖heatFourierLaplace t f 0 x‖| / (1 + x ^ 2) = U x + V x := by
    dsimp only [U, V]
    rw [← add_div, abs_log_eq_log_max_one_add_posLog_inv (norm_nonneg _)]
  have hUDom : (∫ x in T, U x) ≤ ∫ x in {x : ℝ | (N : ℝ) ≤ |x|}, U x :=
    setIntegral_mono_set hUInt.integrableOn (ae_of_all _ hU₀)
      (ae_of_all _ fun _ hx => (le_max_left _ _).trans hx)
  have hVDom : (∫ x in T, V x) ≤ ∫ x in {x : ℝ | R ≤ |x|}, V x :=
    setIntegral_mono_set hVInt.integrableOn (ae_of_all _ hV₀)
      (ae_of_all _ fun _ hx => (le_max_right _ _).trans hx)
  refine ⟨?_, ?_⟩
  · rw [funext hEq]
    exact (show Integrable U from hUInt).add (show Integrable V from hVInt)
  change (∫ x in T, |Real.log ‖heatFourierLaplace t f 0 x‖| / (1 + x ^ 2)) < ε
  simp_rw [hEq]
  rw [integral_add hUInt.integrableOn hVInt.integrableOn]
  linarith only [hUDom, hVDom, hUTail, hVTail]

/-- The total weighted absolute logarithm is bounded uniformly for all
sufficiently small positive heat times. -/
theorem exists_eventually_integral_weighted_abs_log_heatFourierLaplace_le
    {f : ℝ → ℝ} (hf : Integrable f) (hfCont : Continuous f) (hf₀ : f ≠ 0) :
    ∃ C : ℝ, ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      let V (x : ℝ) := |Real.log ‖heatFourierLaplace t f 0 x‖| / (1 + x ^ 2)
      Integrable V ∧ (∫ x : ℝ, V x) ≤ C := by
  let M := Real.pi * (2 * Real.sqrt 2 * Real.sqrt (1 + ∫ x : ℝ, ‖f x‖))
  obtain ⟨C, hNeg⟩ := exists_eventually_integrable_weighted_neg_log_heatFourierLaplace_centered
    hf hfCont hf₀
  obtain ⟨_, _, hPos⟩ := exists_uniform_weighted_log_pos_tail_heatFourierLaplace hf zero_lt_one
  refine ⟨2 * M + C, ?_⟩
  have hT : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [hT, hNeg] with t ht hV
  obtain ⟨hVInt, hVBound⟩ := hV
  obtain ⟨hUInt, _⟩ := hPos t ht
  obtain ⟨hWInt, hWBound⟩ := integrable_sqrt_norm_heatFourierLaplace_weighted hf ht
  let U (x : ℝ) := Real.log (max 1 ‖heatFourierLaplace t f 0 x‖) / (1 + x ^ 2)
  let V (x : ℝ) := Real.posLog ‖heatFourierLaplace t f 0 x‖⁻¹ / (1 + x ^ 2)
  let W (x : ℝ) := Real.sqrt ‖heatFourierLaplace t f 0 x‖ / (1 + x ^ 2)
  have hEq : (fun x : ℝ => |Real.log ‖heatFourierLaplace t f 0 x‖| / (1 + x ^ 2)) =
      fun x => U x + V x := by
    funext x
    dsimp only [U, V]
    rw [← add_div, abs_log_eq_log_max_one_add_posLog_inv (norm_nonneg _)]
  have hP (x : ℝ) : U x ≤ 2 * W x := by
    have he : Real.log (max 1 ‖heatFourierLaplace t f 0 x‖) ≤
        2 * Real.sqrt ‖heatFourierLaplace t f 0 x‖ := by
      rw [← Real.posLog_eq_log_max_one (norm_nonneg _), Real.posLog_apply]
      apply max_le (by positivity)
      have h := Real.log_le_rpow_div (norm_nonneg (heatFourierLaplace t f 0 x))
        (by norm_num : (0 : ℝ) < 1 / 2)
      rw [← Real.sqrt_eq_rpow] at h
      linarith only [h]
    dsimp only [U, W]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right he (by positivity)
  have hU : (∫ x : ℝ, U x) ≤ 2 * M := by
    calc
      _ ≤ ∫ x : ℝ, 2 * W x := integral_mono hUInt (hWInt.const_mul _) hP
      _ ≤ _ := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left hWBound (by norm_num)
  rw [hEq]
  refine ⟨(show Integrable U from hUInt).add (show Integrable V from hVInt), ?_⟩
  rw [integral_add hUInt hVInt]
  exact add_le_add hU hVBound

/-- One common cutoff gives small weighted tails and their measurable
conjugate radial limits for all sufficiently small positive heat times. -/
theorem exists_eventually_angular_heat_log_tail_radial_limit
    {f : ℝ → ℝ} (hf : Integrable f) (hfCont : Continuous f) (hf₀ : f ≠ 0)
    {ε : ℝ} (hε : 0 < ε) (ρ : ℕ → ℝ) (hρ₁ : ∀ n, ρ n < 1)
    (hρ : Tendsto ρ atTop (𝓝 1)) :
    ∃ R > 0, ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      let u := {x : ℝ | R ≤ |x|}.indicator
        (fun x => Real.log ‖heatFourierLaplace t f 0 (x : ℂ)‖)
      Integrable (fun x : ℝ => u x / (1 + x ^ 2)) ∧
      (∫ x : ℝ, ‖u x / (1 + x ^ 2)‖) < ε ∧
      ∃ v : ℝ → ℝ, Measurable v ∧
        (∀ x, v (cayleyBoundaryAngle x) = weightedDiskHerglotzBoundaryConjugate u x) ∧
        ∀ᵐ θ ∂diskAngleMeasure, Tendsto
          (fun n : ℕ => (weightedDiskHerglotzIntegral u (circleMap 0 (ρ n) θ)).im)
          atTop (𝓝 (v θ)) := by
  obtain ⟨R, hR, hTail⟩ := exists_eventually_weighted_abs_log_tail_lt_heatFourierLaplace
    hf hfCont hf₀ hε
  obtain ⟨x, d, hd, hCenter⟩ := exists_eventually_norm_heatFourierLaplace_lower_bound
    hf hfCont hf₀ (s := 0) le_rfl (by simp) (y := 1) zero_lt_one
  refine ⟨R, hR, ?_⟩
  have hPos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [hTail, hCenter, hPos] with t hTail' hCenter' ht
  have hNonzero : ∃ z : ℂ, heatFourierLaplace t f 0 z ≠ 0 :=
    ⟨(x : ℂ) + (1 : ℂ) * Complex.I, norm_pos_iff.mp (hd.trans_le hCenter')⟩
  obtain ⟨hInt, hMass, hLim⟩ := exists_angular_weightedDiskHerglotz_log_tail_radial_limit
    (differentiable_heatFourierLaplace hf ht 0) hNonzero hTail'.1 R ρ hρ₁ hρ
  exact ⟨hInt, hMass.trans_lt hTail'.2, hLim⟩

end
end MeyerGeneralProblem
