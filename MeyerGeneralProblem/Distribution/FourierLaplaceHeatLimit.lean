module

public import MeyerGeneralProblem.Distribution.CauchyDensityBoundary
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Removing Gaussian smoothing in the upper half-plane

The positive-frequency Laplace integral of an integrable density exists
at strictly positive height. Multiplication by the Gaussian Fourier
multiplier tends to the identity uniformly over every closed half-plane
separated from the real line.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory MeromorphicOn Set
open scoped ComplexConjugate FourierTransform Topology

/-- The original positive-frequency transform, with an optional higher
frequency cutoff. -/
def fourierLaplaceRealDensity (f : ℝ → ℝ) (s : ℝ) (z : ℂ) : ℂ :=
  ∫ ξ in Ioi s, (𝓕 (fun x : ℝ => (f x : ℂ))) ξ *
    Complex.exp ((↑(2 * Real.pi * ξ) * Complex.I) * z)

/-- The ordinary Fourier transform of an integrable real density is continuous. -/
theorem continuous_fourier_ofReal {f : ℝ → ℝ} (hf : Integrable f) :
    Continuous (𝓕 (fun x : ℝ => (f x : ℂ))) := by
  have hInner : Continuous fun p : ℝ × ℝ => inner ℝ p.1 p.2 :=
    (innerSL ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).continuous₂
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar hInner hf.ofReal

private theorem norm_fourierLaplace_exponential (ξ : ℝ) (z : ℂ) :
    ‖Complex.exp ((↑(2 * Real.pi * ξ) * Complex.I) * z)‖ =
      Real.exp (-(2 * Real.pi * z.im) * ξ) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

private theorem exp_fourierLaplace_height_le {b ξ : ℝ} {z : ℂ}
    (hbz : b ≤ z.im) (hξ : 0 ≤ ξ) :
    Real.exp (-(2 * Real.pi * z.im) * ξ) ≤ Real.exp (-(2 * Real.pi * b) * ξ) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbz
    Real.two_pi_pos.le) hξ
  linarith only [h]

private theorem damping_nonneg_le_one {t : ℝ} (ht : 0 ≤ t) (ξ : ℝ) :
    Real.exp (-(Real.pi ^ 2 * t) * ξ ^ 2) ≤ 1 :=
  Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (mul_nonneg (sq_nonneg _) ht)) (sq_nonneg ξ))

private theorem integrableOn_damped_fourierLaplace_integrand
    {f : ℝ → ℝ} (hf : Integrable f) {s : ℝ} (hs : 0 ≤ s)
    {b : ℝ} (hb : 0 < b) {z : ℂ} (hbz : b ≤ z.im)
    (a : ℝ → ℝ) (ha : Continuous a) (haNorm : ∀ ξ, ‖a ξ‖ ≤ 1) :
    IntegrableOn (fun ξ : ℝ => (𝓕 (fun x : ℝ => (f x : ℂ))) ξ * (a ξ : ℂ) *
      Complex.exp ((↑(2 * Real.pi * ξ) * Complex.I) * z)) (Ioi s) := by
  let M := ∫ x : ℝ, ‖f x‖
  have hB : IntegrableOn (fun ξ : ℝ => M * Real.exp (-(2 * Real.pi * b) * ξ)) (Ioi s) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos (mul_pos Real.two_pi_pos hb)) s).const_mul M
  have hCont : Continuous (fun ξ : ℝ => (𝓕 (fun x : ℝ => (f x : ℂ))) ξ * (a ξ : ℂ) *
      Complex.exp ((↑(2 * Real.pi * ξ) * Complex.I) * z)) :=
    ((continuous_fourier_ofReal hf).mul (Complex.continuous_ofReal.comp ha)).mul (by fun_prop)
  refine hB.mono' hCont.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
  rw [norm_mul, norm_mul, Complex.norm_real, norm_fourierLaplace_exponential]
  exact mul_le_mul
    ((mul_le_of_le_one_right (norm_nonneg _) (haNorm ξ)).trans
      (norm_fourier_ofReal_le_integral_norm f ξ))
    (exp_fourierLaplace_height_le hbz (hs.trans (mem_Ioi.mp hξ).le))
    (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)

/-- The heat flow's analytic positive-frequency parts converge to the
original transform uniformly wherever the imaginary height is at least
a fixed positive number. -/
theorem tendstoUniformlyOn_heatFourierLaplace_at_zero
    {f : ℝ → ℝ} (hf : Integrable f) {s b : ℝ} (hs : 0 ≤ s) (hb : 0 < b) :
    TendstoUniformlyOn (fun t : ℝ => heatFourierLaplace t f s)
      (fourierLaplaceRealDensity f s) (𝓝[>] (0 : ℝ)) {z : ℂ | b ≤ z.im} := by
  let M := ∫ x : ℝ, ‖f x‖
  let B (ξ : ℝ) := Real.exp (-(2 * Real.pi * b) * ξ)
  let A (t ξ : ℝ) := Real.exp (-(Real.pi ^ 2 * t) * ξ ^ 2)
  let D (t ξ : ℝ) := M * (1 - A t ξ) * B ξ
  let ν := volume.restrict (Ioi s)
  have hM : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
  have hB : Integrable B ν :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos (mul_pos Real.two_pi_pos hb)) s
  have hDCont (t : ℝ) : Continuous (D t) := by unfold D A B; fun_prop
  have hDNonneg {t : ℝ} (ht : 0 ≤ t) (ξ : ℝ) : 0 ≤ D t ξ :=
    mul_nonneg (mul_nonneg hM (sub_nonneg.mpr (damping_nonneg_le_one ht ξ)))
      (Real.exp_pos _).le
  have hDLe {t : ℝ} (ht : 0 ≤ t) (ξ : ℝ) : ‖D t ξ‖ ≤ M * B ξ := by
    rw [Real.norm_of_nonneg (hDNonneg ht ξ)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right hM (sub_le_self _ (Real.exp_pos _).le)) (Real.exp_pos _).le
  have hT : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hLim : Tendsto (fun t : ℝ => ∫ ξ, D t ξ ∂ν) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    suffices Tendsto (fun t : ℝ => ∫ ξ, D t ξ ∂ν) (𝓝[>] (0 : ℝ))
        (𝓝 (∫ _ : ℝ, (0 : ℝ) ∂ν)) by simpa only [integral_zero] using this
    refine tendsto_integral_filter_of_dominated_convergence (fun ξ => M * B ξ)
      (Eventually.of_forall fun t => (hDCont t).aestronglyMeasurable)
      (hT.mono fun t ht => ae_of_all _ (hDLe ht.le))
      (hB.const_mul M) (ae_of_all _ fun ξ => ?_)
    have hc : Continuous (fun t : ℝ => D t ξ) := by unfold D A; fun_prop
    have hzero : D 0 ξ = 0 := by simp [D, A]
    have hC : Tendsto (fun t : ℝ => D t ξ) (𝓝[>] (0 : ℝ)) (𝓝 (D 0 ξ)) :=
      hc.continuousAt.continuousWithinAt
    simpa only [hzero] using hC
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hT, (tendsto_order.1 hLim).2 ε hε] with t ht hSmall
  intro z hz
  have hbz : b ≤ z.im := hz
  let K (ξ : ℝ) := (𝓕 (fun x : ℝ => (f x : ℂ))) ξ
  let E (ξ : ℝ) := Complex.exp ((↑(2 * Real.pi * ξ) * Complex.I) * z)
  have hKin : Integrable (fun ξ => K ξ * E ξ) ν := by
    simpa only [K, E, Complex.ofReal_one, mul_one, IntegrableOn, ν] using
      integrableOn_damped_fourierLaplace_integrand hf hs hb hbz (fun _ => 1)
        continuous_const (by simp)
  have hKout : Integrable (fun ξ => K ξ * (A t ξ : ℂ) * E ξ) ν :=
    integrableOn_damped_fourierLaplace_integrand hf hs hb hbz (A t)
      (by unfold A; fun_prop) (fun ξ => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]
        exact damping_nonneg_le_one ht.le ξ)
  have hHeat : heatFourierLaplace t f s z = ∫ ξ, K ξ * (A t ξ : ℂ) * E ξ ∂ν := by
    unfold heatFourierLaplace
    exact integral_congr_ae (ae_of_all _ fun ξ => by
      dsimp [K, A, E]; rw [fourier_realGaussianSmoothing hf ht])
  have hDom : Integrable (D t) ν := (hB.const_mul M).mono'
    (hDCont t).aestronglyMeasurable (ae_of_all _ (hDLe ht.le))
  rw [dist_eq_norm, hHeat, fourierLaplaceRealDensity, ← integral_sub hKin hKout]
  refine ((norm_integral_le_integral_norm _).trans ?_).trans_lt hSmall
  apply integral_mono_ae (hKin.sub hKout).norm hDom
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
  have hFreq : 0 ≤ ξ := hs.trans (mem_Ioi.mp hξ).le
  change ‖K ξ * E ξ - K ξ * (A t ξ : ℂ) * E ξ‖ ≤ D t ξ
  have hAlg : K ξ * E ξ - K ξ * (A t ξ : ℂ) * E ξ =
      K ξ * ((1 - A t ξ : ℝ) : ℂ) * E ξ := by
    push_cast
    ring
  rw [hAlg, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (sub_nonneg.mpr (damping_nonneg_le_one ht.le ξ))]
  dsimp only [D, B, E]
  rw [norm_fourierLaplace_exponential]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right (norm_fourier_ofReal_le_integral_norm f ξ)
      (sub_nonneg.mpr (damping_nonneg_le_one ht.le ξ)))
    (exp_fourierLaplace_height_le hbz hFreq) (Real.exp_pos _).le
    (mul_nonneg hM (sub_nonneg.mpr (damping_nonneg_le_one ht.le ξ)))

/-- On every horizontal line above the real axis, the original
positive-frequency transform of a nonzero real density with a centered
gap is nonzero at some point. -/
theorem exists_fourierLaplaceRealDensity_horizontal_ne_zero
    {f : ℝ → ℝ} (hf : Integrable f) (hfCont : Continuous f) (hf₀ : f ≠ 0)
    {s : ℝ} (hGap : EqOn (𝓕 (fun x : ℝ => (f x : ℂ))) 0 (Ioo (-s) s))
    {y : ℝ} (hy : 0 < y) :
    ∃ x : ℝ, fourierLaplaceRealDensity f s ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
  by_contra! hLine
  let F : ℝ → ℂ := 𝓕 (fun x : ℝ => (f x : ℂ))
  let D (ξ : ℝ) : ℂ := F ξ * (Real.exp (-(2 * Real.pi * y) * ξ) : ℂ)
  let P := (Ioi s).indicator D
  have hDCont : Continuous D := (continuous_fourier_ofReal hf).mul (by fun_prop)
  have hDInt : IntegrableOn D (Ioi s) := by
    refine ((integrableOn_exp_mul_Ioi (neg_neg_of_pos (mul_pos Real.two_pi_pos hy)) s).const_mul
      (∫ x : ℝ, ‖f x‖)).mono' hDCont.aestronglyMeasurable ?_
    filter_upwards with ξ
    change ‖F ξ * (Real.exp (-(2 * Real.pi * y) * ξ) : ℂ)‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_right (norm_fourier_ofReal_le_integral_norm f ξ) (Real.exp_pos _).le
  have hPInt : Integrable P := hDInt.integrable_indicator measurableSet_Ioi
  have hInv : 𝓕⁻ P = 0 := by
    funext x
    change 𝓕⁻ P x = 0
    rw [Real.fourierInv_eq']
    calc
      _ = ∫ ξ in Ioi s, Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I) • D ξ := by
        rw [← integral_indicator measurableSet_Ioi]
        apply integral_congr_ae
        filter_upwards with ξ
        by_cases hξ : ξ ∈ Ioi s
        · simp only [P, indicator_of_mem hξ]
        · simp only [P, indicator_of_notMem hξ, smul_zero]
      _ = fourierLaplaceRealDensity f s ((x : ℂ) + (y : ℂ) * Complex.I) := by
        unfold fourierLaplaceRealDensity
        apply integral_congr_ae
        filter_upwards with ξ
        simp only [D, smul_eq_mul, Complex.ofReal_exp, Real.inner_apply]
        rw [mul_left_comm, mul_assoc, ← Complex.exp_add]
        congr 2
        push_cast
        linear_combination -(2 * (Real.pi : ℂ) * ξ * y) * Complex.I_sq
      _ = 0 := hLine x
  have hForward : 𝓕 P = 0 := by
    funext ξ
    have he := congrFun hInv (-ξ)
    rw [Real.fourierInv_eq_fourier_neg, neg_neg] at he
    exact he
  have hInvZero : 𝓕⁻ (0 : ℝ → ℂ) = 0 := by
    funext ξ
    simp only [Real.fourierInv_eq, Pi.zero_apply, smul_zero, integral_zero]
  have hFOpen : EqOn F 0 (Ioi s) := by
    intro ξ hξ
    have hC : ContinuousAt P ξ := hDCont.continuousAt.congr (by
      filter_upwards [Ioi_mem_nhds hξ] with u hu
      simp only [P, indicator_of_mem hu])
    have hForwardInt : Integrable (𝓕 P) := hForward ▸ integrable_zero ℝ ℂ volume
    have hz := hPInt.fourierInv_fourier_eq hForwardInt hC
    rw [hForward, hInvZero] at hz
    have hD : F ξ * (Real.exp (-(2 * Real.pi * y) * ξ) : ℂ) = 0 := by
      simpa only [P, indicator_of_mem hξ, Pi.zero_apply] using hz.symm
    exact (mul_eq_zero.mp hD).resolve_right (by exact_mod_cast Real.exp_ne_zero _)
  have hFUpper : EqOn F 0 (Ici s) := by
    simpa only [closure_Ioi] using hFOpen.closure (continuous_fourier_ofReal hf) continuous_const
  have hFZero : F = 0 := by
    funext ξ
    by_cases hUpper : s ≤ ξ
    · exact hFUpper hUpper
    by_cases hLower : ξ ≤ -s
    · have hFlip : F ξ = conj (F (-ξ)) := by
        simpa only [F, neg_neg] using fourier_ofReal_neg_eq_conj f (-ξ)
      have hReflect : s ≤ -ξ := by simpa only [neg_neg] using neg_le_neg hLower
      rw [hFlip, show F (-ξ) = 0 from hFUpper hReflect, map_zero]
      rfl
    · exact hGap ⟨lt_of_not_ge hLower, lt_of_not_ge hUpper⟩
  have hInvInt : Integrable F := hFZero ▸ integrable_zero ℝ ℂ volume
  have hfInv := (Complex.continuous_ofReal.comp hfCont).fourierInv_fourier_eq hf.ofReal hInvInt
  change 𝓕⁻ F = (fun x : ℝ => (f x : ℂ)) at hfInv
  rw [hFZero, hInvZero] at hfInv
  apply hf₀
  funext x
  exact Complex.ofReal_eq_zero.mp (congrFun hfInv x).symm

/-- A fixed point on any chosen positive horizontal line gives a positive
lower bound for the heated transform for all sufficiently small heat
times. -/
theorem exists_eventually_norm_heatFourierLaplace_lower_bound
    {f : ℝ → ℝ} (hf : Integrable f) (hfCont : Continuous f) (hf₀ : f ≠ 0)
    {s : ℝ} (hs : 0 ≤ s)
    (hGap : EqOn (𝓕 (fun x : ℝ => (f x : ℂ))) 0 (Ioo (-s) s))
    {y : ℝ} (hy : 0 < y) :
    ∃ x : ℝ, ∃ δ > 0, ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      δ ≤ ‖heatFourierLaplace t f s ((x : ℂ) + (y : ℂ) * Complex.I)‖ := by
  obtain ⟨x, hx⟩ := exists_fourierLaplaceRealDensity_horizontal_ne_zero hf hfCont hf₀ hGap hy
  let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  let δ := ‖fourierLaplaceRealDensity f s z‖ / 2
  have hδ : 0 < δ := half_pos (norm_pos_iff.mpr hx)
  refine ⟨x, δ, hδ, ?_⟩
  have hUnif := Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_heatFourierLaplace_at_zero hf hs hy) δ hδ
  filter_upwards [hUnif] with t hT
  have hMem : z ∈ {w : ℂ | y ≤ w.im} := by
    simp [z, Complex.add_im, Complex.mul_im]
  have he := hT z hMem
  rw [dist_eq_norm] at he
  have hTriangle : ‖fourierLaplaceRealDensity f s z‖ ≤
      ‖fourierLaplaceRealDensity f s z - heatFourierLaplace t f s z‖ +
        ‖heatFourierLaplace t f s z‖ := by
    simpa only [sub_add_cancel] using norm_add_le
      (fourierLaplaceRealDensity f s z - heatFourierLaplace t f s z)
      (heatFourierLaplace t f s z)
  change δ ≤ ‖heatFourierLaplace t f s z‖
  dsimp only [δ] at *
  linarith only [he, hTriangle]

private theorem log_norm_le_circleAverage_log_norm {F : ℂ → ℂ} {r : ℝ}
    (hr : 0 < r) (hF : AnalyticOnNhd ℂ F (Metric.closedBall 0 |r|)) (hF₀ : F 0 ≠ 0) :
    Real.log ‖F 0‖ ≤ Real.circleAverage (fun w => Real.log ‖F w‖) 0 r := by
  rw [hF.circleAverage_log_norm hr.ne' hF₀]
  apply le_add_of_nonneg_left
  apply finsum_nonneg
  intro w
  by_cases hw : w ∈ Metric.closedBall (0 : ℂ) |r|
  · by_cases h₀ : w = 0
    · subst w
      rw [AnalyticOnNhd.divisor_apply hF hw, (hF 0 hw).analyticOrderAt_eq_zero.mpr hF₀]
      simp
    · have hNorm : 0 < ‖w‖ := norm_pos_iff.mpr h₀
      have hNormLe : ‖w‖ ≤ r := by
        simpa only [Metric.mem_closedBall, dist_zero_right, abs_of_pos hr] using hw
      have hLog : 0 ≤ Real.log (r * ‖(0 : ℂ) - w‖⁻¹) := by
        apply Real.log_nonneg
        simp only [zero_sub, norm_neg, ← div_eq_mul_inv]
        exact (one_le_div hNorm).mpr hNormLe
      exact mul_nonneg (by exact_mod_cast hF.divisor_nonneg w) hLog
  · simp only [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem (divisor F _) hw, Int.cast_zero,
      zero_mul, le_rfl]

/-- Jensen's formula bounds the radial negative logarithmic moment by
the radial half-moment and a lower bound at the center. -/
theorem circleAverage_neg_log_norm_le_of_circleAverage_sqrt_norm_le
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    {δ M r : ℝ} (hδ : 0 < δ) (hCenter : δ ≤ ‖F 0‖)
    (hr : 0 < r) (hr₁ : r < 1)
    (hHalf : Real.circleAverage (fun w => Real.sqrt ‖F w‖) 0 r ≤ M) :
    Real.circleAverage (fun w => Real.posLog ‖F w‖⁻¹) 0 r ≤ 2 * M - Real.log δ := by
  have hClosed : Metric.closedBall (0 : ℂ) |r| ⊆ Metric.ball 0 1 := by
    rw [abs_of_pos hr]
    exact Metric.closedBall_subset_ball hr₁
  have hSphere : Metric.sphere (0 : ℂ) |r| ⊆ Metric.ball 0 1 :=
    Metric.sphere_subset_closedBall.trans hClosed
  have hA := (hF.analyticOnNhd Metric.isOpen_ball).mono hClosed
  have hM : MeromorphicOn F (Metric.sphere 0 |r|) :=
    (hA.mono Metric.sphere_subset_closedBall).meromorphicOn
  have hPosI : CircleIntegrable (fun w => Real.posLog ‖F w‖) 0 r :=
    hM.circleIntegrable_posLog_norm
  have hNegI : CircleIntegrable (fun w => Real.posLog ‖F w‖⁻¹) 0 r := by
    simpa only [Pi.inv_apply, norm_inv] using hM.inv.circleIntegrable_posLog_norm
  have hSqrtI : CircleIntegrable (fun w => 2 * Real.sqrt ‖F w‖) 0 r :=
    (continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn
      (hF.continuousOn.mono hSphere).norm)).circleIntegrable'
  have hPosAvg : Real.circleAverage (fun w => Real.posLog ‖F w‖) 0 r ≤ 2 * M := by
    calc
      _ ≤ Real.circleAverage (fun w => 2 * Real.sqrt ‖F w‖) 0 r := by
        refine Real.circleAverage_mono hPosI hSqrtI fun w _ => ?_
        rw [Real.posLog]
        apply max_le (by positivity)
        have h := Real.log_le_rpow_div (norm_nonneg (F w)) (by norm_num : (0 : ℝ) < 1 / 2)
        rw [← Real.sqrt_eq_rpow] at h
        linarith only [h]
      _ = 2 * Real.circleAverage (fun w => Real.sqrt ‖F w‖) 0 r := by
        change Real.circleAverage (fun w => (2 : ℝ) • Real.sqrt ‖F w‖) 0 r = _
        rw [Real.circleAverage_fun_smul, smul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hHalf (by norm_num)
  have hAvgDiff :
      Real.circleAverage (fun w => Real.posLog ‖F w‖) 0 r -
        Real.circleAverage (fun w => Real.posLog ‖F w‖⁻¹) 0 r =
      Real.circleAverage (fun w => Real.log ‖F w‖) 0 r := by
    rw [← Real.circleAverage_fun_sub hPosI hNegI]
    simp only [Real.posLog_sub_posLog_inv]
  have hJ := log_norm_le_circleAverage_log_norm hr hA (norm_pos_iff.mp (hδ.trans_le hCenter))
  have hLog : Real.log δ ≤ Real.log ‖F 0‖ := Real.log_le_log hδ hCenter
  linarith only [hJ, hLog, hAvgDiff, hPosAvg]

/-- A single translated disk chart bounds the radial negative-logarithm
averages at every radius for all sufficiently small positive heat times. -/
theorem exists_eventually_circleAverage_neg_log_heatFourierLaplace_le
    {f : ℝ → ℝ} (hf : Integrable f) (hfCont : Continuous f) (hf₀ : f ≠ 0) :
    ∃ a C : ℝ, ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ∀ r : ℝ, 0 < r → r < 1 →
      Real.circleAverage (fun w => Real.posLog
        ‖heatFourierLaplace t f 0 (cayleyToUpperHalfPlane w + a)‖⁻¹) 0 r ≤ C := by
  have hGap : EqOn (𝓕 (fun x : ℝ => (f x : ℂ))) 0 (Ioo (-(0 : ℝ)) 0) := by simp
  obtain ⟨a, δ, hδ, hEventually⟩ := exists_eventually_norm_heatFourierLaplace_lower_bound
    hf hfCont hf₀ (s := 0) le_rfl hGap (y := 1) zero_lt_one
  let M := 2 * Real.sqrt 2 * Real.sqrt (1 + ∫ x : ℝ, ‖f x‖)
  refine ⟨a, 2 * M - Real.log δ, ?_⟩
  have hT : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [hT, hEventually] with t ht hCenter
  intro r hr hr₁
  let F (w : ℂ) := heatFourierLaplace t f 0 (cayleyToUpperHalfPlane w + a)
  have hF : DifferentiableOn ℂ F (Metric.ball 0 1) :=
    (differentiable_heatFourierLaplace hf ht 0).comp_differentiableOn
      (differentiableOn_cayleyToUpperHalfPlane.add (differentiableOn_const (a : ℂ)))
  have hF₀ : δ ≤ ‖F 0‖ := by
    simpa [F, cayleyToUpperHalfPlane, add_comm] using hCenter
  exact circleAverage_neg_log_norm_le_of_circleAverage_sqrt_norm_le hF hδ hF₀ hr hr₁
    (circleAverage_sqrt_norm_heatFourierLaplace_add_real_le hf ht a hr.le hr₁)

/-- At small heat times the negative logarithm has uniformly bounded
weighted total mass on the real line in a fixed translated chart. -/
theorem exists_eventually_integrable_weighted_neg_log_heatFourierLaplace
    {f : ℝ → ℝ} (hf : Integrable f) (hfCont : Continuous f) (hf₀ : f ≠ 0) :
    ∃ a C : ℝ, ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      let W (x : ℝ) := Real.posLog ‖heatFourierLaplace t f 0 ((x : ℂ) + a)‖⁻¹ / (1 + x ^ 2)
      Integrable W ∧ (∫ x : ℝ, W x) ≤ C := by
  obtain ⟨a, C, hC⟩ := exists_eventually_circleAverage_neg_log_heatFourierLaplace_le hf hfCont hf₀
  refine ⟨a, Real.pi * max C 0, ?_⟩
  have hT : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [hT, hC] with t ht hBound
  exact integrable_weighted_neg_log_of_uniform_radial
    (differentiable_heatFourierLaplace hf ht 0) a hBound

/-- The negative logarithm of the heated transform is integrable with
the centered Cauchy weight, with a uniform total bound for small heat
times. -/
theorem exists_eventually_integrable_weighted_neg_log_heatFourierLaplace_centered
    {f : ℝ → ℝ} (hf : Integrable f) (hfCont : Continuous f) (hf₀ : f ≠ 0) :
    ∃ C : ℝ, ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      let W (x : ℝ) := Real.posLog ‖heatFourierLaplace t f 0 x‖⁻¹ / (1 + x ^ 2)
      Integrable W ∧ (∫ x : ℝ, W x) ≤ C := by
  obtain ⟨a, C, hC⟩ := exists_eventually_integrable_weighted_neg_log_heatFourierLaplace hf hfCont hf₀
  let K := 2 * (1 + a ^ 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K * C, ?_⟩
  have hT : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  filter_upwards [hT, hC] with t ht htC
  obtain ⟨hA, hABound⟩ := htC
  let L (x : ℝ) := Real.posLog ‖heatFourierLaplace t f 0 x‖⁻¹
  let W (x : ℝ) := L x / (1 + x ^ 2)
  let A (x : ℝ) := L (x + a) / (1 + x ^ 2)
  have hG : Continuous (fun x : ℝ => heatFourierLaplace t f 0 x) :=
    (differentiable_heatFourierLaplace hf ht 0).continuous.comp Complex.continuous_ofReal
  have hL : Measurable L := measurable_const.max (Real.measurable_log.comp hG.measurable.norm.inv)
  have hMW : Measurable W := hL.div (by fun_prop)
  have hNorm (x : ℝ) : 1 + x ^ 2 ≤ K * (1 + (x + a) ^ 2) := by
    dsimp [K]
    nlinarith only [sq_nonneg (x + 2 * a), sq_nonneg a, sq_nonneg (x + a),
      mul_nonneg (sq_nonneg a) (sq_nonneg (x + a))]
  have hPt (x : ℝ) : ‖W (x + a)‖ ≤ K * A x := by
    rw [Real.norm_of_nonneg (div_nonneg Real.posLog_nonneg (by positivity) : 0 ≤ W (x + a))]
    dsimp only [W, A]
    rw [← mul_div_assoc]
    exact (div_le_div_iff₀ (by positivity) (by positivity)).2 (by
      calc
        _ ≤ L (x + a) * (K * (1 + (x + a) ^ 2)) :=
          mul_le_mul_of_nonneg_left (hNorm x) Real.posLog_nonneg
        _ = _ := by ring)
  have hAI : Integrable A := by
    simpa only [A, L, Complex.ofReal_add] using hA
  have hAB : (∫ x : ℝ, A x) ≤ C := by
    simpa only [A, L, Complex.ofReal_add] using hABound
  have hTrans : Integrable (fun x : ℝ => W (x + a)) :=
    (hAI.const_mul K).mono' (hMW.comp (by fun_prop)).aestronglyMeasurable (ae_of_all _ hPt)
  have hWInt : Integrable W := by
    have he : (fun x : ℝ => W (x + (-a) + a)) = W := by
      funext x
      congr 1
      ring
    rw [← he]
    exact hTrans.comp_add_right (-a)
  refine ⟨hWInt, ?_⟩
  change (∫ x : ℝ, W x) ≤ K * C
  rw [← integral_add_right_eq_self W a]
  calc
    _ ≤ ∫ x : ℝ, K * A x := integral_mono hTrans (hAI.const_mul K) fun x =>
      (Real.le_norm_self _).trans (hPt x)
    _ ≤ _ := by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hAB hK

end
end MeyerGeneralProblem
