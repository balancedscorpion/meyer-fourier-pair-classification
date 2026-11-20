module

public import MeyerGeneralProblem.Distribution.CompactSchwartzDensity
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

@[expose] public section

/-!
# Entire inverse Fourier kernels of compact cutoffs

Complex differentiation and two integrations by parts give the
inverse-quadratic estimates used by the entire orbit representative.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Topology FourierTransform SchwartzMap

/-- An entire Fourier kernel formed by integrating frequencies over a compact interval. -/
def compactFrequencyKernel (σ : ℂ) (M : ℝ) (φ : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ x in Icc (-M) M, Complex.exp (σ * (x : ℂ) * z) * φ x

/-- A complex derivative of the compact-frequency kernel inserts one frequency factor. -/
theorem hasDerivAt_compactFrequencyKernel
    (σ : ℂ) (M : ℝ) (hM : 0 ≤ M) (φ : ℝ → ℂ) (hφ : Continuous φ) (z₀ : ℂ) :
    HasDerivAt (compactFrequencyKernel σ M φ)
      (compactFrequencyKernel σ M (fun x => (σ * (x : ℂ)) * φ x) z₀) z₀ := by
  let μ := (volume : Measure ℝ).restrict (Icc (-M) M)
  let F (z : ℂ) (x : ℝ) := Complex.exp (σ * (x : ℂ) * z) * φ x
  let F' (z : ℂ) (x : ℝ) := Complex.exp (σ * (x : ℂ) * z) * ((σ * (x : ℂ)) * φ x)
  let D := Real.exp (‖σ‖ * M * (‖z₀‖ + 1))
  have hzle (z : ℂ) (hz : z ∈ Metric.ball z₀ 1) : ‖z‖ ≤ ‖z₀‖ + 1 := by
    have hz' : ‖z - z₀‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
    calc
      ‖z‖ = ‖z - z₀ + z₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
      _ ≤ ‖z₀‖ + 1 := by linarith
  have hxle (x : ℝ) (hx : x ∈ Icc (-M) M) : ‖(x : ℂ)‖ ≤ M := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr hx
  have hExp (z : ℂ) (hz : z ∈ Metric.ball z₀ 1) (x : ℝ) (hx : x ∈ Icc (-M) M) :
      ‖Complex.exp (σ * (x : ℂ) * z)‖ ≤ D := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hxle x hx) (norm_nonneg _)) (hzle z hz)
      (norm_nonneg _) (mul_nonneg (norm_nonneg _) hM)
  have hF (z : ℂ) : AEStronglyMeasurable (F z) μ := by
    apply Continuous.aestronglyMeasurable
    exact (show Continuous (fun x : ℝ => Complex.exp (σ * (x : ℂ) * z)) by fun_prop).mul hφ
  have hF' (z : ℂ) : AEStronglyMeasurable (F' z) μ := by
    apply Continuous.aestronglyMeasurable
    exact (show Continuous (fun x : ℝ => Complex.exp (σ * (x : ℂ) * z)) by fun_prop).mul
      ((continuous_const.mul Complex.continuous_ofReal).mul hφ)
  have hφInt : Integrable φ μ := hφ.continuousOn.integrableOn_compact isCompact_Icc
  have hMem : ∀ᵐ x ∂μ, x ∈ Icc (-M) M := ae_restrict_mem measurableSet_Icc
  have hInt : Integrable (F z₀) μ := by
    apply (hφInt.norm.const_mul D).mono' (hF z₀)
    filter_upwards [hMem] with x hx
    change ‖Complex.exp (σ * (x : ℂ) * z₀) * φ x‖ ≤ D * ‖φ x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hExp z₀ (Metric.mem_ball_self one_pos) x hx) (norm_nonneg _)
  have hBound : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball z₀ 1, ‖F' z x‖ ≤ (D * (‖σ‖ * M)) * ‖φ x‖ := by
    filter_upwards [hMem] with x hx z hz
    change ‖Complex.exp (σ * (x : ℂ) * z) * ((σ * (x : ℂ)) * φ x)‖ ≤ _
    rw [norm_mul, norm_mul, norm_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hExp z hz x hx)
      (mul_le_mul_of_nonneg_left (hxle x hx) (norm_nonneg _)) (by positivity) (Real.exp_pos _).le)
      (norm_nonneg _)
  have hDiff (x : ℝ) (z : ℂ) : HasDerivAt (fun v => F v x) (F' z x) z := by
    have h := (((hasDerivAt_id' z).const_mul (σ * (x : ℂ))).cexp).mul_const (φ x)
    simpa only [F, F', mul_assoc, mul_one] using h
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z₀ one_pos) (Eventually.of_forall hF) hInt (hF' z₀) hBound
    (hφInt.norm.const_mul _) (Eventually.of_forall fun x z _ => hDiff x z)
  exact h.2

/-- Integration by parts transfers one physical factor from the kernel
to the derivative of the compact frequency function. -/
theorem mul_compactFrequencyKernel_eq_neg_deriv
    (σ : ℂ) (M : ℝ) (hM : 0 ≤ M) (φ φ' : ℝ → ℂ)
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hφ' : Continuous φ')
    (hBot : φ (-M) = 0) (hTop : φ M = 0) (z : ℂ) :
    (σ * z) * compactFrequencyKernel σ M φ z = -compactFrequencyKernel σ M φ' z := by
  let c := σ * z
  let e (x : ℝ) := Complex.exp (σ * (x : ℂ) * z)
  let e' (x : ℝ) := c * e x
  have heDiff (x : ℝ) : HasDerivAt e (e' x) x := by
    have hc := ((((hasDerivAt_id' (x : ℂ)).const_mul c).cexp).comp_ofReal)
    have hEq (y : ℝ) : c * (y : ℂ) = σ * (y : ℂ) * z := by dsimp [c]; ring
    simpa only [id_eq, hEq, mul_one, mul_comm (Complex.exp _) c, e, e'] using hc
  have he : Continuous e := continuous_iff_continuousAt.mpr fun x => (heDiff x).continuousAt
  have he' : Continuous e' := continuous_const.mul he
  have hCont : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hφ x).continuousAt
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := -M) (b := M) he.continuousOn hCont.continuousOn
    (fun x _ => heDiff x) (fun x _ => hφ x) (he'.intervalIntegrable _ _) (hφ'.intervalIntegrable _ _)
  rw [hBot, hTop, mul_zero, mul_zero, sub_self, zero_sub] at h
  have hC : (∫ x in -M..M, e' x * φ x) = c * ∫ x in -M..M, e x * φ x := by
    simp only [e', mul_assoc, intervalIntegral.integral_const_mul]
  rw [hC] at h
  have hMM : -M ≤ M := by linarith
  simp only [compactFrequencyKernel, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hMM]
  change c * (∫ x in -M..M, e x * φ x) = -(∫ x in -M..M, e x * φ' x)
  rw [h, neg_neg]

/-- Two integrations by parts give the inverse-quadratic factor
used for uniform bounded-strip domination. -/
theorem sq_mul_compactFrequencyKernel_eq_second_deriv
    (σ : ℂ) (M : ℝ) (hM : 0 ≤ M) (φ φ' φ'' : ℝ → ℂ)
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hφ' : ∀ x, HasDerivAt φ' (φ'' x) x)
    (hφ'' : Continuous φ'') (hBot : φ (-M) = 0) (hTop : φ M = 0)
    (hBot' : φ' (-M) = 0) (hTop' : φ' M = 0) (z : ℂ) :
    (σ * z) ^ 2 * compactFrequencyKernel σ M φ z = compactFrequencyKernel σ M φ'' z := by
  have hc : Continuous φ' := continuous_iff_continuousAt.mpr fun x => (hφ' x).continuousAt
  have h1 := mul_compactFrequencyKernel_eq_neg_deriv σ M hM φ φ' hφ hc hBot hTop z
  have h2 := mul_compactFrequencyKernel_eq_neg_deriv σ M hM φ' φ'' hφ' hφ'' hBot' hTop' z
  rw [pow_two, mul_assoc, h1, mul_neg, h2, neg_neg]

private theorem norm_compactFrequencyKernel_le_of_abs_im_le
    (σ : ℂ) (hσ : σ.re = 0) (M : ℝ) (hM : 0 ≤ M)
    (φ : ℝ → ℂ) (hφ : Continuous φ) (z : ℂ) (Y : ℝ) (hY : |z.im| ≤ Y) :
    ‖compactFrequencyKernel σ M φ z‖ ≤
      Real.exp (‖σ‖ * M * Y) * ∫ x in Icc (-M) M, ‖φ x‖ := by
  let D := Real.exp (‖σ‖ * M * Y)
  let ν := (volume : Measure ℝ).restrict (Icc (-M) M)
  have hInt : Integrable φ ν := hφ.continuousOn.integrableOn_compact isCompact_Icc
  have hMem : ∀ᵐ x ∂ν, x ∈ Icc (-M) M := ae_restrict_mem measurableSet_Icc
  have hDom : ∀ᵐ (x : ℝ) ∂ν, ‖Complex.exp (σ * (x : ℂ) * z) * φ x‖ ≤ D * ‖φ x‖ := by
    filter_upwards [hMem] with x hx
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hRe : (σ * (x : ℂ) * z).re = -(σ.im * x * z.im) := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        hσ, zero_mul, mul_zero, sub_zero, zero_add, zero_sub]
    rw [hRe]
    calc
      _ ≤ |- (σ.im * x * z.im)| := le_abs_self _
      _ = |σ.im| * |x| * |z.im| := by rw [abs_neg, abs_mul, abs_mul]
      _ ≤ ‖σ‖ * M * Y :=
        mul_le_mul (mul_le_mul (Complex.abs_im_le_norm _) (abs_le.mpr hx) (abs_nonneg _) (norm_nonneg _))
          hY (abs_nonneg _) (mul_nonneg (norm_nonneg _) hM)
  calc
    _ ≤ ∫ x, D * ‖φ x‖ ∂ν := norm_integral_le_of_norm_le (hInt.norm.const_mul D) hDom
    _ = _ := by rw [integral_const_mul]

/-- A smooth compact Fourier kernel has locally uniform inverse-quadratic
decay along horizontal translates. -/
theorem exists_norm_compactFrequencyKernel_le_inverse_quadratic
    (σ : ℂ) (hσ : σ.re = 0) (hσ₀ : σ ≠ 0) (M : ℝ) (hM : 0 ≤ M)
    (φ φ' φ'' : ℝ → ℂ) (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ' : ∀ x, HasDerivAt φ' (φ'' x) x) (hφ'' : Continuous φ'')
    (hBot : φ (-M) = 0) (hTop : φ M = 0)
    (hBot' : φ' (-M) = 0) (hTop' : φ' M = 0) (z₀ : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Metric.ball z₀ 1, ∀ x : ℝ,
      ‖compactFrequencyKernel σ M φ (z - (x : ℂ))‖ ≤ C * (1 + x ^ 2)⁻¹ := by
  let Y := ‖z₀‖ + 1
  let D := Real.exp (‖σ‖ * M * Y)
  let A := D * ∫ u in Icc (-M) M, ‖φ u‖
  let B := D * ∫ u in Icc (-M) M, ‖φ'' u‖
  let C := (2 * (1 + Y ^ 2)) * (A + B / ‖σ‖ ^ 2)
  have hA : 0 ≤ A := mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)
  have hB : 0 ≤ B := mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)
  have hS : 0 < ‖σ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hσ₀)
  have hCont : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hφ x).continuousAt
  refine ⟨C, by dsimp [C]; positivity, fun z hz x => ?_⟩
  let v := z - (x : ℂ)
  let K := compactFrequencyKernel σ M φ v
  have hZ : ‖z‖ ≤ Y := by
    have hz' : ‖z - z₀‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
    calc
      ‖z‖ = ‖z - z₀ + z₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
      _ ≤ Y := by dsimp [Y]; linarith
  have hV : |v.im| ≤ Y := by
    have hIm : v.im = z.im := by simp [v]
    rw [hIm]
    exact (Complex.abs_im_le_norm z).trans hZ
  have hK : ‖K‖ ≤ A := norm_compactFrequencyKernel_le_of_abs_im_le σ hσ M hM φ hCont v Y hV
  have hK₂ : ‖v‖ ^ 2 * ‖K‖ ≤ B / ‖σ‖ ^ 2 := by
    apply (le_div_iff₀ hS).mpr
    have hN := congrArg norm (sq_mul_compactFrequencyKernel_eq_second_deriv
      σ M hM φ φ' φ'' hφ hφ' hφ'' hBot hTop hBot' hTop' v)
    simp only [norm_mul, norm_pow, mul_pow] at hN
    have hF : ‖v‖ ^ 2 * ‖K‖ * ‖σ‖ ^ 2 =
        (‖σ‖ ^ 2 * ‖v‖ ^ 2) * ‖compactFrequencyKernel σ M φ v‖ := by dsimp [K]; ring
    rw [hF, hN]
    exact norm_compactFrequencyKernel_le_of_abs_im_le σ hσ M hM φ'' hφ'' v Y hV
  have hX : |x| ≤ ‖v‖ + Y := by
    have he : (x : ℂ) = z - v := by dsimp [v]; abel
    calc
      |x| = ‖(x : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖z‖ + ‖v‖ := by rw [he]; exact norm_sub_le _ _
      _ ≤ ‖v‖ + Y := by linarith
  have hXY : x ^ 2 ≤ 2 * (‖v‖ ^ 2 + Y ^ 2) := by
    have hY₀ : 0 ≤ Y := by dsimp [Y]; positivity
    have hn : 0 ≤ ‖v‖ + Y := add_nonneg (norm_nonneg _) hY₀
    have ht := mul_self_le_mul_self (abs_nonneg x) hX
    rw [← sq, sq_abs, ← sq] at ht
    nlinarith [sq_nonneg (‖v‖ - Y)]
  have hGrowth : 1 + x ^ 2 ≤ 2 * (1 + Y ^ 2) * (1 + ‖v‖ ^ 2) := by
    nlinarith [mul_nonneg (sq_nonneg Y) (sq_nonneg ‖v‖)]
  have hBound : (1 + ‖v‖ ^ 2) * ‖K‖ ≤ A + B / ‖σ‖ ^ 2 := by
    rw [add_mul, one_mul]
    exact add_le_add hK hK₂
  change ‖K‖ ≤ C * (1 + x ^ 2)⁻¹
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity)).2
  calc
    ‖K‖ * (1 + x ^ 2) ≤ ‖K‖ * (2 * (1 + Y ^ 2) * (1 + ‖v‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hGrowth (norm_nonneg _)
    _ = (2 * (1 + Y ^ 2)) * ((1 + ‖v‖ ^ 2) * ‖K‖) := by ring
    _ ≤ C := mul_le_mul_of_nonneg_left hBound (by positivity)

/-- A compactly supported Schwartz function has an entire inverse Fourier
kernel with locally uniform inverse-quadratic decay. Its derivative has
the same decay and the real restriction is the ordinary inverse transform. -/
theorem exists_entire_inverseFourierKernel_of_hasCompactSupport
    (χ : SchwartzMap ℝ ℂ) (hχ : HasCompactSupport (χ : ℝ → ℂ)) :
    ∃ k k' : ℂ → ℂ, (∀ z, HasDerivAt k (k' z) z) ∧ Continuous k' ∧
      (∀ x : ℝ, k (x : ℂ) = (𝓕⁻ χ : SchwartzMap ℝ ℂ) x) ∧
      ∀ z₀ : ℂ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Metric.ball z₀ 1, ∀ x : ℝ,
        ‖k (z - (x : ℂ))‖ ≤ C * (1 + x ^ 2)⁻¹ ∧
        ‖k' (z - (x : ℂ))‖ ≤ C * (1 + x ^ 2)⁻¹ := by
  let σ : ℂ := 2 * Real.pi * Complex.I
  let φ : ℝ → ℂ := χ
  let ψ (x : ℝ) := (σ * (x : ℂ)) * φ x
  have hσ : σ.re = 0 := by simp [σ, Complex.mul_re]
  have hσ₀ : σ ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hφ : ContDiff ℝ ∞ φ := χ.smooth _
  have hψ : ContDiff ℝ ∞ ψ := (contDiff_const.mul Complex.ofRealCLM.contDiff).mul hφ
  have hψSupp : HasCompactSupport ψ := hχ.mul_left (f := fun x : ℝ => σ * (x : ℂ))
  let S := (tsupport φ ∪ tsupport (deriv φ)) ∪ (tsupport ψ ∪ tsupport (deriv ψ))
  have hS : IsCompact S := (hχ.union hχ.deriv).union (hψSupp.union hψSupp.deriv)
  obtain ⟨M, hM, hSub⟩ := hS.isBounded.subset_ball_lt 0 0
  have hEnds (u : ℝ → ℂ) (hu : tsupport u ⊆ S) : u (-M) = 0 ∧ u M = 0 := by
    have hZ (x : ℝ) (hx : ¬ |x| < M) : u x = 0 := by
      by_contra hn
      have hBall := hSub (hu (subset_tsupport _ hn))
      exact hx (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hBall)
    exact ⟨hZ (-M) (by simp [abs_of_pos hM]), hZ M (by simp [abs_of_pos hM])⟩
  have hφEnds := hEnds φ (Set.Subset.trans Set.subset_union_left Set.subset_union_left)
  have hφ'Ends := hEnds (deriv φ) (Set.Subset.trans Set.subset_union_right Set.subset_union_left)
  have hψEnds := hEnds ψ (Set.Subset.trans Set.subset_union_left Set.subset_union_right)
  have hψ'Ends := hEnds (deriv ψ) (Set.Subset.trans Set.subset_union_right Set.subset_union_right)
  let k := compactFrequencyKernel σ M φ
  let k' := compactFrequencyKernel σ M ψ
  have hk (z : ℂ) : HasDerivAt k (k' z) z :=
    hasDerivAt_compactFrequencyKernel σ M hM.le φ hφ.continuous z
  have hk' : Continuous k' := continuous_iff_continuousAt.mpr fun z =>
    (hasDerivAt_compactFrequencyKernel σ M hM.le ψ hψ.continuous z).continuousAt
  refine ⟨k, k', hk, hk', ?_, ?_⟩
  · intro x
    have hZero (u : ℝ) (hu : u ∉ Icc (-M) M) : φ u = 0 := by
      by_contra hn
      have hBall := hSub (show u ∈ S from Or.inl (Or.inl (subset_tsupport _ hn)))
      have hAbs : |u| < M := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hBall
      exact hu (abs_le.mp hAbs.le)
    change (∫ u in Icc (-M) M, Complex.exp (σ * (u : ℂ) * (x : ℂ)) * φ u) = _
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun u hu => by rw [hZero u hu, mul_zero]), SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with u
    simp only [smul_eq_mul, Real.inner_apply]
    congr 2
    dsimp [σ]
    push_cast
    ring
  · intro z₀
    have hDecay (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
        (huEnd : u (-M) = 0 ∧ u M = 0) (hu'End : deriv u (-M) = 0 ∧ deriv u M = 0) :
        ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Metric.ball z₀ 1, ∀ x : ℝ,
          ‖compactFrequencyKernel σ M u (z - (x : ℂ))‖ ≤ C * (1 + x ^ 2)⁻¹ := by
      have hu' := (contDiff_infty_iff_deriv.mp hu).2
      have hu'' := (contDiff_infty_iff_deriv.mp hu').2
      exact exists_norm_compactFrequencyKernel_le_inverse_quadratic σ hσ hσ₀ M hM.le
        u (deriv u) (deriv (deriv u)) (fun x => (hu.differentiable (by simp) x).hasDerivAt)
        (fun x => (hu'.differentiable (by simp) x).hasDerivAt) hu''.continuous
        huEnd.1 huEnd.2 hu'End.1 hu'End.2 z₀
    obtain ⟨C, hC, hBound⟩ := hDecay φ hφ hφEnds hφ'Ends
    obtain ⟨C', hC', hBound'⟩ := hDecay ψ hψ hψEnds hψ'Ends
    refine ⟨C + C', add_nonneg hC hC', fun z hz x => ?_⟩
    exact ⟨(hBound z hz x).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC') (by positivity)),
      (hBound' z hz x).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (by positivity))⟩

end
end MeyerGeneralProblem
