module

public import MeyerGeneralProblem.Distribution.FourierLaplaceHeatLimit
public import MeyerGeneralProblem.Cardinal.Strong.CauchyJump

@[expose] public section

/-!
# Detecting the lower edge by a Laplace transform

The Stieltjes integral of an integrable complex density has a pointwise
jump at every continuity point. This detects the lower edge even when
the Laplace density has complex signs.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Set StrongParity
open scoped FourierTransform Topology

/-- The Stieltjes integral in the convention with denominator z - x. -/
def stieltjesDensity (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, (z - x)⁻¹ * g x

private theorem abs_im_le_norm_sub_real (z : ℂ) (x : ℝ) : |z.im| ≤ ‖z - x‖ := by
  simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using
    Complex.abs_im_le_norm (z - x)

private theorem sub_real_ne_zero_of_abs_im_pos {z : ℂ} (hz : 0 < |z.im|) (x : ℝ) :
    z - x ≠ 0 := norm_pos_iff.mp (hz.trans_le (abs_im_le_norm_sub_real z x))

private theorem integrable_stieltjesDensity_integrand {g : ℝ → ℂ} (hg : Integrable g)
    {z : ℂ} (hz : 0 < |z.im|) :
    Integrable (fun x : ℝ => (z - x)⁻¹ * g x) := by
  have hCont : Continuous (fun x : ℝ => (z - x)⁻¹ : ℝ → ℂ) :=
    (show Continuous (fun x : ℝ => z - (x : ℂ)) by fun_prop).inv₀
      (sub_real_ne_zero_of_abs_im_pos hz)
  refine (hg.norm.const_mul |z.im|⁻¹).mono'
    (hCont.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
  filter_upwards with x
  rw [norm_mul, norm_inv]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hz (abs_im_le_norm_sub_real z x)) (norm_nonneg _)

/-- The Stieltjes integral is holomorphic on both sides of the real line. -/
theorem differentiableOn_stieltjesDensity {g : ℝ → ℂ} (hg : Integrable g) :
    DifferentiableOn ℂ (stieltjesDensity g) {z : ℂ | z.im ≠ 0} := by
  intro z hz
  have hz' : 0 < |z.im| := abs_pos.mpr hz
  let a := |z.im| / 2
  have ha : 0 < a := half_pos hz'
  let K (w : ℂ) (x : ℝ) := (w - x)⁻¹ * g x
  let L (w : ℂ) (x : ℝ) := (-(w - x)⁻¹ ^ 2) * g x
  have hW {w : ℂ} (hw : w ∈ Metric.ball z a) : a < |w.im| := by
    have hDist := Metric.mem_ball.mp hw
    rw [dist_eq_norm] at hDist
    have hIm : |z.im| ≤ |w.im| + ‖w - z‖ := by
      calc
        |z.im| = |w.im + (z - w).im| := by rw [Complex.sub_im]; ring_nf
        _ ≤ |w.im| + |(z - w).im| := abs_add_le _ _
        _ ≤ _ := by rw [norm_sub_rev]; exact add_le_add (le_refl _) (Complex.abs_im_le_norm _)
    dsimp only [a] at *
    linarith only [hDist, hIm]
  have hCont : Continuous (fun x : ℝ => (z - (x : ℂ))⁻¹) :=
    (show Continuous (fun x : ℝ => z - (x : ℂ)) by fun_prop).inv₀
      (sub_real_ne_zero_of_abs_im_pos hz')
  have hL : AEStronglyMeasurable (L z) volume :=
    ((hCont.pow 2).neg.aestronglyMeasurable.mul hg.aestronglyMeasurable)
  have hNear : ∀ᶠ w in 𝓝 z, w ∈ Metric.ball z a := Metric.ball_mem_nhds z ha
  have hD := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ)) (F := K) (F' := L)
    (Metric.ball_mem_nhds z ha)
    (hNear.mono fun w hw =>
      (integrable_stieltjesDensity_integrand hg (ha.trans (hW hw))).aestronglyMeasurable)
    (integrable_stieltjesDensity_integrand hg hz') hL
    (ae_of_all _ fun x w hw => by
      change ‖(-(w - x)⁻¹ ^ 2) * g x‖ ≤ a⁻¹ ^ 2 * ‖g x‖
      rw [norm_mul, norm_neg, norm_pow, norm_inv]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _))
          (inv_anti₀ ha ((hW hw).le.trans (abs_im_le_norm_sub_real w x))) _)
        (norm_nonneg _))
    (hg.norm.const_mul (a⁻¹ ^ 2))
    (ae_of_all _ fun x w hw => by
      have hSub := sub_real_ne_zero_of_abs_im_pos (ha.trans (hW hw)) x
      have hInv := ((hasDerivAt_id w).sub_const (x : ℂ)).inv hSub
      simpa only [K, L, Pi.inv_apply, id_eq, neg_one_mul, inv_pow, div_eq_mul_inv, one_mul] using
        hInv.mul_const (g x))).2
  exact hD.differentiableAt.differentiableWithinAt

/-- The upper-minus-lower difference of the Stieltjes integral detects
the density at every real continuity point. -/
theorem tendsto_stieltjesDensity_jump {g : ℝ → ℂ} (hg : Integrable g) {x : ℝ}
    (hx : ContinuousAt g x) :
    Tendsto (fun t : ℝ => stieltjesDensity g ((x : ℂ) + t * Complex.I) -
      stieltjesDensity g ((x : ℂ) - t * Complex.I)) (𝓝[>] (0 : ℝ))
      (𝓝 (-((2 * Real.pi : ℝ) * Complex.I) * g x)) := by
  have h := realPoleJump_integral_tendsto (1 : ℂ) hg hx
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  have hUpper : 0 < |((x : ℂ) + t * Complex.I).im| := by
    simpa [Complex.add_im, Complex.mul_im, abs_of_pos ht'] using ht'
  have hLower : 0 < |((x : ℂ) - t * Complex.I).im| := by
    simpa [Complex.sub_im, Complex.mul_im, abs_of_pos ht'] using ht'
  unfold stieltjesDensity
  rw [← integral_sub (integrable_stieltjesDensity_integrand hg hUpper)
    (integrable_stieltjesDensity_integrand hg hLower)]
  apply integral_congr_ae
  filter_upwards with y
  rw [← sub_mul, realPoleJump, Complex.ofReal_sub, one_div, one_div]
  have h₁ : (x : ℂ) + t * Complex.I - y = -((y : ℂ) - x - t * Complex.I) := by ring
  have h₂ : (x : ℂ) - t * Complex.I - y = -((y : ℂ) - x + t * Complex.I) := by ring
  rw [h₁, h₂, inv_neg, inv_neg]
  ring

/-- The Laplace transform over the positive half-line, in the convention
with kernel exp (-y x). -/
def positiveLaplaceDensity (g : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), (Real.exp (-(y * x)) : ℂ) * g x

private theorem norm_positiveLaplaceDensity_le {g : ℝ → ℂ} (hg : Integrable g)
    {y : ℝ} (hy : 0 ≤ y) :
    ‖positiveLaplaceDensity g y‖ ≤ ∫ x : ℝ, ‖g x‖ := by
  let F (x : ℝ) := (Real.exp (-(y * x)) : ℂ) * g x
  have hPoint : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), ‖F x‖ ≤ ‖g x‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change ‖(Real.exp (-(y * x)) : ℂ) * g x‖ ≤ ‖g x‖
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg hy hx.le)))
  have hF : IntegrableOn F (Ioi (0 : ℝ)) :=
    hg.norm.integrableOn.mono'
      (((Complex.continuous_ofReal.comp (by fun_prop)).aestronglyMeasurable).mul
        hg.integrableOn.aestronglyMeasurable) hPoint
  exact ((norm_integral_le_integral_norm F).trans (integral_mono_ae hF.norm
    hg.norm.integrableOn hPoint)).trans (setIntegral_le_integral hg.norm (ae_of_all _ fun _ => norm_nonneg _))

private theorem continuousOn_positiveLaplaceDensity {g : ℝ → ℂ} (hg : Integrable g) :
    ContinuousOn (positiveLaplaceDensity g) (Ici (0 : ℝ)) := by
  apply continuousOn_of_dominated (bound := fun x : ℝ => ‖g x‖)
  · intro y _
    have hE : Continuous (fun x : ℝ => (Real.exp (-(y * x)) : ℂ)) := by fun_prop
    exact hE.aestronglyMeasurable.mul hg.integrableOn.aestronglyMeasurable
  · intro y hy
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg hy hx.le)))
  · exact hg.norm.integrableOn
  · filter_upwards with x
    fun_prop

/-- The negative of the second Laplace integral in the Laplace variable.
Where it converges to a holomorphic function, it continues the
Stieltjes integral. -/
def continuedStieltjesDensity (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  -(∫ y in Ioi (0 : ℝ), positiveLaplaceDensity g y * Complex.exp (z * y))

private theorem differentiableOn_continuedStieltjesDensity
    {g : ℝ → ℂ} (hg : Integrable g) {d C : ℝ} (hC : 0 ≤ C)
    (hDecay : ∀ y > 0, ‖positiveLaplaceDensity g y‖ ≤ C * Real.exp (-d * y)) :
    DifferentiableOn ℂ (continuedStieltjesDensity g) {z : ℂ | z.re < d} := by
  apply DifferentiableOn.neg
  intro z hz
  have hz' : z.re < d := hz
  let a := (d - z.re) / 2
  have ha : 0 < a := half_pos (sub_pos.mpr hz')
  let ν := volume.restrict (Ioi (0 : ℝ))
  let K (w : ℂ) (y : ℝ) := positiveLaplaceDensity g y * Complex.exp (w * y)
  let L (w : ℂ) (y : ℝ) := K w y * (y : ℂ)
  have hW {w : ℂ} (hw : w ∈ Metric.ball z a) : w.re ≤ d - a := by
    have hDist := Metric.mem_ball.mp hw
    rw [dist_eq_norm] at hDist
    have hLe : w.re - z.re ≤ ‖w - z‖ := by
      rw [← Complex.sub_re]
      exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
    dsimp only [a] at *
    linarith only [hDist, hLe]
  have hG : AEStronglyMeasurable (positiveLaplaceDensity g) ν :=
    ((continuousOn_positiveLaplaceDensity hg).mono Ioi_subset_Ici_self).aestronglyMeasurable
      measurableSet_Ioi
  have hMeas (w : ℂ) : AEStronglyMeasurable (K w) ν :=
    hG.mul (show Continuous (fun y : ℝ => Complex.exp (w * y)) by fun_prop).aestronglyMeasurable
  have hBound {w : ℂ} (hw : w ∈ Metric.ball z a) {y : ℝ} (hy : 0 < y) :
      ‖K w y‖ ≤ C * Real.exp (-a * y) := by
    change ‖positiveLaplaceDensity g y * Complex.exp (w * y)‖ ≤ _
    rw [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    refine (mul_le_mul_of_nonneg_right (hDecay y hy) (Real.exp_pos _).le).trans ?_
    rw [mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hC
    linarith only [mul_le_mul_of_nonneg_right (hW hw) hy.le]
  have hE : Integrable (fun y : ℝ => Real.exp (-a * y)) ν :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0
  have hKInt : Integrable (K z) ν := (hE.const_mul C).mono' (hMeas z)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        exact hBound (Metric.mem_ball_self ha) hy)
  have hTimes : Integrable (fun y : ℝ => C * (y * Real.exp (-a * y))) ν := by
    have he := integrableOn_rpow_mul_exp_neg_mul_rpow
      (b := a) (p := 1) (s := 1) (by norm_num) one_pos ha
    simpa only [Real.rpow_one] using he.const_mul C
  have hNear : ∀ᶠ w in 𝓝 z, w ∈ Metric.ball z a := Metric.ball_mem_nhds z ha
  have hD := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := ν) (F := K) (F' := L)
    (Metric.ball_mem_nhds z ha)
    (Eventually.of_forall hMeas) hKInt
    ((hMeas z).mul Complex.continuous_ofReal.aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy w hw
      have hy' : 0 < y := hy
      change ‖K w y * (y : ℂ)‖ ≤ _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hy'.le]
      calc
        _ ≤ (C * Real.exp (-a * y)) * y :=
          mul_le_mul_of_nonneg_right (hBound hw hy') hy'.le
        _ = _ := by ring)
    hTimes
    (ae_of_all _ fun y w _ => by
      simpa only [K, L, id_eq, one_mul, mul_assoc,
        mul_comm (y : ℂ) (Complex.exp (w * y))] using
        (((hasDerivAt_id w).mul_const (y : ℂ)).cexp.const_mul (positiveLaplaceDensity g y)))).2
  exact hD.differentiableAt.differentiableWithinAt

private theorem continuedStieltjesDensity_eq_stieltjesDensity
    {g : ℝ → ℂ} (hg : Integrable g) {z : ℂ} (hz : z.re < 0) :
    continuedStieltjesDensity g z = stieltjesDensity ((Ioi (0 : ℝ)).indicator g) z := by
  let ν := volume.restrict (Ioi (0 : ℝ))
  let K (y x : ℝ) := Complex.exp ((z - x) * y) * g x
  have hE : Integrable (fun y : ℝ => Real.exp (z.re * y)) ν :=
    integrableOn_exp_mul_Ioi hz 0
  have hExp : Continuous (fun p : ℝ × ℝ => Complex.exp ((z - p.2) * p.1)) := by fun_prop
  have hK : Integrable (Function.uncurry K) (ν.prod ν) := by
    apply (hE.mul_prod hg.norm.integrableOn).mono'
      (hExp.aestronglyMeasurable.mul hg.integrableOn.aestronglyMeasurable.comp_snd)
    have hAe : ∀ᵐ p : ℝ × ℝ ∂ν.prod ν, p.1 ∈ Ioi (0 : ℝ) ∧ p.2 ∈ Ioi (0 : ℝ) :=
      (Measure.ae_prod_iff_ae_ae (measurableSet_Ioi.prod measurableSet_Ioi)).mpr
        (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
            exact ⟨hy, hx⟩)
    filter_upwards [hAe] with p hp
    change ‖Complex.exp ((z - p.2) * p.1) * g p.2‖ ≤ Real.exp (z.re * p.1) * ‖g p.2‖
    rw [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.sub_re, Complex.ofReal_re]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (sub_le_self _ hp.2.le) hp.1.le)
  unfold continuedStieltjesDensity
  have hOuter : (∫ y, positiveLaplaceDensity g y * Complex.exp (z * y) ∂ν) =
      ∫ y, ∫ x, K y x ∂ν ∂ν := by
    apply integral_congr_ae
    filter_upwards with y
    unfold positiveLaplaceDensity
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with x
    simp only [K, Complex.ofReal_exp, mul_right_comm _ (g x), ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hOuter, integral_integral_swap hK, ← integral_neg]
  unfold stieltjesDensity
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · simp only [indicator_of_mem hx]
    have hRe : (z - (x : ℂ)).re < 0 := by
      rw [Complex.sub_re, Complex.ofReal_re]
      linarith only [hz, show 0 < x from hx]
    have hComp : (∫ y, K y x ∂ν) =
        (∫ y, Complex.exp ((z - x) * y) ∂ν) * g x := integral_mul_const _ _
    rw [hComp, ← neg_mul]
    change -(∫ y in Ioi (0 : ℝ), Complex.exp ((z - x) * y)) * g x = _
    rw [integral_exp_mul_complex_Ioi hRe]
    simp [div_eq_mul_inv]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

private theorem eqOn_continuedStieltjesDensity_of_sign
    {g : ℝ → ℂ} (hg : Integrable g) {d C : ℝ} (hd : 0 < d) (hC : 0 ≤ C)
    (hDecay : ∀ y > 0, ‖positiveLaplaceDensity g y‖ ≤ C * Real.exp (-d * y))
    {σ : ℝ} (hσ : σ ≠ 0) :
    EqOn (continuedStieltjesDensity g) (stieltjesDensity ((Ioi (0 : ℝ)).indicator g))
      ({z : ℂ | z.re < d} ∩ {z : ℂ | 0 < σ * z.im}) := by
  let U := {z : ℂ | z.re < d} ∩ {z : ℂ | 0 < σ * z.im}
  have hOpen : IsOpen U :=
    (isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt continuous_const (continuous_const.mul Complex.continuous_im))
  have hL : IsLinearMap ℝ (fun z : ℂ => σ * z.im) := by
    refine ⟨?_, ?_⟩
    · intro z w
      simp [Complex.add_im, mul_add]
    · intro x z
      simp [smul_eq_mul]
      ring
  have hRe : IsLinearMap ℝ Complex.re :=
    ⟨Complex.add_re, Complex.smul_re⟩
  have hConv : Convex ℝ U := (convex_halfSpace_lt hRe d).inter (convex_halfSpace_gt hL 0)
  have h₁ := ((differentiableOn_continuedStieltjesDensity hg hC hDecay).mono
    (show U ⊆ {z : ℂ | z.re < d} from inter_subset_left)).analyticOnNhd hOpen
  have h₂ : AnalyticOnNhd ℂ (stieltjesDensity ((Ioi (0 : ℝ)).indicator g)) U := by
    apply DifferentiableOn.analyticOnNhd _ hOpen
    apply (differentiableOn_stieltjesDensity (hg.indicator measurableSet_Ioi)).mono
    intro z hz
    have hpos : 0 < σ * z.im := hz.2
    intro hz₀
    rw [hz₀, mul_zero] at hpos
    exact (lt_irrefl _) hpos
  let z₀ : ℂ := -1 + (σ : ℂ) * Complex.I
  have hzRe : z₀.re < 0 := by simp [z₀, Complex.add_re, Complex.mul_re, Complex.neg_re]
  have hzIm : z₀.im = σ := by simp [z₀, Complex.add_im, Complex.mul_im, Complex.neg_im]
  have hz₀ : z₀ ∈ U := ⟨hzRe.trans hd, by
    change 0 < σ * z₀.im
    rw [hzIm]
    exact mul_self_pos.mpr hσ⟩
  have hNear : ∀ᶠ z in 𝓝[≠] z₀, z.re < 0 :=
    mem_nhdsWithin_of_mem_nhds ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds hzRe)
  exact h₁.eqOn_of_preconnected_of_frequently_eq h₂ hConv.isPreconnected hz₀
    (hNear.mono fun _ hz => continuedStieltjesDensity_eq_stieltjesDensity hg hz).frequently

/-- Extra exponential decay of the positive Laplace transform forces
the original density to vanish at its continuity points below the
claimed decay rate. -/
theorem eq_zero_of_positiveLaplaceDensity_exponential_bound
    {g : ℝ → ℂ} (hg : Integrable g) {d C : ℝ} (hd : 0 < d) (hC : 0 ≤ C)
    (hDecay : ∀ y > 0, ‖positiveLaplaceDensity g y‖ ≤ C * Real.exp (-d * y))
    {x : ℝ} (hx : 0 < x) (hxd : x < d) (hCont : ContinuousAt g x) : g x = 0 := by
  let G := continuedStieltjesDensity g
  let g₀ := (Ioi (0 : ℝ)).indicator g
  have hg₀ : Integrable g₀ := hg.indicator measurableSet_Ioi
  have hCont₀ : ContinuousAt g₀ x := hCont.congr (by
    filter_upwards [Ioi_mem_nhds hx] with a ha
    simp only [g₀, indicator_of_mem ha])
  have hUp := eqOn_continuedStieltjesDensity_of_sign hg hd hC hDecay (σ := 1) one_ne_zero
  have hDown := eqOn_continuedStieltjesDensity_of_sign hg hd hC hDecay (σ := -1)
    (by norm_num)
  have hG : ContinuousAt G (x : ℂ) :=
    (((differentiableOn_continuedStieltjesDensity hg hC hDecay).differentiableAt
      ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds
        (show (x : ℂ).re < d by simpa only [Complex.ofReal_re] using hxd)))).continuousAt
  have hPlus : Tendsto (fun t : ℝ => (x : ℂ) + t * Complex.I)
      (𝓝[>] (0 : ℝ)) (𝓝 (x : ℂ)) := by
    have hP : Continuous (fun t : ℝ => (x : ℂ) + t * Complex.I) := by fun_prop
    have hLim : Tendsto (fun t : ℝ => (x : ℂ) + t * Complex.I)
        (𝓝[>] (0 : ℝ)) (𝓝 ((x : ℂ) + (↑(0 : ℝ) : ℂ) * Complex.I)) :=
      hP.continuousAt.continuousWithinAt
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hLim
  have hMinus : Tendsto (fun t : ℝ => (x : ℂ) - t * Complex.I)
      (𝓝[>] (0 : ℝ)) (𝓝 (x : ℂ)) := by
    have hP : Continuous (fun t : ℝ => (x : ℂ) - t * Complex.I) := by fun_prop
    have hLim : Tendsto (fun t : ℝ => (x : ℂ) - t * Complex.I)
        (𝓝[>] (0 : ℝ)) (𝓝 ((x : ℂ) - (↑(0 : ℝ) : ℂ) * Complex.I)) :=
      hP.continuousAt.continuousWithinAt
    simpa only [Complex.ofReal_zero, zero_mul, sub_zero] using hLim
  have hV : Tendsto (fun t : ℝ => G ((x : ℂ) + t * Complex.I) -
      G ((x : ℂ) - t * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def, sub_self] using (hG.tendsto.comp hPlus).sub (hG.tendsto.comp hMinus)
  have hV' : Tendsto (fun t : ℝ => stieltjesDensity g₀ ((x : ℂ) + t * Complex.I) -
      stieltjesDensity g₀ ((x : ℂ) - t * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply hV.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht₀ : 0 < t := ht
    have hp₁ : ((x : ℂ) + t * Complex.I).re < d := by
      simpa [Complex.add_re, Complex.mul_re] using hxd
    have hm₁ : ((x : ℂ) - t * Complex.I).re < d := by
      simpa [Complex.sub_re, Complex.mul_re] using hxd
    have hp₂ : 0 < 1 * ((x : ℂ) + t * Complex.I).im := by
      simpa [Complex.add_im, Complex.mul_im] using ht₀
    have hm₂ : 0 < (-1) * ((x : ℂ) - t * Complex.I).im := by
      simpa [Complex.sub_im, Complex.mul_im] using ht₀
    exact congrArg₂ (· - ·) (hUp ⟨hp₁, hp₂⟩) (hDown ⟨hm₁, hm₂⟩)
  have hEq := tendsto_nhds_unique (tendsto_stieltjesDensity_jump hg₀ hCont₀) hV'
  have hFactor : -((2 * Real.pi : ℝ) * Complex.I : ℂ) ≠ 0 := by
    apply neg_ne_zero.mpr
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.two_pi_pos.ne') Complex.I_ne_zero
  have hZero := (mul_eq_zero.mp hEq).resolve_left hFactor
  simpa only [g₀, indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)] using hZero

/-- When nonzero continuity points approach the lower edge, no positive
exponential rate bounds its Laplace transform on the full tail. -/
theorem frequently_positiveLaplaceDensity_norm_gt_exp
    {g : ℝ → ℂ} (hg : Integrable g)
    (hEdge : ∀ d > 0, ∃ x ∈ Ioo 0 d, ContinuousAt g x ∧ g x ≠ 0)
    {d : ℝ} (hd : 0 < d) :
    ∃ᶠ y : ℝ in atTop, Real.exp (-d * y) < ‖positiveLaplaceDensity g y‖ := by
  by_contra! hSmall
  obtain ⟨Y, hY⟩ := eventually_atTop.1 hSmall
  let M := ∫ x : ℝ, ‖g x‖
  let C := max 1 (M * Real.exp (d * max Y 0))
  have hC : 0 ≤ C := zero_le_one.trans (le_max_left _ _)
  have hM : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
  have hDecay (y : ℝ) (hy : 0 < y) : ‖positiveLaplaceDensity g y‖ ≤ C * Real.exp (-d * y) := by
    by_cases hyY : Y ≤ y
    · exact (hY y hyY).trans (le_mul_of_one_le_left (Real.exp_pos _).le (le_max_left _ _))
    · have hyB : y ≤ max Y 0 := (lt_of_not_ge hyY).le.trans (le_max_left _ _)
      calc
        _ ≤ M := norm_positiveLaplaceDensity_le hg hy.le
        _ = (M * Real.exp (d * y)) * Real.exp (-d * y) := by
          rw [mul_assoc, ← Real.exp_add]
          have hz : d * y + -d * y = 0 := by ring
          rw [hz, Real.exp_zero, mul_one]
        _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left hyB hd.le)) hM).trans (le_max_right _ _)
  obtain ⟨x, hx, hCont, hx₀⟩ := hEdge d hd
  exact hx₀ (eq_zero_of_positiveLaplaceDensity_exponential_bound hg hd hC hDecay hx.1 hx.2 hCont)

/-- The original and every positive-time heated transform have one
common lower edge of their positive spectral support. -/
theorem exists_common_positiveFourier_lower_edge
    {f : ℝ → ℝ} (hf : Integrable f) (hfCont : Continuous f) (hf₀ : f ≠ 0)
    {s : ℝ} (hs : 0 ≤ s)
    (hGap : EqOn (𝓕 (fun x : ℝ => (f x : ℂ))) 0 (Ioo (-s) s)) :
    ∃ b : ℝ, s ≤ b ∧
      EqOn (𝓕 (fun x : ℝ => (f x : ℂ))) 0 (Ioo 0 b) ∧
      (∀ c > b, ∃ ξ ∈ Ioo b c, 𝓕 (fun x : ℝ => (f x : ℂ)) ξ ≠ 0) ∧
      ∀ t > 0, EqOn (𝓕 (fun x : ℝ => (realGaussianSmoothing t f x : ℂ))) 0 (Ioo 0 b) ∧
        (∀ c > b, ∃ ξ ∈ Ioo b c,
          𝓕 (fun x : ℝ => (realGaussianSmoothing t f x : ℂ)) ξ ≠ 0) := by
  let F : ℝ → ℂ := 𝓕 (fun x : ℝ => (f x : ℂ))
  let P := {ξ : ℝ | 0 < ξ ∧ F ξ ≠ 0}
  obtain ⟨x, hx⟩ := exists_fourierLaplaceRealDensity_horizontal_ne_zero hf hfCont hf₀ hGap
    (y := 1) zero_lt_one
  obtain ⟨ξ, hξ, hN⟩ := exists_ne_zero_of_setIntegral_ne_zero hx
  have hP : P.Nonempty := ⟨ξ, lt_of_le_of_lt hs (mem_Ioi.mp hξ),
    fun h => hN (by rw [show 𝓕 (fun x : ℝ => (f x : ℂ)) ξ = 0 from h, zero_mul])⟩
  have hLower : s ∈ lowerBounds P := by
    intro ξ hξ
    by_contra! hBad
    exact hξ.2 (hGap ⟨lt_of_le_of_lt (neg_nonpos.mpr hs) hξ.1, hBad⟩)
  have hPBelow : BddBelow P := ⟨s, hLower⟩
  let b := sInf P
  have hb : s ≤ b := le_csInf hP hLower
  have hZero : EqOn F 0 (Ioo 0 b) := by
    intro ξ hξ
    by_contra! hN
    exact (not_lt_of_ge (csInf_le hPBelow (show ξ ∈ P from ⟨hξ.1, hN⟩))) hξ.2
  have hNear (c : ℝ) (hc : b < c) : ∃ ξ ∈ Ioo b c, F ξ ≠ 0 := by
    obtain ⟨ξ, hξ, hξc⟩ := exists_lt_of_csInf_lt hP hc
    have hξb : b ≤ ξ := csInf_le hPBelow hξ
    rcases hξb.lt_or_eq with hLt | hEq
    · exact ⟨ξ, ⟨hLt, hξc⟩, hξ.2⟩
    have hFb : F b ≠ 0 := hEq ▸ hξ.2
    have hOpen : IsOpen {z : ℝ | F z ≠ 0} :=
      isOpen_ne_fun (continuous_fourier_ofReal hf) continuous_const
    have hN : ∀ᶠ z in 𝓝[>] b, F z ≠ 0 :=
      mem_nhdsWithin_of_mem_nhds (hOpen.mem_nhds hFb)
    have hInt : ∀ᶠ z in 𝓝[>] b, z ∈ Ioo b c := Ioo_mem_nhdsGT hc
    exact (hInt.and hN).exists
  refine ⟨b, hb, hZero, hNear, ?_⟩
  intro t ht
  refine ⟨fun ξ hξ => (fourier_realGaussianSmoothing_eq_zero_iff hf ht ξ).mpr (hZero hξ), ?_⟩
  intro c hc
  obtain ⟨ξ, hξ, hN⟩ := hNear c hc
  exact ⟨ξ, hξ, fun hz => hN ((fourier_realGaussianSmoothing_eq_zero_iff hf ht ξ).mp hz)⟩

private theorem setIntegral_Ioi_eq_of_eq_zero_Ioo {K : ℝ → ℂ} {s b : ℝ} (hsb : s ≤ b)
    (hK : EqOn K 0 (Ioo s b)) :
    (∫ ξ in Ioi s, K ξ) = ∫ ξ in Ioi b, K ξ := by
  have hU : Ioi s = Ioi b ∪ Ioc s b := by
    ext x
    change s < x ↔ b < x ∨ (s < x ∧ x ≤ b)
    constructor
    · intro hx
      rcases lt_or_ge b x with h | h
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
    · rintro (h | ⟨h, _⟩)
      · exact hsb.trans_lt h
      · exact h
  rw [hU]
  apply integral_union_eq_left_of_ae
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with ξ hξ
  exact hK hξ

/-- Moving the positive-frequency cutoff across a zero interval leaves
the underlying Fourier–Laplace integral unchanged. -/
theorem fourierLaplaceRealDensity_eq_of_zero_Ioo {f : ℝ → ℝ} {s b : ℝ} (hsb : s ≤ b)
    (hZero : EqOn (𝓕 (fun x : ℝ => (f x : ℂ))) 0 (Ioo s b)) :
    fourierLaplaceRealDensity f s = fourierLaplaceRealDensity f b := by
  funext z
  apply setIntegral_Ioi_eq_of_eq_zero_Ioo hsb
  intro ξ hξ
  change 𝓕 (fun x : ℝ => (f x : ℂ)) ξ * Complex.exp _ = 0
  rw [show 𝓕 (fun x : ℝ => (f x : ℂ)) ξ = 0 from hZero hξ, zero_mul]

/-- The cutoff identity uses the same zero interval at every positive
heat time. -/
theorem heatFourierLaplace_eq_of_zero_Ioo {f : ℝ → ℝ} (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) {s b : ℝ} (hsb : s ≤ b)
    (hZero : EqOn (𝓕 (fun x : ℝ => (f x : ℂ))) 0 (Ioo s b)) :
    heatFourierLaplace t f s = heatFourierLaplace t f b := by
  funext z
  apply setIntegral_Ioi_eq_of_eq_zero_Ioo hsb
  intro ξ hξ
  change 𝓕 (fun x : ℝ => (realGaussianSmoothing t f x : ℂ)) ξ * Complex.exp _ = 0
  rw [(fourier_realGaussianSmoothing_eq_zero_iff hf ht ξ).mpr (hZero hξ), zero_mul]

private theorem setIntegral_Ioi_add (K : ℝ → ℂ) (b : ℝ) :
    (∫ x in Ioi (0 : ℝ), K (x + b)) = ∫ x in Ioi b, K x := by
  calc
    _ = ∫ x : ℝ, (Ioi (0 : ℝ)).indicator (fun y => K (y + b)) x :=
      (integral_indicator measurableSet_Ioi).symm
    _ = ∫ x : ℝ, (Ioi b).indicator K (x + b) := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : 0 < x
      · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx),
          indicator_of_mem (show x + b ∈ Ioi b from by
            change b < x + b
            linarith only [hx])]
      · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx),
          indicator_of_notMem (show x + b ∉ Ioi b from by
            change ¬ b < x + b
            linarith only [le_of_not_gt hx])]
    _ = ∫ x : ℝ, (Ioi b).indicator K x :=
      integral_add_right_eq_self ((Ioi b).indicator K) b
    _ = _ := integral_indicator measurableSet_Ioi

/-- At the actual lower Fourier edge, the unheated transform on the
imaginary axis cannot have an additional positive exponential decay
rate. The density may have any complex-valued Fourier coefficients. -/
theorem frequently_fourierLaplaceRealDensity_norm_gt_edge_exp
    {f : ℝ → ℝ} (hf : Integrable f) {b : ℝ}
    (hEdge : ∀ c > b, ∃ ξ ∈ Ioo b c, 𝓕 (fun x : ℝ => (f x : ℂ)) ξ ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ y : ℝ in atTop, Real.exp (-ε * y) <
      Real.exp (2 * Real.pi * b * y) * ‖fourierLaplaceRealDensity f b ((y : ℂ) * Complex.I)‖ := by
  let F : ℝ → ℂ := 𝓕 (fun x : ℝ => (f x : ℂ))
  let P (u : ℝ) := (Real.exp (-(2 * Real.pi) * u) : ℂ) * F (u + b)
  let g := (Ioi (0 : ℝ)).indicator P
  have hP : Continuous P :=
    (show Continuous (fun u : ℝ => (Real.exp (-(2 * Real.pi) * u) : ℂ)) by fun_prop).mul
      ((continuous_fourier_ofReal hf).comp (by fun_prop))
  have hPInt : IntegrableOn P (Ioi (0 : ℝ)) := by
    refine ((integrableOn_exp_mul_Ioi (neg_neg_of_pos Real.two_pi_pos) 0).const_mul
      (∫ x : ℝ, ‖f x‖)).mono' hP.aestronglyMeasurable ?_
    filter_upwards with u
    change ‖(Real.exp (-(2 * Real.pi) * u) : ℂ) * F (u + b)‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_fourier_ofReal_le_integral_norm f (u + b)) (Real.exp_pos _).le
  have hg : Integrable g := hPInt.integrable_indicator measurableSet_Ioi
  have hEdge₀ (d : ℝ) (hd : 0 < d) : ∃ x ∈ Ioo 0 d, ContinuousAt g x ∧ g x ≠ 0 := by
    obtain ⟨ξ, hξ, hFξ⟩ := hEdge (b + d) (by linarith only [hd])
    have hx : 0 < ξ - b := sub_pos.mpr hξ.1
    have hxMem : ξ - b ∈ Ioi (0 : ℝ) := hx
    refine ⟨ξ - b, ⟨hx, by linarith only [hξ.2]⟩, ?_, ?_⟩
    · apply hP.continuousAt.congr
      filter_upwards [Ioi_mem_nhds hx] with u hu
      simp only [g, indicator_of_mem hu]
    · simp only [g, indicator_of_mem hxMem, P, sub_add_cancel]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) hFξ
  have hRep (y : ℝ) : (Real.exp (2 * Real.pi * b * y) : ℂ) *
      fourierLaplaceRealDensity f b ((y : ℂ) * Complex.I) =
      positiveLaplaceDensity g (2 * Real.pi * (y - 1)) := by
    unfold fourierLaplaceRealDensity positiveLaplaceDensity
    rw [← setIntegral_Ioi_add, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    rw [show g u = P u from indicator_of_mem hu P]
    have hE : Complex.exp ((↑(2 * Real.pi * (u + b)) * Complex.I) * ((y : ℂ) * Complex.I)) =
        (Real.exp (-(2 * Real.pi * y) * (u + b)) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      linear_combination (2 * (Real.pi : ℂ) * (u + b) * y) * Complex.I_sq
    rw [hE]
    change (Real.exp (2 * Real.pi * b * y) : ℂ) *
       (F (u + b) * (Real.exp (-(2 * Real.pi * y) * (u + b)) : ℂ)) = _
    unfold P
    rw [mul_left_comm, ← mul_assoc _ _ (F (u + b)), mul_comm _ (F (u + b))]
    simp only [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  have hFreq := frequently_positiveLaplaceDensity_norm_gt_exp hg hEdge₀
    (show 0 < ε / (2 * Real.pi) from div_pos hε Real.two_pi_pos)
  apply frequently_atTop.mpr
  intro Y
  obtain ⟨u, hu, huLower⟩ := frequently_atTop.mp hFreq ((Y - 1) * (2 * Real.pi))
  let y := 1 + u / (2 * Real.pi)
  have hU : 2 * Real.pi * (y - 1) = u := by
    dsimp [y]
    field_simp [Real.pi_ne_zero]
    ring
  have hy : Y ≤ y := by
    have hY := (le_div_iff₀ Real.two_pi_pos).2 hu
    dsimp only [y]
    linarith only [hY]
  refine ⟨y, hy, ?_⟩
  have hEq := congrArg norm (hRep y)
  rw [hU, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at hEq
  rw [hEq]
  refine (Real.exp_le_exp.mpr ?_).trans_lt huLower
  rw [← hU]
  field_simp [Real.pi_ne_zero]
  nlinarith only [hε, Real.pi_pos]

/-- Remove the Fourier edge from the argument of the heated analytic
part by modulation. On the real line the multiplier has unit modulus. -/
def edgeNormalizedHeatFourierLaplace (t : ℝ) (f : ℝ → ℝ) (b : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(↑(2 * Real.pi * b) * Complex.I) * z) * heatFourierLaplace t f b z

/-- Above the real line the normalized transform is the Stieltjes
integral of the shifted-frequency heated density. -/
theorem edgeNormalizedHeatFourierLaplace_eq_stieltjesDensity
    {f : ℝ → ℝ} (hf : Integrable f) {t : ℝ} (ht : 0 < t) (b : ℝ)
    {z : ℂ} (hz : 0 < z.im) :
    edgeNormalizedHeatFourierLaplace t f b z =
      ((↑(2 * Real.pi) : ℂ)⁻¹ * Complex.I) *
      stieltjesDensity (fun x : ℝ => Complex.exp ((↑(-(2 * Real.pi * b) * x) : ℂ) * Complex.I) *
        (realGaussianSmoothing t f x : ℂ)) z := by
  rw [edgeNormalizedHeatFourierLaplace, heatFourierLaplace_eq_cauchyIntegral hf ht b hz,
    stieltjesDensity, ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  let p : ℂ := ↑(2 * Real.pi)
  let E : ℂ := Complex.exp (-(↑(2 * Real.pi * b) * Complex.I) * z)
  let H : ℂ := Complex.exp (((p * Complex.I) * (z - x)) * b)
  have he : E * H = Complex.exp ((↑(-(2 * Real.pi * b) * x) : ℂ) * Complex.I) := by
    dsimp only [E, H, p]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  change E * ((-H / ((p * Complex.I) * (z - x))) * (realGaussianSmoothing t f x : ℂ)) = _
  rw [← he, div_eq_mul_inv, mul_inv_rev, mul_inv_rev, Complex.inv_I]
  ring

/-- Edge normalization leaves the real boundary amplitude unchanged. -/
theorem norm_edgeNormalizedHeatFourierLaplace_real
    (t : ℝ) (f : ℝ → ℝ) (b x : ℝ) :
    ‖edgeNormalizedHeatFourierLaplace t f b x‖ = ‖heatFourierLaplace t f b x‖ := by
  have hE : ‖Complex.exp (-(↑(2 * Real.pi * b) * Complex.I) * x)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im]
  rw [edgeNormalizedHeatFourierLaplace, norm_mul, hE, one_mul]

/-- Arbitrarily high imaginary centers retain a subexponential lower
bound after normalization, uniformly for sufficiently small positive
heat times at each chosen center. -/
theorem exists_large_height_eventually_edgeNormalizedHeatFourierLaplace_norm_gt_exp
    {f : ℝ → ℝ} (hf : Integrable f) {b : ℝ} (hb : 0 ≤ b)
    (hEdge : ∀ c > b, ∃ ξ ∈ Ioo b c, 𝓕 (fun x : ℝ => (f x : ℂ)) ξ ≠ 0)
    {ε : ℝ} (hε : 0 < ε) (Y : ℝ) :
    ∃ y > Y, 0 < y ∧
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), Real.exp (-ε * y) <
        ‖edgeNormalizedHeatFourierLaplace t f b ((y : ℂ) * Complex.I)‖ := by
  obtain ⟨y, hy, hLower⟩ := frequently_atTop'.mp
    (frequently_fourierLaplaceRealDensity_norm_gt_edge_exp hf hEdge hε) (max Y 0)
  have hy₀ : 0 < y := (le_max_right Y 0).trans_lt hy
  refine ⟨y, (le_max_left Y 0).trans_lt hy, hy₀, ?_⟩
  let z : ℂ := (y : ℂ) * Complex.I
  have hz : z ∈ {w : ℂ | y ≤ w.im} := by
    change y ≤ z.im
    simp [z, Complex.mul_im]
  have hPoint := (tendstoUniformlyOn_heatFourierLaplace_at_zero hf hb hy₀).tendsto_at hz
  have hValue := hPoint.norm.const_mul (Real.exp (2 * Real.pi * b * y))
  have hExp : ‖Complex.exp (-(↑(2 * Real.pi * b) * Complex.I) * z)‖ =
      Real.exp (2 * Real.pi * b * y) := by
    rw [Complex.norm_exp]
    congr 1
    simp [z, Complex.mul_re, Complex.mul_im, Complex.neg_re]
  filter_upwards [(tendsto_order.1 hValue).1 _ hLower] with t ht
  change Real.exp (-ε * y) < ‖edgeNormalizedHeatFourierLaplace t f b z‖
  rw [edgeNormalizedHeatFourierLaplace, norm_mul, hExp]
  exact ht

private theorem stieltjesDensity_add_im_re {g : ℝ → ℂ} (hg : Integrable g)
    {z : ℂ} (hz : 0 < z.im) :
    stieltjesDensity g z =
      stieltjesDensity (fun x => ((g x).re : ℂ)) z +
        Complex.I * stieltjesDensity (fun x => ((g x).im : ℂ)) z := by
  have hR : Integrable (fun x => ((g x).re : ℂ)) := by
    have h : Integrable (fun x => (g x).re) := by
      simpa only [Complex.reCLM_apply] using Complex.reCLM.integrable_comp hg
    exact h.ofReal
  have hI : Integrable (fun x => ((g x).im : ℂ)) := by
    have h : Integrable (fun x => (g x).im) := by
      simpa only [Complex.imCLM_apply] using Complex.imCLM.integrable_comp hg
    exact h.ofReal
  have hz' : 0 < |z.im| := abs_pos.mpr hz.ne'
  unfold stieltjesDensity
  rw [← integral_const_mul, ← integral_add
    (integrable_stieltjesDensity_integrand hR hz')
    ((integrable_stieltjesDensity_integrand hI hz').const_mul Complex.I)]
  apply integral_congr_ae
  filter_upwards with x
  calc
    _ = (z - x)⁻¹ * (↑(g x).re + ↑(g x).im * Complex.I) := by rw [Complex.re_add_im]
    _ = _ := by ring

private theorem norm_stieltjesDensity_ofReal (g : ℝ → ℝ) (z : ℂ) :
    ‖stieltjesDensity (fun x => (g x : ℂ)) z‖ = ‖cauchyRealDensity g z‖ := by
  have he : cauchyRealDensity g z = Complex.I * stieltjesDensity (fun x => (g x : ℂ)) z := by
    unfold cauchyRealDensity stieltjesDensity
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [div_eq_mul_inv, mul_assoc]
  rw [he, norm_mul, Complex.norm_I, one_mul]

/-- The radial half-moment bound extends to complex-valued Stieltjes
densities by applying the real Cauchy estimate to their two parts. -/
theorem circleAverage_sqrt_norm_stieltjesDensity_le {g : ℝ → ℂ} (hg : Integrable g)
    {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) :
    Real.circleAverage (fun w => Real.sqrt ‖stieltjesDensity g (cayleyToUpperHalfPlane w)‖) 0 r ≤
      4 * Real.sqrt 2 * Real.sqrt (1 + ∫ x : ℝ, ‖g x‖) := by
  let gR (x : ℝ) := (g x).re
  let gI (x : ℝ) := (g x).im
  have hR : Integrable gR := by simpa only [gR, Complex.reCLM_apply] using
    Complex.reCLM.integrable_comp hg
  have hI : Integrable gI := by simpa only [gI, Complex.imCLM_apply] using
    Complex.imCLM.integrable_comp hg
  have hMR : (∫ x : ℝ, ‖gR x‖) ≤ ∫ x : ℝ, ‖g x‖ :=
    integral_mono hR.norm hg.norm fun x => Complex.abs_re_le_norm (g x)
  have hMI : (∫ x : ℝ, ‖gI x‖) ≤ ∫ x : ℝ, ‖g x‖ :=
    integral_mono hI.norm hg.norm fun x => Complex.abs_im_le_norm (g x)
  let A (u : ℝ → ℝ) (w : ℂ) := Real.sqrt ‖cauchyRealDensity u (cayleyToUpperHalfPlane w)‖
  have hS : Metric.sphere (0 : ℂ) |r| ⊆ Metric.ball 0 1 := by
    rw [abs_of_nonneg hr]
    exact Metric.sphere_subset_closedBall.trans (Metric.closedBall_subset_ball hr₁)
  have hHeight : ∀ w ∈ Metric.ball (0 : ℂ) 1, 0 < (cayleyToUpperHalfPlane w).im := by
    intro w hw
    exact im_cayleyToUpperHalfPlane_pos (by simpa only [Metric.mem_ball, dist_zero_right] using hw)
  have hC {u : ℝ → ℝ} (hu : Integrable u) : ContinuousOn (A u) (Metric.sphere 0 |r|) :=
    (Real.continuous_sqrt.comp_continuousOn
      ((differentiableOn_cauchyRealDensity hu).comp differentiableOn_cayleyToUpperHalfPlane
        hHeight).continuousOn.norm).mono hS
  have hSt : ContinuousOn (fun w => Real.sqrt ‖stieltjesDensity g (cayleyToUpperHalfPlane w)‖)
      (Metric.sphere 0 |r|) :=
    (Real.continuous_sqrt.comp_continuousOn
      ((differentiableOn_stieltjesDensity hg).comp differentiableOn_cayleyToUpperHalfPlane
        (fun w hw => (hHeight w hw).ne')).continuousOn.norm).mono hS
  calc
    _ ≤ Real.circleAverage (fun w => A gR w + A gI w) 0 r := by
      refine Real.circleAverage_mono hSt.circleIntegrable'
        ((hC hR).add (hC hI)).circleIntegrable' fun w hw => ?_
      dsimp only [A]
      rw [stieltjesDensity_add_im_re hg (hHeight w (hS hw))]
      apply le_trans (Real.sqrt_le_sqrt (norm_add_le _ _))
      rw [norm_mul, Complex.norm_I, one_mul,
        norm_stieltjesDensity_ofReal gR, norm_stieltjesDensity_ofReal gI]
      exact sqrt_add_le_add_sqrt (norm_nonneg _) (norm_nonneg _)
    _ = Real.circleAverage (A gR) 0 r + Real.circleAverage (A gI) 0 r :=
      Real.circleAverage_fun_add (hC hR).circleIntegrable' (hC hI).circleIntegrable'
    _ ≤ _ := by
      have h₁ := (circleAverage_sqrt_norm_cauchyRealDensity_le hR hr hr₁).trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (add_le_add (le_refl _) hMR)) (by positivity))
      have h₂ := (circleAverage_sqrt_norm_cauchyRealDensity_le hI hr hr₁).trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (add_le_add (le_refl _) hMI)) (by positivity))
      have hEq : (2 * Real.sqrt 2 : ℝ) * Real.sqrt (1 + ∫ x : ℝ, ‖g x‖) +
          (2 * Real.sqrt 2 : ℝ) * Real.sqrt (1 + ∫ x : ℝ, ‖g x‖) =
          4 * Real.sqrt 2 * Real.sqrt (1 + ∫ x : ℝ, ‖g x‖) := by ring
      exact (add_le_add h₁ h₂).trans_eq hEq

end
end MeyerGeneralProblem
