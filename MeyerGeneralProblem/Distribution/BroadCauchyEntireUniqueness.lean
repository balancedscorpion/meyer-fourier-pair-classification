module

public import MeyerGeneralProblem.Distribution.BroadCauchyEntireAxis
public import MeyerGeneralProblem.Sampling.BernsteinGrowth
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Convex.Basic

@[expose] public section

/-!
# Uniqueness from exponential decay on a line

Exponential tilts and the Bernstein growth bound control all parallel
lines. A rectangular contour then identifies the exponentially
convergent Fourier integral on a half-line of frequencies.
-/

namespace MeyerGeneralProblem

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped FourierTransform Real Topology

private theorem mul_le_decay_mul_abs {s x d : ℝ} (hs : |s| ≤ d) : s * x ≤ d * |x| := by
  calc
    _ ≤ |s * x| := le_abs_self _
    _ = |s| * |x| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hs (abs_nonneg _)

private theorem entire_norm_le_exp_strip_decay {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {T C M d : ℝ} (hT : 0 ≤ T) (hC : 0 < C) (hM : 0 ≤ M) (hd : 0 < d)
    (htype : ∀ z, ‖g z‖ ≤ C * Real.exp (T * ‖z‖))
    (hreal : ∀ x : ℝ, ‖g x‖ ≤ M * Real.exp (-d * |x|)) (z : ℂ) :
    ‖g z‖ ≤ M * Real.exp ((T + d) * |z.im| - d * |z.re|) := by
  have htilt (s : ℝ) (hs : |s| ≤ d) :
      ‖g z‖ ≤ M * Real.exp ((T + d) * |z.im| - s * z.re) := by
    let G := fun w : ℂ => Complex.exp ((s : ℂ) * w) * g w
    have hG : Differentiable ℂ G := (differentiable_id.const_mul _).cexp.mul hg
    have hnorm (w : ℂ) : ‖G w‖ = Real.exp (s * w.re) * ‖g w‖ := by
      simp only [G, norm_mul, Complex.norm_exp, Complex.mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    have htype' (ε : ℝ) (hε : 0 < ε) :
        ∃ B > 0, ∀ w, ‖G w‖ ≤ B * Real.exp ((T + d + ε) * ‖w‖) := by
      refine ⟨C, hC, fun w => ?_⟩
      rw [hnorm]
      have hsr : s * w.re ≤ d * ‖w‖ :=
        (mul_le_decay_mul_abs hs).trans (mul_le_mul_of_nonneg_left
          (Complex.abs_re_le_norm w) hd.le)
      calc
        _ ≤ Real.exp (s * w.re) * (C * Real.exp (T * ‖w‖)) :=
          mul_le_mul_of_nonneg_left (htype w) (Real.exp_pos _).le
        _ = C * Real.exp (s * w.re + T * ‖w‖) := by rw [mul_left_comm, ← Real.exp_add]
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
          have he := mul_nonneg hε.le (norm_nonneg w)
          nlinarith)) hC.le
    have hreal' (x : ℝ) : ‖G x‖ ≤ M := by
      rw [hnorm, ofReal_re]
      calc
        _ ≤ Real.exp (s * x) * (M * Real.exp (-d * |x|)) :=
          mul_le_mul_of_nonneg_left (hreal x) (Real.exp_pos _).le
        _ = M * Real.exp (s * x - d * |x|) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
        _ ≤ M := mul_le_of_le_one_right hM
          (Real.exp_le_one_iff.mpr (sub_nonpos.mpr (mul_le_decay_mul_abs hs)))
    have hB := norm_entire_le_exp_abs_im hG (add_nonneg hT hd.le) hM htype' hreal' z
    rw [hnorm] at hB
    calc
      _ = (Real.exp (s * z.re) * ‖g z‖) * Real.exp (-(s * z.re)) := by
        rw [mul_comm (Real.exp (s * z.re)), mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ ≤ (M * Real.exp ((T + d) * |z.im|)) * Real.exp (-(s * z.re)) :=
        mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc, ← Real.exp_add, sub_eq_add_neg]
  by_cases hz : 0 ≤ z.re
  · rw [abs_of_nonneg hz]
    exact htilt d (by rw [abs_of_pos hd])
  · rw [abs_of_nonpos (le_of_not_ge hz)]
    have h := htilt (-d) (by rw [abs_neg, abs_of_pos hd])
    calc
      _ ≤ M * Real.exp ((T + d) * |z.im| - -d * z.re) := h
      _ = _ := by congr 2; ring

private theorem integrable_abs_pow_mul_exp_neg_abs (d : ℝ) (hd : 0 < d) (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k * Real.exp (-d * |x|)) := by
  let f (x : ℝ) := |x| ^ k * Real.exp (-d * |x|)
  have hpos : IntegrableOn f (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (k : ℝ)) (p := 1) (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg k))
      zero_lt_one hd
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [f, Real.rpow_one, Real.rpow_natCast, abs_of_pos (mem_Ioi.mp hx)]
  have hI := (integrable_indicator_iff measurableSet_Ioi).mpr hpos
  have hNeg := (LinearIsometryEquiv.neg ℝ (E := ℝ)).measurePreserving.integrable_comp_of_integrable hI
  refine (hI.add hNeg).congr ?_
  filter_upwards [(volume : Measure ℝ).ae_ne (0 : ℝ)] with x hx
  change (Ioi (0 : ℝ)).indicator f x + (Ioi (0 : ℝ)).indicator f (-x) = f x
  rcases lt_or_gt_of_ne hx with hn | hp
  · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from not_lt_of_gt hn),
      indicator_of_mem (show -x ∈ Ioi (0 : ℝ) from neg_pos.mpr hn), zero_add]
    simp only [f, abs_neg]
  · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hp),
      indicator_of_notMem (show -x ∉ Ioi (0 : ℝ) from not_lt.mpr (neg_nonpos.mpr hp.le)), add_zero]

private theorem tendsto_exp_neg_mul_atTop_zero (d : ℝ) (hd : 0 < d) :
    Tendsto (fun x : ℝ => Real.exp (-d * x)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hd))

private theorem norm_add_mul_I_plane (x y : ℝ) :
    ((x : ℂ) + (y : ℂ) * Complex.I).re = x ∧ ((x : ℂ) + (y : ℂ) * Complex.I).im = y := by
  simp only [add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im, mul_zero,
    sub_zero, add_zero, mul_one, zero_add, and_self]

private theorem integral_entire_horizontal_eq {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {M B d : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hd : 0 < d)
    (hbound : ∀ z, ‖f z‖ ≤ M * Real.exp (B * |z.im|) * Real.exp (-d * |z.re|))
    (v : ℝ) :
    (∫ x : ℝ, f (x : ℂ)) = ∫ x : ℝ, f ((x : ℂ) + (v : ℂ) * Complex.I) := by
  let J (y R : ℝ) := ∫ x : ℝ in -R..R, f ((x : ℂ) + (y : ℂ) * Complex.I)
  let V (R : ℝ) := ∫ y : ℝ in 0..v, f ((R : ℂ) + (y : ℂ) * Complex.I)
  let C := M * Real.exp (B * |v|)
  have hInt (y : ℝ) : Integrable (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * Complex.I)) := by
    have hbase : Integrable (fun x : ℝ => Real.exp (-d * |x|)) := by
      simpa only [pow_zero, one_mul] using integrable_abs_pow_mul_exp_neg_abs d hd 0
    refine (hbase.const_mul (M * Real.exp (B * |y|))).mono'
      ((hf.continuous.comp (by fun_prop : Continuous (fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I))).aestronglyMeasurable) ?_
    filter_upwards with x
    simpa only [(norm_add_mul_I_plane x y).1, (norm_add_mul_I_plane x y).2]
      using hbound ((x : ℂ) + (y : ℂ) * Complex.I)
  have hJ (y : ℝ) : Tendsto (J y) atTop (𝓝 (∫ x : ℝ, f ((x : ℂ) + (y : ℂ) * Complex.I))) :=
    intervalIntegral_tendsto_integral (hInt y) tendsto_neg_atTop_atBot tendsto_id
  have hV (R : ℝ) : ‖V R‖ ≤ C * Real.exp (-d * |R|) * |v| := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := C * Real.exp (-d * |R|)) ?_).trans_eq ?_
    · intro y hy
      have hv : |y| ≤ |v| := by
        simpa only [sub_zero] using abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hy)
      have hh := hbound ((R : ℂ) + (y : ℂ) * Complex.I)
      rw [(norm_add_mul_I_plane R y).1, (norm_add_mul_I_plane R y).2] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hv hB)) hM)
        (Real.exp_pos _).le)
    · rw [sub_zero]
  have hVlim (s : ℝ) (hs : |s| = 1) :
      Tendsto (fun R : ℝ => V (s * R)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have ht : Tendsto (fun R : ℝ => C * Real.exp (-d * R) * |v|) atTop (𝓝 0) := by
      simpa only [mul_zero, zero_mul] using
        ((tendsto_exp_neg_mul_atTop_zero d hd).const_mul C).mul_const |v|
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ ht
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    simpa only [abs_mul, hs, abs_of_nonneg hR, one_mul] using hV (s * R)
  have hRect (R : ℝ) : J 0 R - J v R + Complex.I * V R - Complex.I * V (-R) = 0 := by
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f (-(R : ℂ))
      ((R : ℂ) + (v : ℂ) * Complex.I) hf.differentiableOn
    simpa only [J, V, neg_im, ofReal_im, neg_zero, neg_re, ofReal_re, smul_eq_mul,
      (norm_add_mul_I_plane R v).1, (norm_add_mul_I_plane R v).2] using h
  have hVr : Tendsto V atTop (𝓝 0) := by simpa only [one_mul] using hVlim 1 abs_one
  have hVl : Tendsto (fun R : ℝ => V (-R)) atTop (𝓝 0) := by
    simpa only [neg_mul, one_mul] using hVlim (-1) (by norm_num)
  have hlim : Tendsto (fun R => J 0 R - J v R + Complex.I * V R - Complex.I * V (-R)) atTop
      (𝓝 ((∫ x : ℝ, f (x : ℂ)) - ∫ x : ℝ, f ((x : ℂ) + (v : ℂ) * Complex.I))) := by
    simpa only [ofReal_zero, zero_mul, mul_zero, add_zero, sub_zero] using
      (((hJ 0).sub (hJ v)).add (hVr.const_mul Complex.I)).sub (hVl.const_mul Complex.I)
  have hz : Tendsto (fun R => J 0 R - J v R + Complex.I * V R - Complex.I * V (-R)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (Eventually.of_forall fun R => (hRect R).symm)
  exact sub_eq_zero.mp (tendsto_nhds_unique hlim hz)

private def entireFourierLaplace (g : ℂ → ℂ) (w : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-Complex.I * w * (x : ℂ)) * g (x : ℂ)

private theorem norm_fourier_exp_mul (ω : ℝ) (z : ℂ) :
    ‖Complex.exp (-Complex.I * (ω : ℂ) * z)‖ = Real.exp (ω * z.im) := by
  simp only [Complex.norm_exp, mul_re, mul_im, neg_re, I_re, I_im, ofReal_re, ofReal_im,
    zero_mul, sub_zero, mul_zero, zero_add, zero_sub, neg_neg, neg_mul, one_mul]

private theorem entireFourierLaplace_eq_zero_of_lt
    {g : ℂ → ℂ} (hg : Differentiable ℂ g) {A M d : ℝ}
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hd : 0 < d)
    (hbound : ∀ z, ‖g z‖ ≤ M * Real.exp (A * |z.im| - d * |z.re|))
    (ω : ℝ) (hω : A < ω) :
    entireFourierLaplace g (ω : ℂ) = 0 := by
  let f (z : ℂ) := Complex.exp (-Complex.I * (ω : ℂ) * z) * g z
  have hf : Differentiable ℂ f :=
    ((differentiable_id.const_mul (-Complex.I * (ω : ℂ))).cexp).mul hg
  have hnorm (z : ℂ) : ‖f z‖ ≤ M * Real.exp (A * |z.im| + ω * z.im) * Real.exp (-d * |z.re|) := by
    dsimp only [f]
    rw [norm_mul, norm_fourier_exp_mul]
    calc
      _ ≤ Real.exp (ω * z.im) * (M * Real.exp (A * |z.im| - d * |z.re|)) :=
        mul_le_mul_of_nonneg_left (hbound z) (Real.exp_pos _).le
      _ = _ := by rw [sub_eq_add_neg, Real.exp_add, Real.exp_add]; ring
  have hwide (z : ℂ) : ‖f z‖ ≤ M * Real.exp ((A + |ω|) * |z.im|) * Real.exp (-d * |z.re|) := by
    apply (hnorm z).trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_left _ hM
    rw [add_mul]
    exact Real.exp_le_exp.mpr (add_le_add_right (mul_le_decay_mul_abs (le_refl |ω|)) _)
  have hshift (v : ℝ) : entireFourierLaplace g (ω : ℂ) =
      ∫ x : ℝ, f ((x : ℂ) + (v : ℂ) * Complex.I) :=
    integral_entire_horizontal_eq hf hM (add_nonneg hA (abs_nonneg ω)) hd hwide v
  have hInt : Integrable (fun x : ℝ => Real.exp (-d * |x|)) := by
    simpa only [pow_zero, one_mul] using integrable_abs_pow_mul_exp_neg_abs d hd 0
  let C := ∫ x : ℝ, Real.exp (-d * |x|)
  have hlim : Tendsto (fun y : ℝ => M * Real.exp (-(ω - A) * y) * C) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      ((tendsto_exp_neg_mul_atTop_zero (ω - A) (sub_pos.mpr hω)).const_mul M).mul_const C
  apply norm_eq_zero.mp
  refine le_antisymm (ge_of_tendsto hlim ?_) (norm_nonneg _)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  rw [hshift (-y)]
  have hbound' (x : ℝ) : ‖f ((x : ℂ) + ((-y : ℝ) : ℂ) * Complex.I)‖ ≤
      (M * Real.exp (-(ω - A) * y)) * Real.exp (-d * |x|) := by
    have h := hnorm ((x : ℂ) + ((-y : ℝ) : ℂ) * Complex.I)
    rw [(norm_add_mul_I_plane x (-y)).1, (norm_add_mul_I_plane x (-y)).2, abs_neg, abs_of_nonneg hy] at h
    exact h.trans_eq (by congr 3; ring)
  exact (norm_integral_le_of_norm_le (hInt.const_mul _) (Eventually.of_forall hbound')).trans_eq
    (by rw [integral_const_mul])

private theorem norm_fourier_exp_apply_real (w : ℂ) (x : ℝ) :
    ‖Complex.exp (-Complex.I * w * (x : ℂ))‖ = Real.exp (w.im * x) := by
  simp only [Complex.norm_exp, mul_re, mul_im, neg_re, I_re, I_im, ofReal_re, ofReal_im,
    zero_mul, sub_zero, mul_zero, zero_add, zero_sub, neg_neg, neg_mul, one_mul]

private theorem analyticOnNhd_entireFourierLaplace {g : ℂ → ℂ}
    (hg : Continuous g) {M d : ℝ}
    (hreal : ∀ x : ℝ, ‖g (x : ℂ)‖ ≤ M * Real.exp (-d * |x|)) :
    AnalyticOnNhd ℂ (entireFourierLaplace g) {w : ℂ | |w.im| < d} := by
  have hopen : IsOpen {w : ℂ | |w.im| < d} := isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  apply DifferentiableOn.analyticOnNhd _ hopen
  intro z hz
  let e := (d + |z.im|) / 2
  have he : |z.im| < e := by dsimp [e]; linarith [show |z.im| < d from hz]
  have hed : 0 < d - e := by dsimp [e]; linarith [show |z.im| < d from hz]
  let S := {w : ℂ | |w.im| < e}
  have hS : S ∈ 𝓝 z := (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const).mem_nhds he
  let F (w : ℂ) (x : ℝ) := Complex.exp (-Complex.I * w * (x : ℂ)) * g x
  let F' (w : ℂ) (x : ℝ) := (Complex.exp (-Complex.I * w * (x : ℂ)) * (-Complex.I * (x : ℂ))) * g x
  have hF (w : ℂ) : AEStronglyMeasurable (F w) volume := by
    apply Continuous.aestronglyMeasurable
    exact (show Continuous (fun x : ℝ => Complex.exp (-Complex.I * w * (x : ℂ))) by fun_prop).mul
      (hg.comp Complex.continuous_ofReal)
  have hF' (w : ℂ) : AEStronglyMeasurable (F' w) volume := by
    apply Continuous.aestronglyMeasurable
    exact ((show Continuous (fun x : ℝ => Complex.exp (-Complex.I * w * (x : ℂ))) by fun_prop).mul
      (continuous_const.mul Complex.continuous_ofReal)).mul (hg.comp Complex.continuous_ofReal)
  have hbound (w : ℂ) (hw : w ∈ S) (x : ℝ) : ‖F w x‖ ≤ M * Real.exp (-(d - e) * |x|) := by
    have hm := mul_le_decay_mul_abs (show |w.im| ≤ e from (show |w.im| < e from hw).le) (x := x)
    change ‖Complex.exp (-Complex.I * w * (x : ℂ)) * g x‖ ≤ _
    rw [norm_mul, norm_fourier_exp_apply_real]
    calc
      _ ≤ Real.exp (e * |x|) * (M * Real.exp (-d * |x|)) :=
        mul_le_mul (Real.exp_le_exp.mpr hm) (hreal x) (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hInt : Integrable (F z) := by
    have h : Integrable (fun x : ℝ => Real.exp (-(d - e) * |x|)) := by
      simpa only [pow_zero, one_mul] using integrable_abs_pow_mul_exp_neg_abs (d - e) hed 0
    exact (h.const_mul M).mono' (hF z) (Eventually.of_forall (hbound z he))
  have hD (w : ℂ) (hw : w ∈ S) (x : ℝ) :
      ‖F' w x‖ ≤ M * (|x| ^ (1 : ℕ) * Real.exp (-(d - e) * |x|)) := by
    have hnx : ‖-Complex.I * (x : ℂ)‖ = |x| := by
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    change ‖(Complex.exp (-Complex.I * w * (x : ℂ)) * (-Complex.I * (x : ℂ))) * g x‖ ≤ _
    calc
      _ = |x| * ‖F w x‖ := by
        simp only [F, norm_mul, hnx]
        ring
      _ ≤ |x| * (M * Real.exp (-(d - e) * |x|)) :=
        mul_le_mul_of_nonneg_left (hbound w hw x) (abs_nonneg _)
      _ = _ := by rw [pow_one]; ring
  have hDer (x : ℝ) (w : ℂ) : HasDerivAt (fun v => F v x) (F' w x) w := by
    have hlin (v : ℂ) : -Complex.I * v * (x : ℂ) = (-Complex.I * (x : ℂ)) * v := by ring
    simp only [F, F', hlin]
    simpa only [mul_one] using (((hasDerivAt_id' w).const_mul (-Complex.I * (x : ℂ))).cexp).mul_const (g x)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') hS (Eventually.of_forall hF) hInt (hF' z)
    (Eventually.of_forall fun x w hw => hD w hw x)
    ((integrable_abs_pow_mul_exp_neg_abs (d - e) hed 1).const_mul M)
    (Eventually.of_forall fun x w _ => hDer x w)
  exact h.2.differentiableAt.differentiableWithinAt

private theorem analytic_eqOn_zero_of_zero_real_ray {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U)
    (a : ℝ) (ha : (a : ℂ) ∈ U) (hz : ∀ x : ℝ, a < x → f (x : ℂ) = 0) :
    EqOn f 0 U := by
  refine hf.eqOn_zero_of_preconnected_of_mem_closure hU ha (Metric.mem_closure_iff.mpr ?_)
  intro ε hε
  let b := a + ε / 2
  have hab : a < b := lt_add_of_pos_right a (half_pos hε)
  refine ⟨(b : ℂ), ⟨hz b hab, ?_⟩, ?_⟩
  · exact fun h => hab.ne (Complex.ofReal_injective (mem_singleton_iff.mp h)).symm
  · rw [dist_eq_norm, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr hab.le)]
    dsimp only [b]
    linarith

/-- An entire function with a finite radial exponential bound and
two-sided exponential decay on the real line is identically zero. -/
theorem entire_eq_zero_of_radial_exp_bound_and_real_exp_decay
    {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {T C M d : ℝ} (hT : 0 ≤ T) (hC : 0 < C) (hM : 0 ≤ M) (hd : 0 < d)
    (htype : ∀ z, ‖g z‖ ≤ C * Real.exp (T * ‖z‖))
    (hreal : ∀ x : ℝ, ‖g (x : ℂ)‖ ≤ M * Real.exp (-d * |x|)) : g = 0 := by
  let U := {w : ℂ | |w.im| < d}
  have hU : IsPreconnected U := by
    have he : U = Complex.imCLM ⁻¹' Ioo (-d) d := by
      ext w
      change |w.im| < d ↔ -d < w.im ∧ w.im < d
      exact abs_lt
    rw [he]
    exact ((convex_Ioo (𝕜 := ℝ) (-d) d).linear_preimage Complex.imCLM.toLinearMap).isPreconnected
  have hUreal (x : ℝ) : (x : ℂ) ∈ U := by simpa only [U, mem_ofPred_eq, ofReal_im, abs_zero] using hd
  have hA : 0 ≤ T + d := add_nonneg hT hd.le
  have hL : EqOn (entireFourierLaplace g) 0 U :=
    analytic_eqOn_zero_of_zero_real_ray (analyticOnNhd_entireFourierLaplace hg.continuous hreal)
      hU (T + d) (hUreal _) (fun x hx => entireFourierLaplace_eq_zero_of_lt hg hA hM hd
        (entire_norm_le_exp_strip_decay hg hT hC hM hd htype hreal) x hx)
  let f : ℝ → ℂ := fun x => g (x : ℂ)
  have hcont : Continuous f := hg.continuous.comp Complex.continuous_ofReal
  have hint : Integrable f := by
    have hbase : Integrable (fun x : ℝ => Real.exp (-d * |x|)) := by
      simpa only [pow_zero, one_mul] using integrable_abs_pow_mul_exp_neg_abs d hd 0
    exact (hbase.const_mul M).mono' hcont.aestronglyMeasurable (Eventually.of_forall hreal)
  have hFourier (ξ : ℝ) : (𝓕 f) ξ = entireFourierLaplace g ((2 * Real.pi * ξ : ℝ) : ℂ) := by
    rw [Real.fourier_real_eq_integral_exp_smul, entireFourierLaplace]
    apply integral_congr_ae
    filter_upwards with x
    simp only [smul_eq_mul, f]
    congr 2
    push_cast
    ring
  have hFourierZero : 𝓕 f = 0 :=
    funext fun ξ => (hFourier ξ).trans (hL (hUreal _))
  have hFin : Integrable (𝓕 f) := hFourierZero ▸ integrable_zero _ _ _
  have hfzero : f = 0 := by
    rw [← hcont.fourierInv_fourier_eq hint hFin, hFourierZero]
    funext t
    simp [Real.fourierInv_eq]
  have hgz (x : ℝ) : g (x : ℂ) = 0 := congrFun hfzero x
  exact funext fun z => analytic_eqOn_zero_of_zero_real_ray
    (hg.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ 0 (mem_univ _)
    (fun x _ => hgz x) (mem_univ z)

private theorem exists_radial_exp_bound_of_polynomial_bound {F : ℂ → ℂ}
    (q : ℕ) (A L b : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L) (hb : 0 ≤ b)
    (hg : ∀ z, ‖F z‖ ≤ A * (3 + ‖z‖) ^ q *
      Real.exp (b * (‖z‖ + 2) + L * Real.log (4 + ‖z‖))) :
    ∃ T ≥ 0, ∃ C > 0, ∀ z, ‖F z‖ ≤ C * Real.exp (T * ‖z‖) := by
  let T := b + L + (q : ℝ)
  let C := (A + 1) * Real.exp (2 * b + 4 * L + 3 * (q : ℝ))
  refine ⟨T, by dsimp [T]; positivity, C, by dsimp [C]; positivity, fun z => ?_⟩
  let r := ‖z‖
  have hr : 0 ≤ r := norm_nonneg _
  have hlog : Real.log (4 + r) ≤ 4 + r :=
    (Real.log_le_sub_one_of_pos (by positivity : 0 < 4 + r)).trans (by linarith)
  have hp : (3 + r) ^ q ≤ Real.exp ((q : ℝ) * (3 + r)) := by
    rw [Real.exp_nat_mul]
    have he := Real.add_one_le_exp (3 + r)
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hexp : Real.exp (b * (r + 2) + L * Real.log (4 + r)) ≤
      Real.exp (b * (r + 2) + L * (4 + r)) :=
    Real.exp_le_exp.mpr (add_le_add_right (mul_le_mul_of_nonneg_left hlog hL) _)
  calc
    _ ≤ A * (3 + r) ^ q * Real.exp (b * (r + 2) + L * Real.log (4 + r)) := hg z
    _ ≤ (A + 1) * Real.exp ((q : ℝ) * (3 + r)) * Real.exp (b * (r + 2) + L * (4 + r)) :=
      mul_le_mul (mul_le_mul (le_add_of_nonneg_right zero_le_one) hp
        (by positivity) (by positivity)) hexp (Real.exp_pos _).le (by positivity)
    _ = C * Real.exp (T * r) := by
      have he : (q : ℝ) * (3 + r) + (b * (r + 2) + L * (4 + r)) =
          (2 * b + 4 * L + 3 * (q : ℝ)) + T * r := by dsimp only [T]; ring
      rw [mul_assoc, ← Real.exp_add, he, Real.exp_add]
      exact (mul_assoc _ _ _).symm

private theorem exists_norm_exp_neg_abs_of_axis_weighted_limit {F : ℂ → ℂ}
    (hF : Continuous F) {d : ℝ}
    (haxis : Tendsto (fun y : ℝ =>
      (‖F ((y : ℂ) * Complex.I)‖ + ‖F (-((y : ℂ) * Complex.I))‖) * Real.exp (d * y))
      atTop (𝓝 0)) :
    ∃ M ≥ 0, ∀ x : ℝ, ‖F ((x : ℂ) * Complex.I)‖ ≤ M * Real.exp (-d * |x|) := by
  let f (x : ℝ) := ‖F ((x : ℂ) * Complex.I)‖ * Real.exp (d * |x|)
  have hcont : Continuous f := (hF.comp (Complex.continuous_ofReal.mul continuous_const)).norm.mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs))
  obtain ⟨R, hR⟩ := eventually_atTop.mp (haxis.eventually_lt_const zero_lt_one)
  let R' := max 1 R
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R') (b := R')).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max 1 M, zero_le_one.trans (le_max_left _ _), fun x => ?_⟩
  have hx : f x ≤ max 1 M := by
    by_cases hx : |x| ≤ R'
    · have hMx : |f x| ≤ M := by simpa only [Real.norm_eq_abs] using hM x (abs_le.mp hx)
      exact (le_abs_self (f x)).trans (hMx.trans (le_max_right _ _))
    · apply le_trans _ (le_max_left _ _)
      have hc := (hR |x| ((le_max_right (1 : ℝ) R).trans (le_of_not_ge hx))).le
      refine le_trans ?_ hc
      dsimp only [f]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      by_cases hx₀ : 0 ≤ x
      · rw [abs_of_nonneg hx₀]
        exact le_add_of_nonneg_right (norm_nonneg _)
      · rw [abs_of_nonpos (le_of_not_ge hx₀), ofReal_neg, neg_mul, neg_neg]
        exact le_add_of_nonneg_left (norm_nonneg _)
  calc
    _ = f x * Real.exp (-d * |x|) := by
      dsimp only [f]
      rw [mul_assoc, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le

/-- Rotation reduces two-ray imaginary-axis decay to the Fourier
uniqueness theorem on the real axis. -/
theorem entire_eq_zero_of_polynomial_radial_bound_and_imaginary_exp_decay
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (q : ℕ) (A L b : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L) (hb : 0 ≤ b)
    (hg : ∀ z, ‖F z‖ ≤ A * (3 + ‖z‖) ^ q *
      Real.exp (b * (‖z‖ + 2) + L * Real.log (4 + ‖z‖)))
    (d : ℝ) (hd : 0 < d)
    (haxis : Tendsto (fun y : ℝ =>
      (‖F ((y : ℂ) * Complex.I)‖ + ‖F (-((y : ℂ) * Complex.I))‖) * Real.exp (d * y))
      atTop (𝓝 0)) : F = 0 := by
  obtain ⟨T, hT, C, hC, htype⟩ := exists_radial_exp_bound_of_polynomial_bound q A L b hA hL hb hg
  obtain ⟨M, hM, hreal⟩ := exists_norm_exp_neg_abs_of_axis_weighted_limit hF.continuous haxis
  let g (z : ℂ) := F (z * Complex.I)
  have hg' : Differentiable ℂ g := hF.comp (differentiable_id.mul_const _)
  have htype' (z : ℂ) : ‖g z‖ ≤ C * Real.exp (T * ‖z‖) := by
    simpa only [g, norm_mul, Complex.norm_I, mul_one] using htype (z * Complex.I)
  have hzero : g = 0 :=
    entire_eq_zero_of_radial_exp_bound_and_real_exp_decay hg' hT hC hM hd htype' hreal
  funext z
  have h := congrFun hzero (z * -Complex.I)
  have he : z * -Complex.I * Complex.I = z := by
    rw [mul_assoc, neg_mul, ← pow_two, Complex.I_sq, neg_neg, mul_one]
  simpa only [g, he, Pi.zero_apply] using h

end

end MeyerGeneralProblem
