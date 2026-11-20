module

public import MeyerGeneralProblem.Distribution.DiskBoundaryUniqueness

@[expose] public section

/-!
# Half-line support and an open Fourier gap

For a density supported to the left of a cutoff, damping by the
imaginary part gives a bounded holomorphic Fourier–Laplace transform.
An open real Fourier gap would give a vanishing boundary arc of that
transform.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Metric Set
open scoped FourierTransform Topology

private def halfLineFourierLaplaceIntegrand (f : ℝ → ℂ) (a : ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  f x * Complex.exp (((↑(2 * Real.pi * (a - x)) : ℂ) * Complex.I) * z)

private def halfLineFourierLaplace (f : ℝ → ℂ) (a : ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, halfLineFourierLaplaceIntegrand f a z x

private theorem norm_halfLineFourierLaplaceIntegrand (f : ℝ → ℂ) (a : ℝ) (z : ℂ) (x : ℝ) :
    ‖halfLineFourierLaplaceIntegrand f a z x‖ =
      ‖f x‖ * Real.exp (-(2 * Real.pi * (a - x)) * z.im) := by
  rw [halfLineFourierLaplaceIntegrand, norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, zero_sub, add_zero, neg_zero,
    neg_mul]

private theorem norm_halfLineFourierLaplaceIntegrand_le {f : ℝ → ℂ} {a : ℝ}
    (hZero : ∀ x > a, f x = 0) {z : ℂ} (hz : 0 ≤ z.im) (x : ℝ) :
    ‖halfLineFourierLaplaceIntegrand f a z x‖ ≤ ‖f x‖ := by
  rw [norm_halfLineFourierLaplaceIntegrand]
  rcases le_or_gt x a with hx | hx
  · refine mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr ?_)
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (mul_nonneg Real.two_pi_pos.le (sub_nonneg.mpr hx))) hz
  · simp [hZero x hx]

private theorem continuousOn_halfLineFourierLaplace {f : ℝ → ℂ}
    (hf : Continuous f) (hInt : Integrable f) {a : ℝ} (hZero : ∀ x > a, f x = 0) :
    ContinuousOn (halfLineFourierLaplace f a) {z : ℂ | 0 ≤ z.im} := by
  apply continuousOn_of_dominated (bound := fun x => ‖f x‖)
  · intro z _
    unfold halfLineFourierLaplaceIntegrand
    exact (show Continuous _ from hf.mul (by fun_prop)).aestronglyMeasurable
  · exact fun z hz => ae_of_all _ (norm_halfLineFourierLaplaceIntegrand_le hZero hz)
  · exact hInt.norm
  · exact ae_of_all _ fun x => (show Continuous
      (fun z => halfLineFourierLaplaceIntegrand f a z x) by
      unfold halfLineFourierLaplaceIntegrand
      fun_prop).continuousOn

private theorem differentiableOn_halfLineFourierLaplace {f : ℝ → ℂ}
    (hf : Continuous f) (hInt : Integrable f) {a : ℝ} (hZero : ∀ x > a, f x = 0) :
    DifferentiableOn ℂ (halfLineFourierLaplace f a) {z : ℂ | 0 < z.im} := by
  intro z hz
  change 0 < z.im at hz
  let δ := z.im / 2
  have hδ : 0 < δ := half_pos hz
  let t (x : ℝ) := 2 * Real.pi * (a - x)
  let C (x : ℝ) := (t x : ℂ) * Complex.I
  let K := halfLineFourierLaplaceIntegrand f a
  let L (w : ℂ) (x : ℝ) := K w x * C x
  have hNear : ∀ᶠ w : ℂ in 𝓝 z, w ∈ {w : ℂ | δ < w.im} :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (half_lt_self hz)
  have hMeas (w : ℂ) : AEStronglyMeasurable (K w) := by
    change AEStronglyMeasurable (fun x =>
      f x * Complex.exp (((↑(2 * Real.pi * (a - x)) : ℂ) * Complex.I) * w))
    exact (hf.mul (by fun_prop)).aestronglyMeasurable
  have hNorm (w : ℂ) (hw : w ∈ {w : ℂ | δ < w.im}) (x : ℝ) :
      ‖L w x‖ ≤ δ⁻¹ * ‖f x‖ := by
    change δ < w.im at hw
    change ‖halfLineFourierLaplaceIntegrand f a w x * C x‖ ≤ _
    rw [norm_mul, norm_halfLineFourierLaplaceIntegrand]
    change ‖f x‖ * Real.exp (-t x * w.im) * ‖C x‖ ≤ _
    rcases le_or_gt x a with hx | hx
    · have ht : 0 ≤ t x := mul_nonneg Real.two_pi_pos.le (sub_nonneg.mpr hx)
      have hC : ‖C x‖ = t x := by
        simp only [C, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht, Complex.norm_I, mul_one]
      have hExp : Real.exp (-t x * w.im) ≤ Real.exp (-(δ * t x)) := by
        apply Real.exp_le_exp.mpr
        linarith only [mul_le_mul_of_nonneg_right hw.le ht]
      have hScale : t x * Real.exp (-(δ * t x)) ≤ δ⁻¹ := by
        rw [← one_div, le_div_iff₀ hδ]
        calc
          _ = (δ * t x) * Real.exp (-(δ * t x)) := by ring
          _ ≤ 1 := (Real.mul_exp_neg_le_exp_neg_one _).trans
            (Real.exp_le_one_iff.mpr (by norm_num))
      rw [hC, mul_assoc, mul_comm δ⁻¹]
      exact mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_right hExp ht).trans (by simpa only [mul_comm] using hScale))
        (norm_nonneg _)
    · simp [hZero x hx]
  have hKInt : Integrable (K z) := hInt.norm.mono' (hMeas z)
    (ae_of_all _ (norm_halfLineFourierLaplaceIntegrand_le hZero hz.le))
  have hLMeas : AEStronglyMeasurable (L z) :=
    (hMeas z).mul (show Continuous C by unfold C t; fun_prop).aestronglyMeasurable
  have hDeriv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hNear
    (Eventually.of_forall hMeas) hKInt hLMeas (ae_of_all _ fun x w hw => hNorm w hw x)
    (hInt.norm.const_mul δ⁻¹)
    (ae_of_all _ fun x w _ => by
      simpa only [L, K, halfLineFourierLaplaceIntegrand, C, t, mul_assoc, id_eq, mul_one] using
        (((hasDerivAt_id w).const_mul (C x)).cexp.const_mul (f x)))).2
  exact hDeriv.differentiableAt.differentiableWithinAt

private theorem halfLineFourierLaplace_ofReal (f : ℝ → ℂ) (a ξ : ℝ) :
    halfLineFourierLaplace f a (ξ : ℂ) =
      Complex.exp (↑(2 * Real.pi * a * ξ) * Complex.I) * 𝓕 f ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  unfold halfLineFourierLaplace
  congr 1
  funext x
  have h :
      ((↑(2 * Real.pi * (a - x)) : ℂ) * Complex.I) * (ξ : ℂ) =
        ↑(2 * Real.pi * a * ξ) * Complex.I + ↑(-2 * Real.pi * x * ξ) * Complex.I := by
    push_cast
    ring
  rw [halfLineFourierLaplaceIntegrand, h, Complex.exp_add, smul_eq_mul]
  ring

/-- A nonzero continuous integrable function with a centered open
Fourier gap has nonzero values arbitrarily far to the right. -/
theorem exists_nonzero_to_right_of_fourier_gap {f : ℝ → ℂ} (hf : Continuous f)
    (hInt : Integrable f) (hf₀ : f ≠ 0) {s : ℝ} (hs : 0 < s)
    (hGap : EqOn (𝓕 f) 0 (Ioo (-s) s)) (a : ℝ) :
    ∃ x > a, f x ≠ 0 := by
  by_contra! hZero
  let P := halfLineFourierLaplace f a
  let H := {z : ℂ | 0 ≤ z.im}
  have hCont : ContinuousOn P H := continuousOn_halfLineFourierLaplace hf hInt hZero
  have hHol := differentiableOn_halfLineFourierLaplace hf hInt hZero
  have hBound (z : ℂ) (hz : z ∈ H) : ‖P z‖ ≤ ∫ x : ℝ, ‖f x‖ := by
    refine norm_integral_le_of_norm_le hInt.norm ?_
    exact ae_of_all _ (norm_halfLineFourierLaplaceIntegrand_le hZero hz)
  have hNonzero : ∃ ξ : ℝ, 𝓕 f ξ ≠ 0 := by
    by_contra! h
    have he : 𝓕 f = 0 := funext h
    have hI : Integrable (𝓕 f) := by rw [he]; exact integrable_zero _ _ _
    have hInv := hf.fourierInv_fourier_eq hInt hI
    have hInvZero : 𝓕⁻ (0 : ℝ → ℂ) = 0 := by
      funext ξ
      rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
      simp
    rw [he, hInvZero] at hInv
    exact hf₀ hInv.symm
  obtain ⟨x₀, hx₀⟩ := hNonzero
  have hP₀ : P (x₀ : ℂ) ≠ 0 := by
    rw [show P (x₀ : ℂ) = _ from halfLineFourierLaplace_ofReal f a x₀]
    exact mul_ne_zero (Complex.exp_ne_zero _) hx₀
  let v (y : ℝ) := (x₀ : ℂ) + (y : ℂ) * Complex.I
  have hv (y : ℝ) : (v y).im = y := by
    simp [v, Complex.add_im, Complex.mul_im]
  have hv₀ : v 0 = (x₀ : ℂ) := by simp [v]
  have hvCont : Continuous v := by unfold v; fun_prop
  have hvMaps : MapsTo v (Ioi (0 : ℝ)) H := fun y hy => by
    change 0 ≤ (v y).im
    rw [hv]
    exact (mem_Ioi.mp hy).le
  have hLim : Tendsto (fun y => P (v y)) (𝓝[>] (0 : ℝ)) (𝓝 (P (x₀ : ℂ))) := by
    have hh : v 0 ∈ H := by rw [hv₀]; simp [H]
    change Tendsto (P ∘ v) (𝓝[>] (0 : ℝ)) (𝓝 (P (x₀ : ℂ)))
    rw [← hv₀]
    exact ((hCont (v 0) hh).comp hvCont.continuousWithinAt hvMaps).tendsto
  have hSome : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), 0 < y ∧ P (v y) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin,
      hLim.eventually (isClosed_singleton.isOpen_compl.mem_nhds hP₀)] with y hy hPy
    exact ⟨hy, hPy⟩
  obtain ⟨y₀, hy₀, hPy₀⟩ := hSome.exists
  let Q (w : ℂ) := (x₀ : ℂ) + (y₀ : ℂ) * cayleyToUpperHalfPlane w
  have hQim (w : ℂ) : (Q w).im = y₀ * (cayleyToUpperHalfPlane w).im := by
    simp [Q, Complex.add_im, Complex.mul_im]
  have hQmaps : MapsTo Q (ball 0 1) {z : ℂ | 0 < z.im} := by
    intro w hw
    change 0 < (Q w).im
    rw [hQim]
    exact mul_pos hy₀ (im_cayleyToUpperHalfPlane_pos (mem_ball_zero_iff.mp hw))
  have hQhol : DifferentiableOn ℂ Q (ball 0 1) := by
    unfold Q
    exact DifferentiableOn.add (by fun_prop)
      (DifferentiableOn.mul (by fun_prop) differentiableOn_cayleyToUpperHalfPlane)
  have hFhol : DifferentiableOn ℂ (P ∘ Q) (ball 0 1) := hHol.comp hQhol hQmaps
  have hF₀ : (P ∘ Q) 0 ≠ 0 := by
    have hQ₀ : Q 0 = v y₀ := by simp [Q, v, cayleyToUpperHalfPlane]
    simpa only [Function.comp_apply, hQ₀] using hPy₀
  let θ₀ := cayleyBoundaryAngle (-x₀ / y₀)
  have hθ₀ : θ₀ ∈ Ioo 0 (2 * Real.pi) := by
    obtain ⟨hl, hu⟩ := Real.arctan_mem_Ioo (-x₀ / y₀)
    dsimp [θ₀, cayleyBoundaryAngle]
    exact ⟨by linarith only [hl], by linarith only [hu]⟩
  have hQroot : Q (circleMap 0 1 θ₀) = 0 := by
    dsimp only [Q, θ₀]
    rw [cayleyToUpperHalfPlane_circleMap_cayleyBoundaryAngle]
    push_cast
    field_simp [hy₀.ne']
    ring
  have hCayleyCont {w : ℂ} (hw : w ≠ 1) : ContinuousAt Q w :=
    continuousAt_const.add (continuousAt_const.mul
      (analyticAt_cayleyToUpperHalfPlane hw).continuousAt)
  have hArcCont : ContinuousAt (fun θ : ℝ => (Q (circleMap 0 1 θ)).re) θ₀ :=
    Complex.continuous_re.continuousAt.comp
      ((hCayleyCont (circleMap_unit_ne_one hθ₀)).comp (continuous_circleMap 0 1).continuousAt)
  have hArc : {θ : ℝ | θ ∈ Ioo 0 (2 * Real.pi) ∧ (Q (circleMap 0 1 θ)).re ∈ Ioo (-s) s}
      ∈ 𝓝 θ₀ := by
    apply inter_mem (Ioo_mem_nhds hθ₀.1 hθ₀.2)
    have hNear : Ioo (-s) s ∈ 𝓝 (Q (circleMap 0 1 θ₀)).re := by
      rw [hQroot, Complex.zero_re]
      exact Ioo_mem_nhds (neg_lt_zero.mpr hs) hs
    exact hArcCont.tendsto.eventually hNear
  obtain ⟨δ, hδ, hδArc⟩ := Metric.mem_nhds_iff.mp hArc
  let ε := min (δ / 2) (min (θ₀ / 2) ((2 * Real.pi - θ₀) / 2))
  have hε : 0 < ε :=
    lt_min (half_pos hδ) (lt_min (half_pos hθ₀.1) (half_pos (sub_pos.mpr hθ₀.2)))
  have hεle : ε ≤ δ / 2 := min_le_left _ _
  have hLeft : 0 ≤ θ₀ - ε := by
    have h := (min_le_right (δ / 2) _).trans
      (min_le_left (θ₀ / 2) ((2 * Real.pi - θ₀) / 2))
    linarith only [h, hθ₀.1]
  have hRight : θ₀ + ε ≤ 2 * Real.pi := by
    have h := (min_le_right (δ / 2) _).trans
      (min_le_right (θ₀ / 2) ((2 * Real.pi - θ₀) / 2))
    linarith only [h, hθ₀.2]
  have hFBound (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) : ‖(P ∘ Q) w‖ ≤ ∫ x : ℝ, ‖f x‖ := by
    apply hBound
    change 0 ≤ (Q w).im
    exact (show 0 < (Q w).im from hQmaps hw).le
  apply not_radial_zero_on_interval_of_bounded_diskFunction hFhol hF₀ hFBound hLeft hRight
    (show θ₀ - ε < θ₀ + ε by linarith only [hε])
  intro θ hθ
  have hδθ : θ ∈ ball θ₀ δ := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith only [hθ.1, hεle, hδ], by linarith only [hθ.2, hεle, hδ]⟩
  obtain ⟨hθrange, hθgap⟩ := hδArc hδθ
  let z := Q (circleMap 0 1 θ)
  have hzim : z.im = 0 := by
    simp [z, hQim, im_cayleyToUpperHalfPlane, norm_circleMap_zero]
  have hzEq : (z.re : ℂ) = z := by
    apply Complex.ext
    · exact Complex.ofReal_re _
    · rw [Complex.ofReal_im, hzim]
  have hzP : P z = 0 := by
    rw [← hzEq, show P (z.re : ℂ) = _ from halfLineFourierLaplace_ofReal f a z.re,
      hGap hθgap, Pi.zero_apply, mul_zero]
  have hCircle : Continuous (fun r : ℝ => circleMap (0 : ℂ) r θ) := by
    unfold circleMap
    fun_prop
  have hRadial : Tendsto (fun r : ℝ => Q (circleMap 0 r θ)) (𝓝[<] (1 : ℝ)) (𝓝 z) := by
    have hC : ContinuousAt (fun r : ℝ => circleMap (0 : ℂ) r θ) 1 := hCircle.continuousAt
    have hAt : ContinuousAt Q ((fun r : ℝ => circleMap (0 : ℂ) r θ) 1) :=
      hCayleyCont (circleMap_unit_ne_one hθrange)
    exact (hAt.comp (f := fun r : ℝ => circleMap (0 : ℂ) r θ) hC).continuousWithinAt.tendsto
  have hRadialH := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hRadial (s := H)
    (by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one)]
        with r (hr₁ : r < 1) (hr₀ : 0 < r)
      have hw : circleMap (0 : ℂ) r θ ∈ ball 0 1 := by
        rwa [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hr₀]
      exact (show 0 < (Q (circleMap 0 r θ)).im from hQmaps hw).le)
  have hPLim := (hCont z (le_of_eq hzim.symm)).tendsto.comp hRadialH
  change Tendsto (P ∘ fun r : ℝ => Q (circleMap 0 r θ)) (𝓝[<] (1 : ℝ)) (𝓝 0)
  exact hzP ▸ hPLim

end
end MeyerGeneralProblem
