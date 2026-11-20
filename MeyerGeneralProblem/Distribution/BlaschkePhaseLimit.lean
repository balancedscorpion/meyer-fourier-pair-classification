module

public import MeyerGeneralProblem.Distribution.BlaschkeLogarithmicRepresentation

@[expose] public section

/-!
# The boundary phase of the heated Blaschke factorization

At a nonzero boundary value the compensated Herglotz limit identifies
the phase of the analytic logarithm. Multiplying by the actual
Blaschke boundary value preserves the phase with its monotone term.
-/

namespace MeyerGeneralProblem

noncomputable section

open Filter MeasureTheory Metric Set
open scoped FourierTransform Topology

private theorem cayleyBoundaryPoint_ne_one (x : ℝ) : cayleyBoundaryPoint x ≠ 1 := by
  intro h
  have hDen : (x : ℂ) + Complex.I ≠ 0 := by
    intro e
    have hIm := congrArg Complex.im e
    simp at hIm
  rw [cayleyBoundaryPoint, circleMap_cayleyBoundaryAngle] at h
  have he := (div_eq_iff hDen).mp h
  apply Complex.I_ne_zero
  linear_combination -he / 2

/-- The radial path to a finite Cayley boundary point is eventually
in the disk. -/
theorem eventually_mul_cayleyBoundaryPoint_mem_ball (x : ℝ) :
    ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), (r : ℂ) * cayleyBoundaryPoint x ∈ ball (0 : ℂ) 1 := by
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one), self_mem_nhdsWithin]
    with r (hr : 0 < r) (hr₁ : r < 1)
  rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le,
    norm_cayleyBoundaryPoint, mul_one]
  exact hr₁

/-- The radial path in the Cayley chart tends to its real boundary
point in the upper half-plane coordinates. -/
theorem tendsto_cayleyBoundaryRadial (x : ℝ) :
    Tendsto (fun r : ℝ => cayleyToUpperHalfPlane ((r : ℂ) * cayleyBoundaryPoint x))
      (𝓝[<] (1 : ℝ)) (𝓝 (x : ℂ)) := by
  let ζ := cayleyBoundaryPoint x
  have hScale : Tendsto (fun r : ℝ => (r : ℂ) * ζ) (𝓝[<] (1 : ℝ)) (𝓝 ζ) := by
    simpa only [Complex.ofReal_one, one_mul] using
      ((Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mul_const ζ).mono_left
        nhdsWithin_le_nhds
  have he := (analyticAt_cayleyToUpperHalfPlane (cayleyBoundaryPoint_ne_one x)).continuousAt.tendsto.comp hScale
  have hCζ : cayleyToUpperHalfPlane ζ = (x : ℂ) := cayleyToUpperHalfPlane_circleMap_cayleyBoundaryAngle x
  rwa [hCζ] at he

/-- At a nonzero real value the imaginary part of the actual logarithm
has the compensated Herglotz boundary limit and the affine phase. -/
theorem tendsto_im_blaschkeLog_radial_of_weighted_identity {H L : ℂ → ℂ}
    (hH : Differentiable ℂ H)
    (hu : Integrable (fun y : ℝ => Real.log ‖H (y : ℂ)‖ / (1 + y ^ 2)))
    {c d : ℝ}
    (hW : ∀ w ∈ ball (0 : ℂ) 1, L (cayleyToUpperHalfPlane w) =
      weightedDiskHerglotzIntegral (fun y : ℝ => Real.log ‖H (y : ℂ)‖) w +
        (c : ℂ) * Complex.I * cayleyToUpperHalfPlane w + (d : ℂ) * Complex.I)
    {x : ℝ} (hx : H (x : ℂ) ≠ 0) :
    Tendsto (fun r : ℝ => (L (cayleyToUpperHalfPlane ((r : ℂ) * cayleyBoundaryPoint x))).im)
      (𝓝[<] (1 : ℝ))
      (𝓝 (weightedDiskHerglotzBoundaryConjugate (fun y : ℝ => Real.log ‖H (y : ℂ)‖) x + c * x + d)) := by
  have hHReal : DifferentiableAt ℝ (fun y : ℝ => H (y : ℂ)) x :=
    ((hH (x : ℂ)).restrictScalars ℝ).comp x Complex.ofRealCLM.differentiableAt
  have hUReal : DifferentiableAt ℝ (fun y : ℝ => Real.log ‖H (y : ℂ)‖) x :=
    (hHReal.norm ℂ hx).log (norm_ne_zero_iff.mpr hx)
  have hConj := tendsto_im_weightedDiskHerglotzIntegral_radial_of_differentiableAt hu hUReal
  have hPReal : Tendsto (fun r : ℝ => (cayleyToUpperHalfPlane ((r : ℂ) * cayleyBoundaryPoint x)).re)
      (𝓝[<] (1 : ℝ)) (𝓝 x) :=
    Complex.continuous_re.continuousAt.tendsto.comp (tendsto_cayleyBoundaryRadial x)
  refine ((hConj.add (hPReal.const_mul c)).add_const d).congr' ?_
  filter_upwards [eventually_mul_cayleyBoundaryPoint_mem_ball x] with r hr
  have he := congrArg Complex.im (hW _ hr)
  simpa [Complex.mul_im, Complex.mul_re] using he.symm

/-- At a nonzero real point, the actual boundary value has the phase
given by the Blaschke argument, the compensated Herglotz conjugate
and the affine contribution. -/
theorem eq_norm_mul_exp_blaschke_phase_of_nonzero {ι : Type*} {a : ι → ℂ}
    (ha : ∀ i, 0 < (a i).im) (hFin : ∀ R : ℝ, {i | ‖a i‖ ≤ R}.Finite)
    (hSum : Summable (fun i => upperHalfPlaneBlaschkeWeight (a i)))
    {H L : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hFactor : EqOn H (fun z => upperHalfPlaneBlaschkeProduct a z * Complex.exp (L z))
      {z : ℂ | 0 < z.im})
    (hu : Integrable (fun y : ℝ => Real.log ‖H (y : ℂ)‖ / (1 + y ^ 2)))
    {c d : ℝ}
    (hW : ∀ w ∈ ball (0 : ℂ) 1, L (cayleyToUpperHalfPlane w) =
      weightedDiskHerglotzIntegral (fun y : ℝ => Real.log ‖H (y : ℂ)‖) w +
        (c : ℂ) * Complex.I * cayleyToUpperHalfPlane w + (d : ℂ) * Complex.I)
    {x : ℝ} (hx : H (x : ℂ) ≠ 0) :
    let v := weightedDiskHerglotzBoundaryConjugate (fun y : ℝ => Real.log ‖H (y : ℂ)‖) x
    let phase := upperHalfPlaneBlaschkePhaseSum a x + v + c * x + d
    H (x : ℂ) = (‖H (x : ℂ)‖ : ℂ) * Complex.exp ((phase : ℂ) * Complex.I) := by
  let ζ := cayleyBoundaryPoint x
  let C := cayleyToUpperHalfPlane
  let p (r : ℝ) := C ((r : ℂ) * ζ)
  let B := upperHalfPlaneBlaschkeProduct a
  let u (y : ℝ) := Real.log ‖H (y : ℂ)‖
  let v := weightedDiskHerglotzBoundaryConjugate u x
  let s := v + c * x + d
  have hCζ : cayleyToUpperHalfPlane ζ = (x : ℂ) := cayleyToUpperHalfPlane_circleMap_cayleyBoundaryAngle x
  have hζ : ζ ≠ 1 := cayleyBoundaryPoint_ne_one x
  have hNormζ : ‖ζ‖ = 1 := norm_cayleyBoundaryPoint x
  have hBall := eventually_mul_cayleyBoundaryPoint_mem_ball x
  have hP : Tendsto p (𝓝[<] (1 : ℝ)) (𝓝 (x : ℂ)) := tendsto_cayleyBoundaryRadial x
  have hU : ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 < (p r).im :=
    hBall.mono fun _ hr => im_cayleyToUpperHalfPlane_pos (mem_ball_zero_iff.mp hr)
  have hRe : Tendsto (fun r : ℝ => (L (p r)).re) (𝓝[<] (1 : ℝ)) (𝓝 (u x)) := by
    have he := tendsto_re_blaschkeBoundaryLog_radial_of_nonzero ha hFin hSum hH.continuous
      hFactor hNormζ hζ (by rwa [hCζ])
    rwa [hCζ] at he
  have hIm : Tendsto (fun r : ℝ => (L (p r)).im) (𝓝[<] (1 : ℝ)) (𝓝 s) :=
    tendsto_im_blaschkeLog_radial_of_weighted_identity hH hu hW hx
  have hL : Tendsto (fun r : ℝ => L (p r)) (𝓝[<] (1 : ℝ))
      (𝓝 ((u x : ℂ) + (s : ℂ) * Complex.I)) := by
    have hReC := Complex.continuous_ofReal.continuousAt.tendsto.comp hRe
    have hImC := Complex.continuous_ofReal.continuousAt.tendsto.comp hIm
    simpa only [Function.comp_apply, Complex.re_add_im] using hReC.add (hImC.mul_const Complex.I)
  have hClosed : Tendsto p (𝓝[<] (1 : ℝ)) (𝓝[{z : ℂ | 0 ≤ z.im}] (x : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within p hP (hU.mono fun _ hr => hr.le)
  have hBP := (continuousOn_upperHalfPlaneBlaschkeProduct ha hFin hSum (x : ℂ) (by simp)).tendsto.comp hClosed
  have hExp := Complex.continuous_exp.continuousAt.tendsto.comp hL
  have hBoth : Tendsto (fun r : ℝ => H (p r)) (𝓝[<] (1 : ℝ))
      (𝓝 (B (x : ℂ) * Complex.exp ((u x : ℂ) + (s : ℂ) * Complex.I))) :=
    (hBP.mul hExp).congr' (hU.mono fun _ hr => (hFactor hr).symm)
  have he := tendsto_nhds_unique (hH.continuous.continuousAt.tendsto.comp hP) hBoth
  calc
    H (x : ℂ) = B (x : ℂ) * Complex.exp ((u x : ℂ) + (s : ℂ) * Complex.I) := he
    _ = _ := by
      rw [show B (x : ℂ) = _ from upperHalfPlaneBlaschkeProduct_real ha hFin hSum x,
        Complex.exp_add, ← Complex.ofReal_exp]
      have hn : Real.exp (u x) = ‖H (x : ℂ)‖ := Real.exp_log (norm_pos_iff.mpr hx)
      rw [hn, mul_left_comm, ← Complex.exp_add]
      congr 2
      dsimp only [s]
      push_cast
      ring

/-- The actual heated positive-frequency part has the boundary phase
with slope at least the Fourier-gap edge. The same logarithm gives
the interior factorization and weighted representation. -/
theorem exists_eventually_heatFourierLaplace_boundary_phase_of_gap
    {f : ℝ → ℝ} (hf : Integrable f) (hfCont : Continuous f) (hf₀ : f ≠ 0)
    {s : ℝ} (hs : 0 ≤ s)
    (hGap : EqOn (𝓕 (fun x : ℝ => (f x : ℂ))) 0 (Ioo (-s) s)) :
    ∃ b : ℝ, s ≤ b ∧ ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      let H := edgeNormalizedHeatFourierLaplace t f b
      let B := upperHalfPlaneBlaschkeProduct (upperHalfPlaneZeroAtIndex H)
      let U : Set ℂ := {z : ℂ | 0 < z.im}
      let u (x : ℝ) := Real.log ‖heatFourierLaplace t f 0 (x : ℂ)‖
      Summable (fun i : UpperHalfPlaneZeroIndex H =>
        upperHalfPlaneBlaschkeWeight (upperHalfPlaneZeroAtIndex H i)) ∧
      (∀ R : ℝ, {i : UpperHalfPlaneZeroIndex H | ‖upperHalfPlaneZeroAtIndex H i‖ ≤ R}.Finite) ∧
      Integrable (fun x : ℝ => u x / (1 + x ^ 2)) ∧
      (∃ z, H z ≠ 0) ∧
      (∀ x : ℝ, ‖H (x : ℂ)‖ = ‖heatFourierLaplace t f 0 (x : ℂ)‖) ∧
      ∃ (L : ℂ → ℂ) (c d : ℝ), AnalyticOnNhd ℂ L U ∧ EqOn H (fun z => B z * Complex.exp (L z)) U ∧
        0 ≤ c ∧
        (∀ w ∈ ball (0 : ℂ) 1, L (cayleyToUpperHalfPlane w) = weightedDiskHerglotzIntegral u w +
          (c : ℂ) * Complex.I * cayleyToUpperHalfPlane w + (d : ℂ) * Complex.I) ∧
        (∀ z ∈ U, L z = weightedDiskHerglotzIntegral u (scaledUpperHalfPlaneToDisk 1 z) +
          (c : ℂ) * Complex.I * z + (d : ℂ) * Complex.I) ∧
        ∀ x : ℝ,
          let phase := (2 * Real.pi * b) * x + upperHalfPlaneBlaschkePhaseSum (upperHalfPlaneZeroAtIndex H) x +
            weightedDiskHerglotzBoundaryConjugate u x + c * x + d
          heatFourierLaplace t f 0 (x : ℂ) =
            (‖heatFourierLaplace t f 0 (x : ℂ)‖ : ℂ) * Complex.exp ((phase : ℂ) * Complex.I) := by
  obtain ⟨b, hb, hZero, hEdge, _⟩ := exists_common_positiveFourier_lower_edge hf hfCont hf₀ hs hGap
  refine ⟨b, hb, ?_⟩
  have hTime : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨y, _, hNonzero⟩ := exists_height_eventually_summable_edgeNormalizedHeat_weightedZeroOrder hf (hs.trans hb) hEdge
  filter_upwards [hTime, hNonzero,
    eventually_edgeNormalizedHeat_blaschke_hasWeightedLogarithm hf (hs.trans hb) hEdge]
    with t ht hN hF
  obtain ⟨hSum, hFin, hUInt, L, hL, hEq, c, d, hc, hW, hPhys⟩ := hF
  let H := edgeNormalizedHeatFourierLaplace t f b
  let u (x : ℝ) := Real.log ‖heatFourierLaplace t f 0 (x : ℂ)‖
  have hCut := heatFourierLaplace_eq_of_zero_Ioo hf ht (hs.trans hb) hZero
  have hNorm (x : ℝ) : ‖H (x : ℂ)‖ = ‖heatFourierLaplace t f 0 (x : ℂ)‖ :=
    (norm_edgeNormalizedHeatFourierLaplace_real t f b x).trans (congrArg norm (congrFun hCut x).symm)
  have hu : (fun x : ℝ => Real.log ‖H (x : ℂ)‖) = u := by
    funext x
    exact congrArg Real.log (hNorm x)
  refine ⟨hSum, hFin, ?_, ⟨(y : ℂ) * Complex.I, hN.1⟩, hNorm, L, c, d, hL, hEq, hc,
    ?_, ?_, fun x => ?_⟩
  · change Integrable (fun x : ℝ => u x / (1 + x ^ 2))
    rwa [← hu]
  · intro w hw
    change L (cayleyToUpperHalfPlane w) = weightedDiskHerglotzIntegral u w +
      (c : ℂ) * Complex.I * cayleyToUpperHalfPlane w + (d : ℂ) * Complex.I
    rw [← hu]
    exact hW w hw
  · intro z hz
    change L z = weightedDiskHerglotzIntegral u (scaledUpperHalfPlaneToDisk 1 z) +
      (c : ℂ) * Complex.I * z + (d : ℂ) * Complex.I
    rw [← hu]
    exact hPhys z hz
  · by_cases hx : H (x : ℂ) = 0
    · have h0 : ‖heatFourierLaplace t f 0 (x : ℂ)‖ = 0 := (hNorm x).symm.trans (by rw [hx, norm_zero])
      simp [norm_eq_zero.mp h0]
    · have hPhase := eq_norm_mul_exp_blaschke_phase_of_nonzero (fun i => i.1.2) hFin hSum
        (differentiable_edgeNormalizedHeatFourierLaplace hf ht b) hEq hUInt hW hx
      change H (x : ℂ) = (‖H (x : ℂ)‖ : ℂ) * Complex.exp
        ((↑(upperHalfPlaneBlaschkePhaseSum (upperHalfPlaneZeroAtIndex H) x +
          weightedDiskHerglotzBoundaryConjugate (fun y : ℝ => Real.log ‖H (y : ℂ)‖) x +
            c * x + d) : ℂ) * Complex.I) at hPhase
      let k : ℂ := ((2 * Real.pi * b : ℝ) : ℂ) * Complex.I
      have hUndo : Complex.exp (k * (x : ℂ)) * H (x : ℂ) = heatFourierLaplace t f 0 (x : ℂ) := by
        change Complex.exp (k * (x : ℂ)) *
          (Complex.exp (-k * (x : ℂ)) * heatFourierLaplace t f b (x : ℂ)) = _
        rw [← mul_assoc, ← Complex.exp_add, show k * (x : ℂ) + -k * (x : ℂ) = 0 by ring,
          Complex.exp_zero, one_mul, ← hCut]
      calc
        heatFourierLaplace t f 0 (x : ℂ) = Complex.exp (k * (x : ℂ)) * H (x : ℂ) := hUndo.symm
        _ = _ := by
          rw [hPhase, hNorm, hu, mul_left_comm, ← Complex.exp_add]
          congr 2
          dsimp only [k]
          push_cast
          ring

end
end MeyerGeneralProblem
