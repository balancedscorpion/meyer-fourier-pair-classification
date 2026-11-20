module

public import MeyerGeneralProblem.Distribution.BoundedBlaschkeQuotient

@[expose] public section

/-!
# Local boundary form of the Blaschke logarithm

At a finite Cayley boundary point, the quotient extends holomorphically.
Its logarithmic modulus is a finite-order logarithmic singularity plus
a continuous term.
-/

namespace MeyerGeneralProblem

noncomputable section

open ComplexConjugate Filter Metric Set
open scoped Topology

private theorem norm_blaschkeProduct_of_im_eq_zero {ι : Type*} {a : ι → ℂ}
    (ha : ∀ i, 0 < (a i).im) (hFin : ∀ R : ℝ, {i | ‖a i‖ ≤ R}.Finite)
    (hSum : Summable (fun i => upperHalfPlaneBlaschkeWeight (a i))) {z : ℂ} (hz : z.im = 0) :
    ‖upperHalfPlaneBlaschkeProduct a z‖ = 1 := by
  have hReal : (z.re : ℂ) = z := by
    apply Complex.ext <;> simp [hz]
  rw [← hReal, upperHalfPlaneBlaschkeProduct_real ha hFin hSum, Complex.norm_exp]
  simp

private theorem im_cayleyToUpperHalfPlane_eq_zero_of_norm_eq_one {w : ℂ}
    (hw : ‖w‖ = 1) : (cayleyToUpperHalfPlane w).im = 0 := by
  simp [im_cayleyToUpperHalfPlane, hw]

private theorem analyticAt_blaschkeProduct_of_im_eq_zero {ι : Type*} {a : ι → ℂ}
    (ha : ∀ i, 0 < (a i).im) (hFin : ∀ R : ℝ, {i | ‖a i‖ ≤ R}.Finite)
    (hSum : Summable (fun i => upperHalfPlaneBlaschkeWeight (a i))) {z : ℂ} (hz : z.im = 0) :
    AnalyticAt ℂ (upperHalfPlaneBlaschkeProduct a) z := by
  apply analyticAt_upperHalfPlaneBlaschkeProduct_of_avoids_poles ha hFin hSum
  intro i he
  have him := congrArg Complex.im he
  rw [hz, Complex.conj_im] at him
  linarith only [ha i, him]

/-- Near each finite boundary point, the interior logarithm and the
boundary logarithmic modulus share the same finite-order singularity
and the same continuous remainder. -/
theorem exists_local_blaschkeBoundaryLog_model {ι : Type*} {a : ι → ℂ}
    (ha : ∀ i, 0 < (a i).im) (hFin : ∀ R : ℝ, {i | ‖a i‖ ≤ R}.Finite)
    (hSum : Summable (fun i => upperHalfPlaneBlaschkeWeight (a i)))
    {H L : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hFactor : EqOn H (fun z => upperHalfPlaneBlaschkeProduct a z * Complex.exp (L z))
      {z : ℂ | 0 < z.im})
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hζ₁ : ζ ≠ 1) :
    ∃ (n : ℕ) (R : ℂ → ℝ), ContinuousAt R ζ ∧
      (∀ᶠ w in 𝓝[ball (0 : ℂ) 1] ζ,
        (L (cayleyToUpperHalfPlane w)).re = (n : ℝ) * Real.log ‖w - ζ‖ + R w) ∧
      (∀ᶠ w in 𝓝 ζ, ‖w‖ = 1 → w ≠ ζ →
        Real.log ‖H (cayleyToUpperHalfPlane w)‖ = (n : ℝ) * Real.log ‖w - ζ‖ + R w) := by
  let B := upperHalfPlaneBlaschkeProduct a
  let C := cayleyToUpperHalfPlane
  let Q (w : ℂ) := H (C w) / B (C w)
  have hReal : (C ζ).im = 0 := im_cayleyToUpperHalfPlane_eq_zero_of_norm_eq_one hζ
  have hC : AnalyticAt ℂ C ζ := analyticAt_cayleyToUpperHalfPlane hζ₁
  have hB : AnalyticAt ℂ B (C ζ) := analyticAt_blaschkeProduct_of_im_eq_zero ha hFin hSum hReal
  have hB₀ : B (C ζ) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_blaschkeProduct_of_im_eq_zero ha hFin hSum hReal]
    exact one_ne_zero
  have hQ : AnalyticAt ℂ Q ζ := ((hH.analyticAt (C ζ)).comp hC).div (hB.comp hC) hB₀
  have hBnear : ∀ᶠ w in 𝓝 ζ, B (C w) ≠ 0 :=
    (hB.continuousAt.comp hC.continuousAt).eventually_ne hB₀
  have hQeq {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) (hBw : B (C w) ≠ 0) :
      Q w = Complex.exp (L (C w)) := by
    apply (div_eq_iff hBw).mpr
    rw [mul_comm]
    exact hFactor (im_cayleyToUpperHalfPlane_pos (mem_ball_zero_iff.mp hw))
  have hζCl : ζ ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball _ one_ne_zero, mem_closedBall, dist_zero_right, hζ]
  have hQnear : ¬ ∀ᶠ w in 𝓝 ζ, Q w = 0 := by
    intro hZero
    obtain ⟨w, hw, hBw, hQw⟩ :=
      ((mem_closure_iff_frequently.mp hζCl).and_eventually (hBnear.and hZero)).exists
    exact Complex.exp_ne_zero _ ((hQeq hw hBw).symm.trans hQw)
  obtain ⟨n, g, hg, hg₀, hEq⟩ := hQ.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hQnear
  have hgNear : ∀ᶠ w in 𝓝 ζ, g w ≠ 0 := hg.continuousAt.eventually_ne hg₀
  have hLog {w : ℂ} (hw : w ≠ ζ) (hgw : g w ≠ 0)
      (he : Q w = (w - ζ) ^ n • g w) :
      Real.log ‖Q w‖ = (n : ℝ) * Real.log ‖w - ζ‖ + Real.log ‖g w‖ := by
    rw [he, smul_eq_mul, norm_mul, Real.log_mul, norm_pow, Real.log_pow]
    · exact norm_ne_zero_iff.mpr (pow_ne_zero _ (sub_ne_zero.mpr hw))
    · exact norm_ne_zero_iff.mpr hgw
  have hglog : ContinuousAt (fun w => Real.log ‖g w‖) ζ :=
    hg.continuousAt.norm.log (norm_ne_zero_iff.mpr hg₀)
  refine ⟨n, fun w => Real.log ‖g w‖, hglog, ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin, hBnear.filter_mono nhdsWithin_le_nhds,
      hgNear.filter_mono nhdsWithin_le_nhds, hEq.filter_mono nhdsWithin_le_nhds] with w hw hBw hgw he
    have hwζ : w ≠ ζ := by
      intro e
      have hn := mem_ball_zero_iff.mp hw
      rw [e, hζ] at hn
      exact (lt_irrefl _) hn
    have hl := hLog hwζ hgw he
    rwa [hQeq hw hBw, Complex.norm_exp, Real.log_exp] at hl
  · filter_upwards [hgNear, hEq] with w hgw he hw hwζ
    have hl := hLog hwζ hgw he
    have hNorm : ‖Q w‖ = ‖H (C w)‖ := by
      dsimp only [Q]
      rw [norm_div, norm_blaschkeProduct_of_im_eq_zero ha hFin hSum
        (im_cayleyToUpperHalfPlane_eq_zero_of_norm_eq_one hw), div_one]
    rwa [hNorm] at hl

/-- At a nonzero finite boundary value, the radial real part tends to
the logarithmic modulus of the original entire function. -/
theorem tendsto_re_blaschkeBoundaryLog_radial_of_nonzero {ι : Type*} {a : ι → ℂ}
    (ha : ∀ i, 0 < (a i).im) (hFin : ∀ R : ℝ, {i | ‖a i‖ ≤ R}.Finite)
    (hSum : Summable (fun i => upperHalfPlaneBlaschkeWeight (a i)))
    {H L : ℂ → ℂ} (hH : Continuous H)
    (hFactor : EqOn H (fun z => upperHalfPlaneBlaschkeProduct a z * Complex.exp (L z))
      {z : ℂ | 0 < z.im})
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hζ₁ : ζ ≠ 1) (hH₀ : H (cayleyToUpperHalfPlane ζ) ≠ 0) :
    Tendsto (fun r : ℝ => (L (cayleyToUpperHalfPlane ((r : ℂ) * ζ))).re)
      (𝓝[<] (1 : ℝ)) (𝓝 (Real.log ‖H (cayleyToUpperHalfPlane ζ)‖)) := by
  let B := upperHalfPlaneBlaschkeProduct a
  let C := cayleyToUpperHalfPlane
  let Q (w : ℂ) := H (C w) / B (C w)
  let S (r : ℝ) := (r : ℂ) * ζ
  have hReal : (C ζ).im = 0 := im_cayleyToUpperHalfPlane_eq_zero_of_norm_eq_one hζ
  have hC : ContinuousAt C ζ := (analyticAt_cayleyToUpperHalfPlane hζ₁).continuousAt
  have hB : ContinuousAt (fun w => B (C w)) ζ :=
    (analyticAt_blaschkeProduct_of_im_eq_zero ha hFin hSum hReal).continuousAt.comp hC
  have hBnorm : ‖B (C ζ)‖ = 1 := norm_blaschkeProduct_of_im_eq_zero ha hFin hSum hReal
  have hB₀ : B (C ζ) ≠ 0 := norm_ne_zero_iff.mp (hBnorm.trans_ne one_ne_zero)
  have hQcont : ContinuousAt Q ζ := (hH.continuousAt.comp hC).div hB hB₀
  have hQlog : ContinuousAt (fun w => Real.log ‖Q w‖) ζ :=
    hQcont.norm.log (norm_ne_zero_iff.mpr (div_ne_zero hH₀ hB₀))
  have hScale : Tendsto S (𝓝[<] (1 : ℝ)) (𝓝 ζ) := by
    simpa only [S, Complex.ofReal_one, one_mul] using
      ((Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mul_const ζ).mono_left
        nhdsWithin_le_nhds
  have hLimit := hQlog.tendsto.comp hScale
  have he : Real.log ‖Q ζ‖ = Real.log ‖H (C ζ)‖ := by
    rw [show ‖Q ζ‖ = ‖H (C ζ)‖ / ‖B (C ζ)‖ from norm_div _ _, hBnorm, div_one]
  rw [he] at hLimit
  refine hLimit.congr' ?_
  filter_upwards [hScale.eventually (hB.eventually_ne hB₀), self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one)] with r hBr (hr₁ : r < 1) (hr : 0 < r)
  have hNorm : ‖S r‖ < 1 := by
    rw [show ‖S r‖ = ‖(r : ℂ)‖ * ‖ζ‖ from norm_mul _ _, Complex.norm_real,
      Real.norm_of_nonneg hr.le, hζ, mul_one]
    exact hr₁
  have hQeq : Q (S r) = Complex.exp (L (C (S r))) := by
    apply (div_eq_iff hBr).mpr
    rw [mul_comm]
    exact hFactor (im_cayleyToUpperHalfPlane_pos hNorm)
  change Real.log ‖Q (S r)‖ = (L (C (S r))).re
  rw [hQeq, Complex.norm_exp, Real.log_exp]

end
end MeyerGeneralProblem
